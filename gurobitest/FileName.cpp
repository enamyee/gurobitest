#define _CRT_SECURE_NO_WARNINGS
#include <iostream>
#include <vector>
#include <array>
#include <utility>
#include <string>
#include <cmath>
#include <set>
#include <algorithm>
#include "gurobi_c++.h"

using namespace std;

struct DSU {
    vector<int> p, r;
    DSU(int n) : p(n + 1), r(n + 1, 0) {
        for (int i = 1; i <= n; i++) p[i] = i;
    }
    int find(int x) { return p[x] == x ? x : p[x] = find(p[x]); }
    bool unite(int a, int b) {
        a = find(a); b = find(b);
        if (a == b) return false;
        if (r[a] < r[b]) swap(a, b);
        p[b] = a;
        if (r[a] == r[b]) r[a]++;
        return true;
    }
};

bool allConnected(DSU& dsu, const vector<pair<int, int>>& terminals) {
    for (const auto& term : terminals) {
        if (dsu.find(term.first) != dsu.find(term.second)) return false;
    }
    return true;
}

bool checkFeasibility(int V, const vector<array<int, 4>>& edges, const vector<int>& selected, const vector<pair<int, int>>& terminals) {
    DSU dsu(V);
    for (int idx : selected) {
        int u = edges[idx][0], v = edges[idx][1];
        dsu.unite(u, v);
    }
    return allConnected(dsu, terminals);
}

void solveIterativeFixing(int V, const vector<array<int, 4>>& edges, const vector<pair<int, int>>& terminals, int B) {
    int E = static_cast<int>(edges.size());
    vector<int> fixed_edges;

    try {
        GRBEnv env = GRBEnv(true);
        env.set("LogFile", "steiner_fixing.log");
        env.start();
        GRBModel model = GRBModel(env);

        vector<GRBVar> x(E);
        for (int e = 0; e < E; e++) {
                x[e] = model.addVar(0.0, 1.0, 0.0, GRB_CONTINUOUS, "x_" + to_string(e));
        }

        int A = 2 * E;
        vector<int> arc_u(A), arc_v(A), arc_edge(A);
        for (int e = 0; e < E; e++) {
            int u = edges[e][0], v = edges[e][1];
            arc_u[2 * e] = u; arc_v[2 * e] = v; arc_edge[2 * e] = e;
            arc_u[2 * e + 1] = v; arc_v[2 * e + 1] = u; arc_edge[2 * e + 1] = e;
        }

        int K = static_cast<int>(terminals.size());
        vector<vector<GRBVar>> f(K, vector<GRBVar>(A));
        for (int k = 0; k < K; k++) {
            for (int a = 0; a < A; a++) {
                f[k][a] = model.addVar(0.0, 1.0, 0.0, GRB_CONTINUOUS, "f_" + to_string(k) + "_" + to_string(a));
            }
        }

        GRBVar L = model.addVar(0.0, GRB_INFINITY, 0.0, GRB_CONTINUOUS, "L");

        model.update();

        for (int k = 0; k < K; k++) {
            int s = terminals[k].first;
            int t = terminals[k].second;

            for (int v = 1; v <= V; v++) {
                GRBLinExpr net = 0;
                for (int a = 0; a < A; a++) {
                    if (arc_u[a] == v) net += f[k][a];
                    if (arc_v[a] == v) net -= f[k][a];
                }
                if (v == s) model.addConstr(net == 1);
                else if (v == t) model.addConstr(net == -1);
                else model.addConstr(net == 0);
            }
        }

        for (int k = 0; k < K; k++) {
            for (int a = 0; a < A; a++) {
                int e = arc_edge[a];
                model.addConstr(f[k][a] <= x[e]);
            }
        }

        for (int e = 0; e < E; e++) {
            GRBLinExpr total_flow = 0;
            for (int k = 0; k < K; k++) {
                int a1 = 2 * e, a2 = 2 * e + 1;
                total_flow += f[k][a1] + f[k][a2];
            }
            model.addConstr(total_flow <= x[e]);
        }

        GRBLinExpr budget = 0;
        for (int e = 0; e < E; e++) {
            budget += edges[e][2] * x[e];
        }
        model.addConstr(budget <= B);

        for (int k = 0; k < K; ++k) {
            GRBLinExpr path_length = 0;
            for (int a = 0; a < A; ++a) {
                int e = arc_edge[a];
                int len = edges[e][3];
                path_length += f[k][a] * len;
            }
            model.addConstr(path_length <= L);
        }

        model.setObjective(GRBLinExpr(L), GRB_MINIMIZE);

        while (true) {
            model.optimize();

            if (model.get(GRB_IntAttr_Status) != GRB_OPTIMAL) {
                cout << "LP infeasible\n";
                return;
            }

            double max_val = -1;
            int max_e = -1;
            for (int e = 0; e < E; e++) {
                double val = x[e].get(GRB_DoubleAttr_X);
                if (val > max_val && find(fixed_edges.begin(), fixed_edges.end(), e) == fixed_edges.end()) {
                    max_val = val;
                    max_e = e;
                }
            }

            if (max_e == -1) break;

            x[max_e].set(GRB_DoubleAttr_LB, 1.0);
            fixed_edges.push_back(max_e);

            if (checkFeasibility(V, edges, fixed_edges, terminals)) break;
        }

        cout << "\n=== Iterative Fixing Result ===\n";
        int total_cost = 0;
        for (size_t i = 0; i < fixed_edges.size(); ++i) {
            int e = fixed_edges[i];
            cout << edges[e][0] << " - " << edges[e][1] << "  cost=" << edges[e][2] << "\n";
            total_cost += edges[e][2];
        }
        cout << "Total cost = " << total_cost << "\n";
        cout << "최대 단말 간 경로 길이 (L*) = " << L.get(GRB_DoubleAttr_X) << "\n";


    }
    catch (GRBException& e) {
        cerr << "Gurobi Error: " << e.getMessage() << endl;
    }
    catch (...) {
        cerr << "Unknown Error\n";
    }
}

int main() {
    if (!freopen("test.txt", "r", stdin)) {
        cerr << "입력 파일을 열 수 없습니다." << endl;
        return 1;
    }
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int B, V, E, T;
    cin >> B >> V >> E;
    vector<array<int, 4>> edges(E);
    for (int i = 0; i < E; i++) {
        cin >> edges[i][0] >> edges[i][1] >> edges[i][2] >> edges[i][3];
    }
    cin >> T;
    vector<pair<int, int>> terminals(T);
    for (int i = 0; i < T; i++) {
        cin >> terminals[i].first >> terminals[i].second;
    }
    solveIterativeFixing(V, edges, terminals, B);
    return 0;
}
