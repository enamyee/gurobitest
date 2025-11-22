#define _CRT_SECURE_NO_WARNINGS
#include <iostream>
#include <vector>
#include <array>
#include <utility>
#include <string>
#include <cmath>
#include <set>
#include <algorithm>
#include <queue>          
#include "gurobi_c++.h"
#include <fstream>
#include <chrono>

using namespace std;

// ===== DSU =====
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

bool checkFeasibility(int V, const vector<array<int, 4>>& edges,
    const vector<int>& selected,
    const vector<pair<int, int>>& terminals) {
    DSU dsu(V);
    for (int idx : selected) {
        int u = edges[idx][0], v = edges[idx][1];
        dsu.unite(u, v);
    }
    return allConnected(dsu, terminals);
}

// ===== 실제 최악 단말-단말 경로 길이 계산 함수 =====
double computeWorstTerminalPath(int V,
    const vector<array<int, 4>>& edges,
    const vector<int>& fixed_edges,
    const vector<pair<int, int>>& terminals)
{
    const double INF = 1e18;

    // 인접 리스트 (고정된 엣지만 사용)
    vector<vector<pair<int, double>>> adj(V + 1);
    for (int e : fixed_edges) {
        int u = edges[e][0];
        int v = edges[e][1];
        double w = edges[e][3];   // 거리 정보 사용
        adj[u].push_back({ v, w });
        adj[v].push_back({ u, w });
    }

    // 다익스트라 (s -> t)
    auto dijkstra = [&](int s, int t) {
        vector<double> dist(V + 1, INF);
        priority_queue<pair<double, int>,
            vector<pair<double, int>>,
            greater<pair<double, int>>> pq;

        dist[s] = 0.0;
        pq.push({ 0.0, s });

        while (!pq.empty()) {
            auto top = pq.top();
            double d = top.first;
            int u = top.second;
            pq.pop();
            if (d > dist[u]) continue;
            if (u == t) break;

            for (auto& pr : adj[u]) {
                int v = pr.first;
                double w = pr.second;
                if (dist[v] > d + w) {
                    dist[v] = d + w;
                    pq.push({ dist[v], v });
                }
            }
        }
        return dist[t]; // 만약 연결 안되어 있으면 INF
        };

    double worst = 0.0;
    for (auto& term : terminals) {
        int s = term.first;
        int t = term.second;
        double d = dijkstra(s, t);
        worst = max(worst, d);
    }
    return worst;
}

// ================= Main Solver ==================
void solveIterativeFixing(int V, const vector<array<int, 4>>& edges,
    const vector<pair<int, int>>& terminals, int B) {
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
            arc_u[2 * e] = u;
            arc_v[2 * e] = v;
            arc_edge[2 * e] = e;
            arc_u[2 * e + 1] = v;
            arc_v[2 * e + 1] = u;
            arc_edge[2 * e + 1] = e;
        }

        int K = static_cast<int>(terminals.size());
        vector<vector<GRBVar>> f(K, vector<GRBVar>(A));
        for (int k = 0; k < K; k++) {
            for (int a = 0; a < A; a++)
                f[k][a] = model.addVar(0.0, 1.0, 0.0,
                    GRB_CONTINUOUS, "f_" + to_string(k) + "_" + to_string(a));
        }

        GRBVar L = model.addVar(0.0, GRB_INFINITY, 0.0, GRB_CONTINUOUS, "L");
        model.update();

        // flow 보존 제약
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
                else             model.addConstr(net == 0);
            }
        }

        // f <= x
        for (int k = 0; k < K; k++) {
            for (int a = 0; a < A; a++) {
                model.addConstr(f[k][a] <= x[arc_edge[a]]);
            }
        }

        // 예산 제약 (비용)
        GRBLinExpr budget = 0;
        for (int e = 0; e < E; e++) budget += edges[e][2] * x[e];
        model.addConstr(budget <= B);

        // 각 터미널 pair의 경로 길이 <= L
        for (int k = 0; k < K; k++) {
            GRBLinExpr path_length = 0;
            for (int a = 0; a < A; a++) {
                path_length += f[k][a] * edges[arc_edge[a]][3];
            }
            model.addConstr(path_length <= L);
        }

        // 목적: L 최소화
        model.setObjective(GRBLinExpr(L), GRB_MINIMIZE);

        // ===== Iterative Fixing =====
        while (true) {
            model.optimize();
            if (model.get(GRB_IntAttr_Status) != GRB_OPTIMAL) {
                cout << "LP infeasible\n";
                return;
            }

            // 아직 고정 안 된 것 중 최대 x 값 찾기
            double max_val = -1.0;
            for (int e = 0; e < E; e++) {
                if (find(fixed_edges.begin(), fixed_edges.end(), e) == fixed_edges.end()) {
                    max_val = max(max_val, x[e].get(GRB_DoubleAttr_X));
                }
            }
            if (max_val < 0) break;

            // 그 값을 가진 엣지들 모으기
            vector<int> newly_fix;
            for (int e = 0; e < E; e++) {
                if (find(fixed_edges.begin(), fixed_edges.end(), e) == fixed_edges.end()) {
                    if (fabs(x[e].get(GRB_DoubleAttr_X) - max_val) < 1e-9) {
                        newly_fix.push_back(e);
                    }
                }
            }
            if (newly_fix.empty()) break;

            // 해당 엣지들을 1로 고정
            for (int e : newly_fix) {
                x[e].set(GRB_DoubleAttr_LB, 1.0);
                fixed_edges.push_back(e);
            }

            // 터미널 쌍이 모두 연결되면 종료
            if (checkFeasibility(V, edges, fixed_edges, terminals)) break;
        }

        cout << "\n=== Iterative Fixing Result ===\n";
        int total_cost = 0;
        set<int> selected_nodes;

        for (int e : fixed_edges) {
            cout << edges[e][0] << " - " << edges[e][1]
                << "  cost=" << edges[e][2]
                << "  dist=" << edges[e][3] << "\n";
            total_cost += edges[e][2];
            selected_nodes.insert(edges[e][0]);
            selected_nodes.insert(edges[e][1]);
        }

        // 실제 최악 단말-단말 경로 길이 계산
        double worst_actual = computeWorstTerminalPath(V, edges, fixed_edges, terminals);

        cout << "\n=== Selected Graph Information ===\n";
        cout << "Selected Node Count           : " << selected_nodes.size() << "\n";
        cout << "Selected Edge Count           : " << fixed_edges.size() << "\n";
        cout << "Total Construction Cost       : " << total_cost << "\n";
        cout << "Actual worst terminal path    : " << worst_actual << "\n";
        cout << "LP upper bound L* (model var) : " << L.get(GRB_DoubleAttr_X) << "\n";

        ofstream fout("result.dot");
        fout << "graph G {\n";
        for (int e : fixed_edges) {
            fout << "  " << edges[e][0] << " -- " << edges[e][1]
                << " [label=\"" << edges[e][3] << "\", color=blue];\n";
        }
        fout << "}\n";
        fout.close();
    }
    catch (GRBException& e) {
        cerr << "Gurobi Error: " << e.getMessage() << endl;
    }
    catch (...) {
        cerr << "Unknown Error\n";
    }
}

// ================= MAIN ===================
int main() {

    if (!freopen("test.txt", "r", stdin)) {
        cerr << "입력 파일을 열 수 없습니다." << endl;
        return 1;
    }
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int B, V, E, T;
    cin >> V >> E;
    vector<array<int, 4>> edges(E);
    for (int i = 0; i < E; i++)
        cin >> edges[i][0] >> edges[i][1] >> edges[i][2] >> edges[i][3];

    cin >> T;
    vector<pair<int, int>> terminals(T);
    for (int i = 0; i < T; i++)
        cin >> terminals[i].first >> terminals[i].second;

    cin >> B;

    auto start = std::chrono::high_resolution_clock::now();
    solveIterativeFixing(V, edges, terminals, B);
    auto end = std::chrono::high_resolution_clock::now();

    double elapsed = std::chrono::duration<double>(end - start).count();
    cout << "\n=== Extra Information ===\n";
    cout << "Execution time (sec) : " << elapsed << "\n";

    return 0;
}
