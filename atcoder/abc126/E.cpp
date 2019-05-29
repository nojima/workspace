#include <iostream>
#include <vector>
using namespace std;

#define REP(i, n) for (int i = 0; i < (int)(n); ++i)

struct Edge {
    int dst;
};

void dfs(const vector<vector<Edge>>& edges, vector<bool>& visited, int v) {
    for (auto e : edges[v]) {
        if (!visited[e.dst]) {
            visited[e.dst] = true;
            dfs(edges, visited, e.dst);
        }
    }
}

int main() {
    int N, M;
    while (cin >> N >> M) {
        vector<vector<Edge>> edges(N);
        REP(i, M) {
            int X, Y, Z; cin >> X >> Y >> Z; --X; --Y;
            edges[X].push_back({ Y });
            edges[Y].push_back({ X });
        }

        int answer = 0;
        vector<bool> visited(N);
        REP(v, N) {
            if (!visited[v]) {
                visited[v] = true;
                dfs(edges, visited, v);
                ++answer;
            }
        }

        cout << answer << endl;
    }
}