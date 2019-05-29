#include <iostream>
#include <vector>
using namespace std;

int main() {
    int N, M;
    while (cin >> N >> M) {
        vector<vector<int>> links;
        for (int m = 0; m < M; ++m) {
            int k; cin >> k;
            vector<int> switches;
            for (int n = 0; n < k; ++n) {
                int s; cin >> s;
                switches.push_back(s-1);
            }
            links.push_back(switches);
        }
        vector<int> parities;
        for (int m = 0; m < M; ++m) {
            int p; cin >> p;
            parities.push_back(p);
        }

        int count = 0;
        for (int state = 0; state < (1 << N); ++state) {
            bool ok = true;
            for (int m = 0; m < M; ++m) {
                int p = 0;
                for (auto s : links[m]) {
                    p += (state >> s) % 2;
                }
                if (p % 2 != parities[m]) {
                    ok = false;
                    break;
                }
            }
            if (ok) {
                ++count;
            }
        }
        cout << count << endl;
    }
}