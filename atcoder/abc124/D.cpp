#include <iostream>
#include <algorithm>
#include <vector>
#include <string>
using namespace std;

int main() {
    int N, K;
    while (cin >> N >> K) {
        string S; cin >> S;
        vector<int> n_segment(N);
        bool in_segment = (S[0] == '0');
        n_segment[0] = (S[0] == '0');
        for (int i = 1; i < N; ++i) {
            if (S[i] == '0') {
                n_segment[i] = n_segment[i-1] + (in_segment ? 0 : 1);
                in_segment = true;
            } else {
                n_segment[i] = n_segment[i-1];
                in_segment = false;
            }
        }
        int answer = 0;
        for (int i = 0; i < N; ++i) {
            int limit = K + n_segment[i] + (S[i] == '0' ? -1 : 0);
            auto it = upper_bound(n_segment.begin() + i, n_segment.end(), limit);
            int len = it - (n_segment.begin() + i);
            answer = max(answer, len);
        }
        cout << answer << endl;
    }
}