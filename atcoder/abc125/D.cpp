#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;

#define REP(i, n) for (int i = 0; i < (int)(n); ++i)

int main() {
    int N;
    while (cin >> N) {
        vector<long long> A(N);
        REP(i, N) {
            cin >> A[i];
        }

        vector<vector<long long>> dp(N, vector<long long>(2));
        dp[0][0] = A[0];
        dp[0][1] = -1e12;
        for (int i = 1; i < N; ++i) {
            // -1 倍しない場合
            dp[i][0] = A[i] + max(dp[i-1][0], dp[i-1][1]);
            // -1 倍する場合
            dp[i][1] = -A[i] + max(dp[i-1][0] - 2*A[i-1], dp[i-1][1] + 2*A[i-1]);
        }

        cout << max(dp[N-1][0], dp[N-1][1]) << endl;
    }
}