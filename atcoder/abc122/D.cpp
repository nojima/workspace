#include <iostream>
#include <vector>
#include <string>
using namespace std;

const long long MOD = 1'000'000'000 + 9;

long long power(long long m, long long n) {
    long long ret = 1;
    for (int i = 0; i < n; ++i)
        ret = (ret * m) % MOD;
    return ret;
}

int main() {
    int N;
    while (cin >> N) {
        vector<string> forbidden = {"AGC", "ACG", "GAC", "ATGC", "AGGC", "AGTC"};
        long long ans = 0;
        for (int S = 1; S < (1 << forbidden.size()); ++S) {
            int len = 0;
            for (int i = 0; i < (int)forbidden.size(); ++i) {
                if ((S >> i) & 1) {
                    len += forbidden[i].length();
                }
            }
            if (N - len >= 0) {
                long long pattern = power(4, N - len) * (N - len + 1) % MOD;
                if (S == 3) {
                    // GACG
                    pattern = (pattern + MOD - power(4, N - 4)) % MOD;
                }
                cout << "pattern=" << pattern << endl;
                if (__builtin_popcount(S) % 2 == 1) {
                    ans = (ans + pattern) % MOD;
                } else {
                    ans = (ans - pattern + MOD) % MOD;
                }
            }
        }
        long long all = power(4, N);
        cout << (all - ans + MOD) % MOD << endl;
    }
}