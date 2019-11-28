#include <iostream>
#include <vector>
#include <algorithm>
#include <functional>
using namespace std;

#define REP(i, n) for (int i = 0; i < (int)(n); ++i)

int main() {
    int X, Y, Z, K;
    while (cin >> X >> Y >> Z >> K) {
        vector<long long> A(X), B(Y), C(Z);
        REP(i, X) cin >> A[i];
        REP(i, Y) cin >> B[i];
        REP(i, Z) cin >> C[i];
        sort(A.begin(), A.end(), greater<long long>());

        vector<long long> BC;
        REP(y, Y) REP(z, Z) BC.push_back(B[y] + C[z]);
        sort(BC.begin(), BC.end(), greater<long long>());

        vector<long long> ABC;
        REP(x, X) REP(k, min(K, (int)BC.size())) {
            ABC.push_back(A[x] + BC[k]);
        }
        sort(ABC.begin(), ABC.end(), greater<long long>());

        REP(k, K) cout << ABC[k] << '\n';
    }
}