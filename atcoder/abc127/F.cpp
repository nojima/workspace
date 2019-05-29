#include <iostream>
#include <vector>
#include <set>
using namespace std;
 
#define REP(i, n) for (int i = 0; i < (int)(n); ++i)
 
int main() {
    int Q;
    while (cin >> Q) {
        multiset<long long> S;
        multiset<long long>::iterator median;
        size_t median_index;
        long long b_sum = 0, a_diff = 0;
 
        {
            int qt; cin >> qt; // ignore
            long long a, b; cin >> a >> b;
            a_diff = 0;
            b_sum = b;
            S.insert(a);
            median = S.begin();
            median_index = 0;
        }
 
        REP(q, Q-1) {
            int qt; cin >> qt;
            if (qt == 1) {
                long long a, b; cin >> a >> b;
                a_diff += abs(*median - a);
                b_sum += b;
                S.insert(a);
                if (S.size() % 2 == 0) {
                    if (a < *median) {
                        long long m_old = *median;
                        --median;
                        long long d = abs(*median - m_old);
                        size_t n_left = median_index + 1;
                        size_t n_right = S.size() - median_index - 1;
                        a_diff += d * (n_right - n_left);
                    } else {
                        // do nothing
                    }
                } else {
                    if (a < *median) {
                        ++median_index;
                    } else {
                        long long m_old = *median;
                        ++median; ++median_index;
                        long long d = abs(*median - m_old);
                        size_t n_left = median_index;
                        size_t n_right = S.size() - median_index;
                        a_diff += d * (n_left - n_right);
                    }
                }
                //cout << "a_diff=" << a_diff << "; b_sum=" << b_sum << "; median_index=" << median_index << "; median=" << *median << '\n';
            } else {
                cout << *median << " " << a_diff + b_sum << '\n';
            }
        }
    }
}