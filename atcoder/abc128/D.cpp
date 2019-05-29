#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;

int main() {
    int N, K;
    while (cin >> N >> K) {
        vector<long long> values;
        for (int i = 0; i < N; ++i) {
            long long v; cin >> v;
            values.push_back(v);
        }

        long long answer = -1;
        for (int n_left = 0; n_left <= N; ++n_left) {
            for (int n_right = 0; n_right <= N; ++n_right) {
                if (n_left + n_right > N || n_left + n_right > K) break;
                vector<long long> hand;
                hand.insert(hand.end(), values.begin(), values.begin() + n_left);
                hand.insert(hand.end(), values.end() - n_right, values.end());
                sort(hand.begin(), hand.end());
                long long sum_return = 0;
                for (int i = 0; i < (int)hand.size(); ++i) {
                    if (i >= K - (n_left + n_right)) break;
                    if (hand[i] >= 0) break;
                    sum_return += hand[i];
                }
                long long sum = 0;
                for (auto v : hand) {
                    sum += v;
                }
                answer = max(answer, sum - sum_return);
            }
        }

        cout << answer << endl;
    }
}