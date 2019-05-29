#include <iostream>
#include <string>
#include <utility>
#include <vector>
#include <algorithm>
using namespace std;

struct Item {
    string name;
    int score;
    int index;

    bool operator<(const Item& other) const {
        return make_pair(name, -score) < make_pair(other.name, -other.score);
    }
};

int main() {
    int N;
    while (cin >> N) {
        vector<Item> rs;
        for (int i = 0; i < N; ++i) {
            string name;
            int score;
            cin >> name >> score;
            rs.push_back({ name, score, i });
        }
        sort(rs.begin(), rs.end());
        for (int i = 0; i < N; ++i) {
            cout << rs[i].index + 1 << '\n';
        }
    }
}