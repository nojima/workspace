#include <algorithm>
#include <iostream>
#include <vector>
#include <complex>
#include <cmath>
#include <set>
using namespace std;

const double PI = acos(-1);
const complex<double> I(0, 1);
typedef complex<double> Complex;

namespace std {
    bool operator<(const Complex& a, const Complex& b) {
        return make_pair(a.imag(), a.real()) < make_pair(b.imag(), b.real());
    }
}

enum class EventType {
    LINE_BEGIN, LINE_END, PASSENGER,
};

struct Event {
    double y;
    EventType type;
    int index;

    bool operator<(const Event& other) const {
        return y > other.y;
    }
};

// 時計回りに45度回転
Complex rotated(const Complex& p) {
    return p * exp(-I * PI * 0.25);
}

int main() {
    int N, Q;
    while (cin >> N >> Q) {
        vector<Event> events;
        vector<Complex> ps;
        for (int i = 0; i < N; ++i) {
            double S, T, X;
            cin >> S >> T >> X;
            ps.push_back(Complex(S - 0.5, X));
            Complex p1 = rotated(Complex(S - 0.5, X));
            Complex p2 = rotated(Complex(T - 0.5, X));
            events.push_back({ p1.imag(), EventType::LINE_BEGIN, i });
            events.push_back({ p2.imag(), EventType::LINE_END, i });
        }

        for (int i = 0; i < Q; ++i) {
            double D; cin >> D;
            Complex p = rotated(Complex(D, 0));
            events.push_back({ p.imag(), EventType::PASSENGER, i });
        }

        sort(events.begin(), events.end());

        vector<double> answers(Q, -1);
        set<Complex> crossing;
        for (const Event& e : events) {
            switch (e.type) {
                case EventType::LINE_BEGIN: {
                    Complex p = ps[e.index];
                    crossing.insert(p);
                    break;
                }
                case EventType::LINE_END: {
                    Complex p = ps[e.index];
                    crossing.erase(p);
                    break;
                }
                case EventType::PASSENGER: {
                    if (crossing.empty()) break;
                    Complex p = *crossing.begin();
                    answers[e.index] = p.imag();
                    break;
                }
            }
        }

        for (double a : answers) {
            cout << (long long)round(a) << '\n';
        }
    }
}