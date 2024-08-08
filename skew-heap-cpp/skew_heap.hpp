#pragma once
#include <memory>

namespace skewheap {

template<typename T>
struct Node {
    T x;
    Node* l;
    Node* r;
    Node* parent;

    static Node<T>* empty() {
        return nullptr;
    }

    static Node<T>* singleton(T x) {
        return new Node<T>{x, nullptr, nullptr};
    }

    static Node<T>* meld(Node<T>* a, Node<T>* b, Node<T>* parent) {
        if (a == nullptr && b == nullptr) {
            return nullptr;
        }
        if (a == nullptr) {
            b->parent = parent;
            return b;
        }
        if (b == nullptr) {
            a->parent = parent;
            return a;
        }
        if (a->x > b->x) std::swap(a, b);
        a->r = meld(a->r, b, a);
        std::swap(a->l, a->r);
        a->parent = parent;
        return a;
    }

    Node* push(T x) {
        return meld(this, singleton(x));
    }

    T pop() {
        meld(l, r);
    }
};

} // namespace skewheap
