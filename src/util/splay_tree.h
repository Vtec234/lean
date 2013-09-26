/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <algorithm>
#include <utility>
#include <vector>
#include "util/rc.h"
#include "util/pair.h"
#include "util/debug.h"
#include "util/buffer.h"

namespace lean {
/**
   \brief Splay trees (see http://en.wikipedia.org/wiki/Splay_tree)

   It uses a O(1) copy operation. Different tree can share nodes.
   The sharing is thread-safe.

   \c CMP is a functional object for comparing values of type T.
   It must have a method
   <code>
         int operator()(T const & v1, T const & v2) const;
   </code>
   The method must return
   - -1 if <tt>v1 < v2</tt>,
   - 0  if <tt>v1 == v2</tt>,
   - 1  if <tt>v1 > v2</tt>
*/
template<typename T, typename CMP>
class splay_tree : public CMP {
    struct node {
        node * m_left;
        node * m_right;
        T      m_value;
        MK_LEAN_RC();
        static void inc_ref(node * n) { if (n) n->inc_ref(); }
        static void dec_ref(node * n) { if (n) n->dec_ref(); }
        explicit node(T const & v, node * left = nullptr, node * right = nullptr):
            m_left(left), m_right(right), m_value(v), m_rc(0) {
            inc_ref(m_left);
            inc_ref(m_right);
        }
        node(node const & n):node(n.m_value, n.m_left, n.m_right) {}
        ~node() {
            dec_ref(m_left);
            dec_ref(m_right);
        }
        void dealloc() {
            delete this;
        }
        bool is_shared() const { return m_rc > 1; }

        static void display(std::ostream & out, node const * n) {
            if (n) {
                if (n->m_left == nullptr && n->m_right == nullptr) {
                    out << n->m_value << ":" << n->m_rc;
                } else {
                    out << "(" << n->m_value << ":" << n->m_rc << " ";
                    display(out, n->m_left);
                    out << " ";
                    display(out, n->m_right);
                    out << ")";
                }
            } else {
                out << "()";
            }
        }
    };

    node * m_ptr;

    int cmp(T const & v1, T const & v2) const {
        return CMP::operator()(v1, v2);
    }

    void update(node * n, node * l, node * r) {
        lean_assert(!n->is_shared());
        n->m_left  = l;
        n->m_right = r;
    }

    struct entry {
        bool m_right;
        node * m_node;
        entry(bool r, node * n):m_right(r), m_node(n) {}
    };

    void splay_to_top(std::vector<entry> & path, node * n) {
        lean_assert(!n->is_shared());
        while (path.size() > 1) {
            auto p_entry  = path.back(); path.pop_back();
            auto g_entry  = path.back(); path.pop_back();
            bool g_right  = g_entry.m_right;
            bool p_right  = p_entry.m_right;
            node * g = g_entry.m_node;
            node * p = p_entry.m_node;
            lean_assert(!g->is_shared());
            lean_assert(!p->is_shared());
            if (!g_right && !p_right) {
                // zig-zig left
                // (g (p (n A B) C) D) ==> (n A (p B (g C D)))
                lean_assert(g->m_left == p);
                node * A = n->m_left;
                node * B = n->m_right;
                node * C = p->m_right;
                node * D = g->m_right;
                update(g, C, D);
                update(p, B, g);
                update(n, A, p);
            } else if (!g_right && p_right) {
                // zig-zag left-right
                // (g (p A (n B C)) D) ==> (n (p A B) (g C D))
                lean_assert(g->m_left  == p);
                node * A = p->m_left;
                node * B = n->m_left;
                node * C = n->m_right;
                node * D = g->m_right;
                update(p, A, B);
                update(g, C, D);
                update(n, p, g);
            } else if (g_right && !p_right) {
                // zig-zag right-left
                // (g A (p (n B C) D)) ==> (n (g A B) (p C D))
                lean_assert(g->m_right == p);
                node * A = g->m_left;
                node * B = n->m_left;
                node * C = n->m_right;
                node * D = p->m_right;
                update(g, A, B);
                update(p, C, D);
                update(n, g, p);
            } else {
                lean_assert(g_right && p_right);
                lean_assert(g->m_right == p);
                // zig-zig right
                // (g A (p B (n C D))) ==> (n (p (g A B) C) D)
                node * A = g->m_left;
                node * B = p->m_left;
                node * C = n->m_left;
                node * D = n->m_right;
                update(g, A, B);
                update(p, g, C);
                update(n, p, D);
            }
        }
        lean_assert(!n->is_shared());
        if (path.size() == 1) {
            auto p_entry  = path.back(); path.pop_back();
            bool p_right  = p_entry.m_right;
            node * p      = p_entry.m_node;
            if (!p_right) {
                // zig left
                // (p (n A B) C) ==> (n A (p B C))
                node * A = n->m_left;
                node * B = n->m_right;
                node * C = p->m_right;
                update(p, B, C);
                update(n, A, p);
            } else {
                // zig right
                // (p A (n B C)) ==> (n (p A B) C)
                node * A = p->m_left;
                node * B = n->m_left;
                node * C = n->m_right;
                update(p, A, B);
                update(n, p, C);
            }
        }
        lean_assert(path.empty());
        lean_assert(!n->is_shared());
    }

    bool check_invariant(node const * n) const {
        if (n) {
            if (n->m_left) {
                check_invariant(n->m_left);
                lean_assert(cmp(n->m_left->m_value, n->m_value) < 0);
            }
            if (n->m_right) {
                check_invariant(n->m_right);
                lean_assert(cmp(n->m_value, n->m_right->m_value) < 0);
            }
        }
        return true;
    }

    void update_parent(std::vector<entry> const & path, node * child) {
        lean_assert(child);
        if (path.empty()) {
            child->inc_ref();
            node::dec_ref(m_ptr);
            m_ptr = child;
        } else {
            child->inc_ref();
            entry const & last = path.back();
            node * parent = last.m_node;
            lean_assert(!parent->is_shared());
            if (last.m_right) {
                node::dec_ref(parent->m_right);
                parent->m_right = child;
            } else {
                node::dec_ref(parent->m_left);
                parent->m_left = child;
            }
        }
    }

    static void to_buffer(node const * n, buffer<T> & r) {
        if (n) {
            to_buffer(n->m_left, r);
            r.push_back(n->m_value);
            to_buffer(n->m_right, r);
        }
    }

    bool insert_pull(T const & v, bool is_insert) {
        static thread_local std::vector<entry> path;
        node * n   = m_ptr;
        bool found = false;
        while (true) {
            if (n == nullptr) {
                if (is_insert) {
                    n = new node(v);
                    update_parent(path, n);
                } else {
                    if (path.empty())
                        return false;
                    n = path.back().m_node;
                    path.pop_back();
                }
                break;
            } else {
                if (n->is_shared()) {
                    n = new node(*n);
                    update_parent(path, n);
                }
                lean_assert(!n->is_shared());
                int c = cmp(v, n->m_value);
                if (c < 0) {
                    path.push_back(entry(false, n));
                    n = n->m_left;
                } else if (c > 0) {
                    path.push_back(entry(true, n));
                    n = n->m_right;
                } else {
                    if (is_insert)
                        n->m_value = v;
                    found      = true;
                    break;
                }
            }
        }
        splay_to_top(path, n);
        m_ptr = n;
        lean_assert(check_invariant());
        return found;
    }

    bool pull(T const & v) {
        return insert_pull(v, false);
    }

    void pull_max() {
        if (!m_ptr) return;
        static thread_local std::vector<entry> path;
        node * n   = m_ptr;
        while (true) {
            lean_assert(n);
            if (n->is_shared()) {
                n = new node(*n);
                update_parent(path, n);
            }
            if (n->m_right) {
                path.push_back(entry(true, n));
                n = n->m_right;
            } else {
                splay_to_top(path, n);
                m_ptr = n;
                lean_assert(check_invariant());
                return;
            }
        }
    }

    template<typename F, typename R>
    static R fold(node const * n, F & f, R r) {
        if (n) {
            r = fold(n->m_left, f, r);
            r = f(n->m_value, r);
            return fold(n->m_right, f, r);
        } else {
            return r;
        }
    }

    template<typename F>
    static void for_each(node const * n, F & f) {
        if (n) {
            for_each(n->m_left, f);
            f(n->m_value);
            for_each(n->m_right, f);
        }
    }

    splay_tree(splay_tree const & s, node * new_root):CMP(s), m_ptr(new_root) { node::inc_ref(m_ptr); }

public:
    splay_tree(CMP const & cmp = CMP()):CMP(cmp), m_ptr(nullptr) {}
    splay_tree(splay_tree const & s):CMP(s), m_ptr(s.m_ptr) { node::inc_ref(m_ptr); }
    splay_tree(splay_tree && s):CMP(s), m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~splay_tree() { node::dec_ref(m_ptr); }

    /** \brief O(1) copy */
    splay_tree & operator=(splay_tree const & s) { LEAN_COPY_REF(splay_tree, s); }
    /** \brief O(1) move */
    splay_tree & operator=(splay_tree && s) { LEAN_MOVE_REF(splay_tree, s); }

    void swap(splay_tree & t) { std::swap(m_ptr, t.m_ptr); }

    /** \brief Return true iff this splay tree is empty. */
    bool empty() const { return m_ptr == nullptr; }

    /** \brief Remove all elements from the splay tree. */
    void clear() { node::dec_ref(m_ptr); m_ptr = nullptr; }

    /** \brief Return true iff this splay tree and \c t point to the same node */
    bool is_eqp(splay_tree const & t) const { return m_ptr == t.m_ptr; }

    /** \brief Return the size of the splay tree */
    unsigned size() const { return fold([](T const &, unsigned a) { return a + 1; }, 0); }

    /** \brief Insert \c v in this splay tree. */
    void insert(T const & v) {
        insert_pull(v, true);
    }

    /**
        \brief Return a pointer to a value equal to \c v that is stored in this splay tree.
        If the splay tree does not contain any value equal to \c v, then return \c nullptr.

        \remark <tt>find(v) != nullptr</tt> iff <tt>contains(v)</tt>
    */
    T const * find(T const & v) const {
        node const * n = m_ptr;
        while (true) {
            if (n == nullptr)
                return nullptr;
            int c = cmp(v, n->m_value);
            if (c < 0)
                n = n->m_left;
            else if (c > 0)
                n = n->m_right;
            else
                return &(n->m_value);
        }
    }

    /** \brief Return true iff the splay tree contains an element equal to \c v. */
    bool contains(T const & v) const {
        return find(v);
    }

    /**
        \brief Similar to \c find, but the splay tree is reorganized.
        If <tt>find(v)</tt> is invoked after <tt>find_memoize(v)</tt>, then the cost will be O(1).
        The idea is to move recently accessed elements close to the root.
    */
    T const * find_memoize(T const & v) {
        if (pull(v)) {
            lean_assert(cmp(m_ptr->m_value, v) == 0);
            return &(m_ptr->m_value);
        } else {
            return nullptr;
        }
    }

    /** \brief Remove \c v from this splay tree. Actually, it removes an element that is equal to \c v. */
    void erase(T const & v) {
        if (pull(v)) {
            lean_assert(cmp(m_ptr->m_value, v) == 0);
            splay_tree left(*this, m_ptr->m_left);
            splay_tree right(*this, m_ptr->m_right);
            if (left.empty()) {
                swap(right);
            } else if (right.empty()) {
                swap(left);
            } else {
                clear();
                left.pull_max();
                lean_assert(left.m_ptr->m_right == nullptr);
                right.m_ptr->inc_ref();
                left.m_ptr->m_right = right.m_ptr;
                swap(left);
            }
        }
    }

    /** \brief (For debugging) Check whether this splay tree is well formed. */
    bool check_invariant() const {
        return check_invariant(m_ptr);
    }

    /**
        \brief Copy the contents of this splay tree to the given buffer.
        The elements will be stored in increasing order.
    */
    void to_buffer(buffer<T> & r) const {
        to_buffer(m_ptr, r);
    }

    /** \brief (For debugging) Display the content of this splay tree. */
    friend std::ostream & operator<<(std::ostream & out, splay_tree const & t) {
        node::display(out, t.m_ptr);
        return out;
    }

    /**
       \brief Return <tt>f(a_k, ..., f(a_1, f(a_0, r)) ...)</tt>, where
       <tt>a_0, a_1, ... a_k</tt> are the elements is stored in the splay tree.
    */
    template<typename F, typename R>
    R fold(F f, R r) const {
        return fold(m_ptr, f, r);
    }

    /**
       \brief Apply \c f to each value stored in the splay tree.
    */
    template<typename F>
    void for_each(F f) const {
        for_each(m_ptr, f);
    }
};
template<typename T, typename CMP>
splay_tree<T, CMP> insert(splay_tree<T, CMP> & t, T const & v) { splay_tree<T, CMP> r(t); r.insert(v); return r; }
template<typename T, typename CMP>
splay_tree<T, CMP> erase(splay_tree<T, CMP> & t, T const & v) { splay_tree<T, CMP> r(t); r.erase(v); return r; }
template<typename T, typename CMP, typename F, typename R>
R fold(splay_tree<T, CMP> const & t, F f, R r) {
    return t.fold(f, r);
}
template<typename T, typename CMP, typename F>
void for_each(splay_tree<T, CMP> const & t, F f) {
    return t.for_each(f);
}
}
