"""Exact multispecies-coalescent gene tree distributions (one lineage per taxon unless stated).
Forest = frozenset of frozensets (clusters).  Species tree: nested tuples with lengths:
  leaf: 'a'; internal: (children_tuple, length_symbol_or_None)  (None = root)."""
import sympy as sp
from itertools import combinations
from functools import lru_cache

def roots(F):
    return [A for A in F if not any(A < B for B in F)]

def merges(F):
    R = roots(F)
    out = []
    for A, B in combinations(R, 2):
        out.append(frozenset(F | {A | B}))
    return out

def jump(dist):
    """one jump-chain step on a dict forest->weight (only forests with >=2 roots move)"""
    new = {}
    for F, w in dist.items():
        R = roots(F)
        k = len(R)
        if k < 2:
            new[F] = new.get(F, 0) + w
            continue
        c = sp.Rational(1, k*(k-1)//2)
        for G in merges(F):
            new[G] = new.get(G, 0) + w*c
    return new

def g(i, j, T):
    """Tavare g_ij(t) with T = exp(-t)."""
    tot = 0
    for k in range(j, i+1):
        coef = sp.Rational((2*k-1)*(-1)**(k-j), sp.factorial(j)*sp.factorial(k-j)*(j+k-1))
        prod = sp.Integer(1)
        for m in range(k):
            prod *= sp.Rational((j+m)*(i-m), (i+m))
        tot += T**(k*(k-1)//2) * coef * prod
    return sp.expand(tot)

def evolve(dist, T):
    """population of length t (T = e^{-t}): K_t = sum_m g_{k,k-m} J^m"""
    new = {}
    for F, w in dist.items():
        k = len(roots(F))
        cur = {F: sp.Integer(1)}
        for m in range(0, max(k-1, 0)+1):
            if m > k-1: break
            gk = g(k, k-m, T) if k >= 1 else 1
            for G, v in cur.items():
                new[G] = new.get(G, 0) + w*gk*v
            cur = jump(cur)
    return {F: sp.expand(v) for F, v in new.items()}

def absorb(dist):
    cur = dict(dist)
    for _ in range(10):
        cur = jump(cur)
    return {F: sp.expand(v) for F, v in cur.items()}

def leaves(tree):
    if isinstance(tree, str): return [tree]
    return [x for c in tree[0] for x in leaves(c)]

def top(tree, samples=None):
    """distribution of forest at the top of the population above `tree`; samples: taxon->list of lineage names"""
    if isinstance(tree, str):
        lin = samples[tree] if samples else [tree.upper()]
        F = frozenset(frozenset([l]) for l in lin)
        return {F: sp.Integer(1)}
    children, T = tree
    ent = {frozenset(): sp.Integer(1)}
    for c in children:
        d = top(c, samples)
        new = {}
        for F1, w1 in ent.items():
            for F2, w2 in d.items():
                G = F1 | F2
                new[G] = new.get(G, 0) + w1*w2
        ent = new
    if T is None:
        return absorb(ent)
    return evolve(ent, T)

def unroot(G, allL):
    U = frozenset(allL)
    S = set()
    for A in G:
        if A != U:
            S.add(A); S.add(U - A)
    return frozenset(S)

def unrooted_dist(tree, samples=None):
    G = top(tree, samples)
    allL = frozenset().union(*[A for F in G for A in F])
    out = {}
    for F, w in G.items():
        k = unroot(F, allL)
        out[k] = sp.expand(out.get(k, 0) + w)
    return out

def nontrivial_splits(T, allL):
    n = len(allL)
    res = set()
    for A in T:
        if 2 <= len(A) <= n-2:
            B = frozenset(allL) - A
            res.add(frozenset([A, B]))
    return res
