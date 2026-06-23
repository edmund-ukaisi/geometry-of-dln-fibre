#!/usr/bin/env python3
"""
WHICH admissibility clause forces CODEX(column-constant) == CORE(capped window-min)?

CODEX i<j = t_j  (running rank, t_0=M_0, t_{j}=T_{j-1})
CORE  i<j = min( min_{i<=p<j} T_p ,  min(M_i, M_j) )

Claim chain to verify (the monotonicity route):
 (a) admPred => running ranks t = (M_0, T_0, ..., T_{L-1}) weakly DECREASING.
     Needs: t_0=M_0 >= t_1=T_0  (from T_0 <= admBound_0 = min(M_0,M_1) <= M_0)
            t_{j} = T_{j-1} >= t_{j+1} = T_j  (from weak decrease of T)
 (b) t weakly decreasing => window-min over T on [i,j) relates to endpoints:
        min_{i<=p<j} T_p = T_{j-1} = t_j   (the LAST T index, since T decreasing => min at largest p)
     AND we must show min(t_j, min(M_i,M_j)) = t_j, i.e. t_j <= min(M_i, M_j).
        Need t_j <= M_i and t_j <= M_j for i<j.
 (c) so CORE i<j = t_j = CODEX i<j.

So the load-bearing facts beyond "T decreasing" are the WIDTH caps t_j <= M_i and t_j <= M_j.
Let's see which admPred clause gives each, and whether removing a clause breaks codex==core.
"""
from itertools import product

def admBound(M, j):
    return min(M[0], M[1]) if j == 0 else M[j+1]

def clause_perblock(M, T):
    L = len(M)-1
    return all(T[j] <= admBound(M, j) for j in range(L))
def clause_monotone(M, T):
    L = len(M)-1
    return all(T[j] <= T[i] for i in range(L) for j in range(i, L))
def clause_lastzero(M, T):
    L = len(M)-1
    return (L < 1) or T[L-1] == 0

def t_running(M, T):
    return [M[0]] + list(T)

def codex_minus_core_cells(M, T):
    """Return cells (i,j),i<j where CODEX != CORE."""
    L = len(M)-1
    t = t_running(M, T)
    out = []
    for i in range(L+1):
        for j in range(i+1, L+1):
            codex = t[j]
            wmin = min(T[p] for p in range(i, j))
            core = min(wmin, min(M[i], M[j]))
            if codex != core:
                out.append(((i, j), core, codex))
    return out

# For each subset of clauses, count (M,T) where codex != core.
def sweep(predicate, label):
    bad = []
    checked = 0
    for L in [2, 3, 4]:
        for M in product(range(1, 5), repeat=L+1):
            M = list(M)
            for T in product(*[range(max(M)+1) for _ in range(L)]):
                T = list(T)
                if not predicate(M, T):
                    continue
                checked += 1
                diff = codex_minus_core_cells(M, T)
                if diff:
                    bad.append((tuple(M), tuple(T), diff[:2]))
    print(f"[{label}] checked={checked}  codex!=core count={len(bad)}")
    for b in bad[:6]:
        print("     M,T,diffs(cell,core,codex):", b)
    print()
    return bad

print("Question: which clauses are needed to force CODEX == CORE?\n")

sweep(lambda M, T: True, "NO clauses (all T)")
sweep(lambda M, T: clause_perblock(M, T), "per-block bound only")
sweep(lambda M, T: clause_monotone(M, T), "monotone only")
sweep(lambda M, T: clause_perblock(M, T) and clause_monotone(M, T), "per-block + monotone")
sweep(lambda M, T: clause_monotone(M, T) and clause_lastzero(M, T), "monotone + lastzero")
sweep(lambda M, T: clause_perblock(M, T) and clause_monotone(M, T) and clause_lastzero(M, T),
      "ALL THREE (= admPred)")

# Decompose the needed facts: for codex==core we need, for all i<j:
#   t_j = min_{i<=p<j} T_p   AND   t_j <= min(M_i, M_j).
# Verify each sub-fact under (per-block + monotone):
print("=== sub-fact verification under (per-block + monotone) ===")
f1_bad = []  # window-min over T[i,j) != t_j
f2a_bad = []  # t_j > M_i  (left width cap)
f2b_bad = []  # t_j > M_j  (right width cap)
for L in [2, 3, 4]:
    for M in product(range(1, 5), repeat=L+1):
        M = list(M)
        for T in product(*[range(max(M)+1) for _ in range(L)]):
            T = list(T)
            if not (clause_perblock(M, T) and clause_monotone(M, T)):
                continue
            t = t_running(M, T)
            for i in range(L+1):
                for j in range(i+1, L+1):
                    wmin = min(T[p] for p in range(i, j))
                    if wmin != t[j]:
                        f1_bad.append((tuple(M), tuple(T), (i, j), wmin, t[j]))
                    if t[j] > M[i]:
                        f2a_bad.append((tuple(M), tuple(T), (i, j), t[j], M[i]))
                    if t[j] > M[j]:
                        f2b_bad.append((tuple(M), tuple(T), (i, j), t[j], M[j]))
print(f"  F1 (window-min_T[i,j) = t_j) violations: {len(f1_bad)}", f1_bad[:3])
print(f"  F2a (t_j <= M_i) violations:             {len(f2a_bad)}", f2a_bad[:3])
print(f"  F2b (t_j <= M_j) violations:             {len(f2b_bad)}", f2b_bad[:3])
