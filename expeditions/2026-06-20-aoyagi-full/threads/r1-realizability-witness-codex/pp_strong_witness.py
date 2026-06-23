#!/usr/bin/env python3
"""
STRONGER property-breaker: find an admissible witness where the LEFT-WIDTH cap t_j <= M_i at an
INTERIOR cell (0<i<j) is genuinely DELIVERED BY MONOTONICITY, i.e. where the per-block bound at j-1
does NOT directly give t_j <= M_i (so the cascade's feasibility relies on the monotone descent chain).

Strong demands beyond the 4 codex properties:
  (Q1) L >= 4 (room for a real interior window)
  (Q2) an INTERIOR increasing width step  M_s < M_{s+1}  with 0 < s < L-1
  (Q3) a cell (i,j) with 0<i<j and t_j = T_{j-1} > 0 such that the LOCAL per-block bound admBound(j-1)
       EXCEEDS M_i  (so 'T_{j-1} <= admBound(j-1)' alone would NOT bound it below M_i;
       feasibility t_j<=M_i must come from monotone descent T_{j-1}<=...<=admBound(<i> region)).
  (Q4) strict interior drop T_s>T_{s+1} for some interior s.
Then verify exact cascade == codex == core, and that a non-monotone perturbation that respects per-block
breaks it AT THAT interior cell (overshoot beyond the true rank).
"""
import sympy as sp
from itertools import product

def admBound(M, j):
    return min(M[0], M[1]) if j == 0 else M[j+1]
def admPred(M, T):
    L = len(M)-1
    if any(T[j] > admBound(M, j) for j in range(L)): return False
    if any(T[j] > T[i] for i in range(L) for j in range(i, L)): return False
    if L >= 1 and T[L-1] != 0: return False
    return True
def perblock(M, T):
    L = len(M)-1
    return all(T[j] <= admBound(M, j) for j in range(L))
def partialId(r, c, t):
    return sp.Matrix(r, c, lambda a, b: 1 if (a == b and a < t) else 0)
def submult(M, T, i, j):
    P = sp.eye(M[i])
    for s in range(i, j):
        P = partialId(M[s+1], M[s], T[s]) * P
    return P
def rankFn_exact(M, T):
    L = len(M)-1; R = {}
    for i in range(L+1):
        for j in range(L+1):
            R[(i, j)] = submult(M, T, i, j).rank() if i < j else (M[i] if i == j else 0)
    return R
def expSurv(M, T, j): return M[0] if j == 0 else T[j-1]
def codex(M, T):
    L = len(M)-1
    return {(i, j): (expSurv(M, T, j) if i < j else (M[i] if i == j else 0))
            for i in range(L+1) for j in range(L+1)}
def core(M, T):
    L = len(M)-1; R = {}
    for i in range(L+1):
        for j in range(L+1):
            if i < j: R[(i, j)] = min(min(T[p] for p in range(i, j)), min(M[i], M[j]))
            else: R[(i, j)] = M[i] if i == j else 0
    return R

found = None
for L in [4]:
    for M in product(range(1, 5), repeat=L+1):
        M = list(M)
        # Q2: interior increasing step
        if not any(M[s] < M[s+1] for s in range(1, L-1)): continue
        for T in product(*[range(admBound(M, j)+1) for j in range(L)]):
            T = list(T)
            if not admPred(M, T): continue
            t = [M[0]] + list(T)
            # Q4: interior strict drop
            if not any(T[s] > T[s+1] for s in range(1, L-1)): continue
            # Q3: an interior cell (i,j) where local block bound exceeds M_i but monotonicity saves it
            hit = None
            for i in range(1, L):
                for j in range(i+1, L+1):
                    tj = t[j]
                    if tj <= 0: continue
                    # local per-block bound at the relevant index (j-1)
                    local_bound = admBound(M, j-1)
                    if local_bound > M[i] and tj <= M[i]:
                        # feasibility t_j<=M_i is NOT given by local bound alone; monotonicity delivers it
                        hit = (i, j, tj, M[i], local_bound)
                        break
                if hit: break
            if hit:
                found = (M, T, hit); break
        if found: break
    if found: break

if not found:
    print("No witness with the STRONG interior monotone-feasibility property in L=4, widths 1..4.")
    print("Interpretation: at admissible T the left-width cap is often already implied locally; widen the search or accept the L<=4 witness.")
else:
    M, T, hit = found
    i, j, tj, Mi, lb = hit
    L = len(M)-1
    print(f"STRONG WITNESS: M={M}  T={T}  (admissible={admPred(M,T)})")
    print(f"  running ranks t = {[M[0]]+list(T)}")
    print(f"  interior increasing width steps (0<s<L-1): {[s for s in range(1,L-1) if M[s]<M[s+1]]}")
    print(f"  interior strict drops (0<s<L-1): {[s for s in range(1,L-1) if T[s]>T[s+1]]}")
    print(f"  load-bearing interior cell (i,j)=({i},{j}): codex t_j={tj}, M_i={Mi}, LOCAL block bound admBound({j-1})={lb} > M_i")
    print(f"    => 'T_{j-1} <= admBound({j-1})={lb}' does NOT bound t_j below M_i={Mi}; monotone descent does.")
    print()
    Re = rankFn_exact(M, T); Rcd = codex(M, T); Rco = core(M, T)
    print("  EXACT cascade rank pattern (i<=j):")
    print("    i\\j " + "  ".join(str(j) for j in range(L+1)))
    for ii in range(L+1):
        print(f"     {ii} : " + "  ".join(str(Re[(ii, jj)]) for jj in range(L+1)))
    print(f"  exact == codex : {all(Re[k]==Rcd[k] for k in Re)}")
    print(f"  exact == core  : {all(Re[k]==Rco[k] for k in Re)}")
    P = submult(M, T, i, j)
    print(f"\n  interior cell ({i},{j}) actual submult A_{{{j-1}}}..A_{{{i}}}  shape {P.shape}, EXACT rank {P.rank()} (=codex t_j={tj}):")
    sp.pprint(P)
    # non-monotone perturbation overshoot at this cell
    print("\n  non-monotone (per-block) perturbation overshoot:")
    for Tp in product(*[range(admBound(M, jj)+1) for jj in range(L)]):
        Tp = list(Tp)
        if not perblock(M, Tp): continue
        if all(Tp[a] >= Tp[b] for a in range(L) for b in range(a, L)): continue  # want non-monotone
        Rep = rankFn_exact(M, Tp); Rcdp = codex(M, Tp)
        diff = [(k, Rep[k], Rcdp[k]) for k in Rep if Rep[k] != Rcdp[k]]
        if diff:
            print(f"    T'={Tp} (running {[M[0]]+Tp}) breaks at (cell,exact,codex): {diff[:4]}")
            break
