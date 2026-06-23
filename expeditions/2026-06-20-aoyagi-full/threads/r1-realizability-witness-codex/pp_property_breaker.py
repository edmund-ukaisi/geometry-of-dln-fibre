#!/usr/bin/env python3
"""
CHECK 3 — adversarial property-breaker witness.
Find an ADMISSIBLE (M,T) with ALL FOUR codex-prescribed stress properties:
  (P1) L >= 3
  (P2) an interior nonzero T_{j-1} > 0 with 0 < i < j < L+1  (a genuine interior 2-index cell)
  (P3) at least one strict positive drop  T_s > T_{s+1}  before the forced final zero
  (P4) an increasing width step  M_s < M_{s+1}  (so left-width feasibility t_j<=M_i must come from monotonicity)
Then:
  (A) build the ACTUAL cascade matrices over QQ, take EXACT ranks -> rankFn_exact
  (B) compute codex achieverRankPattern and core survivors pattern
  (C) confirm rankFn_exact == codex == core
  (D) PERTURB T to a NON-monotone T' (still per-block feasible) and show the equality BREAKS at the
      cell that the width-cap protects -> the agreement RIDES monotonicity, it is content not identity.
"""
import sympy as sp
from itertools import product

def admBound(M, j):
    return min(M[0], M[1]) if j == 0 else M[j+1]
def admPred(M, T):
    L = len(M)-1
    if any(T[j] > admBound(M, j) for j in range(L)):
        return False
    if any(T[j] > T[i] for i in range(L) for j in range(i, L)):
        return False
    if L >= 1 and T[L-1] != 0:
        return False
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
    L = len(M)-1
    R = {}
    for i in range(L+1):
        for j in range(L+1):
            if i < j:
                R[(i, j)] = submult(M, T, i, j).rank()
            elif i == j:
                R[(i, j)] = M[i]
            else:
                R[(i, j)] = 0
    return R
def expSurv(M, T, j):
    return M[0] if j == 0 else T[j-1]
def codex(M, T):
    L = len(M)-1
    return {(i, j): (expSurv(M, T, j) if i < j else (M[i] if i == j else 0))
            for i in range(L+1) for j in range(L+1)}
def core(M, T):
    L = len(M)-1
    R = {}
    for i in range(L+1):
        for j in range(L+1):
            if i < j:
                R[(i, j)] = min(min(T[p] for p in range(i, j)), min(M[i], M[j]))
            elif i == j:
                R[(i, j)] = M[i]
            else:
                R[(i, j)] = 0
    return R

# --- hunt for a witness with all four properties ---
def props(M, T):
    L = len(M)-1
    p1 = L >= 3
    # P2: interior nonzero cell 0<i<j<L+1 whose codex value expSurv(j)=T_{j-1}>0
    p2 = any(0 < i < j < L+1 and expSurv(M, T, j) > 0 for i in range(L+1) for j in range(L+1))
    p3 = any(T[s] > T[s+1] for s in range(L-1))           # strict drop before final zero
    p4 = any(M[s] < M[s+1] for s in range(L))             # increasing width step
    return p1, p2, p3, p4

best = None
for L in [3, 4]:
    for M in product(range(1, 5), repeat=L+1):
        M = list(M)
        for T in Adm if False else (Tt for Tt in product(*[range(admBound(M, j)+1) for j in range(L)])):
            T = list(T)
            if not admPred(M, T):
                continue
            p1, p2, p3, p4 = props(M, T)
            if p1 and p2 and p3 and p4:
                # prefer a witness with an increasing step strictly INSIDE and a clear interior cell
                best = (M, T)
                break
        if best:
            break
    if best:
        break

print("WITNESS with all four properties (P1 L>=3, P2 interior nonzero, P3 strict drop, P4 increasing width):")
M, T = best
print(f"  M = {M}   T = {T}   admissible = {admPred(M,T)}")
print(f"  properties (p1,p2,p3,p4) = {props(M,T)}")
print(f"  running ranks t = {[M[0]]+list(T)}  (weakly decreasing: {all(([M[0]]+list(T))[s]>=([M[0]]+list(T))[s+1] for s in range(L))})")
print(f"  increasing width steps M_s<M_{{s+1}} at s = {[s for s in range(len(M)-1) if M[s]<M[s+1]]}")
print()

Re = rankFn_exact(M, T)
Rcd = codex(M, T)
Rco = core(M, T)
L = len(M)-1
print("  full rank pattern (i<=j), EXACT cascade vs codex vs core:")
print("    i\\j", "  ".join(str(j) for j in range(L+1)))
for i in range(L+1):
    row_e = "  ".join(str(Re[(i, j)]) for j in range(L+1))
    print(f"     {i} : {row_e}")
match_ec = all(Re[k] == Rcd[k] for k in Re)
match_eo = all(Re[k] == Rco[k] for k in Re)
print(f"  exact == codex : {match_ec}")
print(f"  exact == core  : {match_eo}")
# show the actual interior matrix that is rank-taken at a P2 cell
for i in range(1, L+1):
    for j in range(i+1, L+1):
        if expSurv(M, T, j) > 0:
            P = submult(M, T, i, j)
            print(f"\n  interior cell (i,j)=({i},{j}): submult = A_{{{j-1}}}..A_{{{i}}}, shape {P.shape}, EXACT rank {P.rank()}")
            print(f"     codex value t_{j} = {expSurv(M,T,j)} ; core value = {Rco[(i,j)]} ; matrix:")
            sp.pprint(P)
            break
    else:
        continue
    break

# --- (D) NON-MONOTONE perturbation: does the equality break? ---
print("\n=== (D) non-monotone perturbation breaks the equality (agreement rides monotonicity) ===")
# find a per-block-feasible but NON-monotone T' near the witness that breaks codex==exact at a width-cap cell
broke = None
for Tp in product(*[range(admBound(M, j)+1) for j in range(L)]):
    Tp = list(Tp)
    if not perblock(M, Tp):
        continue
    mono = all(Tp[a] >= Tp[b] for a in range(L) for b in range(a, L))
    if mono:
        continue                       # we want NON-monotone
    Rep = rankFn_exact(M, Tp)
    Rcdp = codex(M, Tp)
    diff = [(k, Rep[k], Rcdp[k]) for k in Rep if Rep[k] != Rcdp[k]]
    if diff:
        broke = (Tp, diff)
        break
if broke:
    Tp, diff = broke
    print(f"  perturbed T' = {Tp}  (per-block feasible, NON-monotone: running ranks {[M[0]]+Tp})")
    print(f"  exact rankFn(cascade T') != codex(T') at cells (cell, exact, codex):")
    for d in diff[:5]:
        print("     ", d)
    print("  => the codex column-constant value OVERSHOOTS the true rank once monotonicity is dropped:")
    print("     the equality is genuine CONTENT carried by admissibility, NOT a definitional identity.")
else:
    print("  (no non-monotone per-block T' breaks it for this M — try the explicit construction below)")
