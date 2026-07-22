#!/usr/bin/env python3
# guards: reflect_branch_structure, swapR_le_B_mechanism, coupled_mono_mechanism
# config: DIAGNOSTIC (not a gate) — characterise (a) the reflection branch on binding profiles
#         (A<=B vs B<A; which minimiser inequality forces Y<=B), and (b) the coupled-monotonicity
#         mechanism (does T<=T' binding + swapR give Y<=Y' and via what).
# provenance: sibling to swap-endpoint-battery.py; nails the exact minimiser-endpoint lemma shape.
from itertools import product as iproduct

def admBound(M, j): return min(M[0], M[1]) if j == 0 else M[j + 1]
def admissible(M, T):
    L = len(T)
    if any(T[j] > admBound(M, j) for j in range(L)): return False
    for i in range(L):
        for j in range(i, L):
            if T[j] > T[i]: return False
    return L >= 1 and T[L - 1] == 0
def tPrev(M, T, j): return M[0] if j == 0 else T[j - 1]
def mval(M, T):
    L = len(T)
    return sum((tPrev(M, T, j) - T[j]) * (M[j + 1] - T[j]) for j in range(L))
def binding(M):
    L = len(M) - 1
    A = [T for T in iproduct(range(max(M) + 1), repeat=L) if admissible(M, T)]
    m = min(mval(M, T) for T in A)
    return [T for T in A if mval(M, T) == m], m
def swapR(P, X, Q, A, B):
    if A <= B and B - A <= P - X: return X + (B - A)
    if B < A and A - B <= X - Q: return X - (A - B)
    return P + Q - X
def branch(P, X, Q, A, B):
    if A <= B and B - A <= P - X: return "up"
    if B < A and A - B <= X - Q: return "dn"
    return "reflect"
def F(P, x, Q, A, B): return (P - x) * (A - x) + (x - Q) * (B - Q)
def swapProfile(M, k, T):
    if k == 0: return tuple(T)
    T = list(T)
    P = M[0] if k == 1 else T[k - 2]
    T[k - 1] = swapR(P, T[k - 1], T[k], M[k], M[k + 1])
    return tuple(T)

refl_AleB = 0
refl_BltA = 0
# for reflection B<A, test whether: X==P  OR  F(X)<=F(X+1) delivers Y<=B
refl_BltA_XeqP = 0
refl_BltA_other = 0
# minimiser-neighbour test: does "for all X' in [Q,min(P,A)], F(X)<=F(X')" plus reflect conds give Y<=B?
# We already know Y<=B holds; characterise the WITNESS competitor X' with F(X')>=F(X) that pins it.
witness_kinds = {}

seen = set()
for L in range(1, 6):
    hi = 4 if L <= 3 else 3
    for M in iproduct(range(1, hi + 1), repeat=L + 1):
        if M in seen: continue
        seen.add(M)
        B_list, m = binding(M)
        for k in range(1, L):
            for T in B_list:
                P = M[0] if k == 1 else T[k - 2]
                X, Q, A, B = T[k - 1], T[k], M[k], M[k + 1]
                Y = swapR(P, X, Q, A, B)
                if branch(P, X, Q, A, B) != "reflect": continue
                if A <= B:
                    refl_AleB += 1
                    # claim: Y<=B follows from Q<=A alone (no min). verify contradiction closes:
                    # reflect A<=B => B-A > P-X ; suppose Y>B => P+Q-X>B. Then Q>A. contra Q<=A.
                    assert Y <= B
                    assert not (Q > A)
                else:
                    refl_BltA += 1
                    if X == P:
                        refl_BltA_XeqP += 1
                        assert Y == Q and Q <= B
                    else:
                        refl_BltA_other += 1
                        # X<P and X<A (X==A impossible here). right neighbour X+1 in [Q,min(P,A)].
                        assert X < P and X < A
                        # Which competitor pins Y<=B? test the reflection point itself:
                        # competitor X' = P+Q-B = the x giving swap-image exactly B (if in range).
                        # Actually: use minimality F(X) <= F(P+Q-B)?  P+Q-B in [Q,min(P,A)]?
                        xr = P + Q - B
                        inrange = Q <= xr <= min(P, A)
                        # test: is F(X) <= F(xr) AND does that alone force X>=xr? (F convex, min at x*)
                        witness_kinds[("xr_in_range", inrange)] = witness_kinds.get(("xr_in_range", inrange), 0) + 1

print(f"reflect A<=B: {refl_AleB}  (Y<=B from Q<=A, no minimality)")
print(f"reflect B<A : {refl_BltA}  = X==P (Y=Q<=B): {refl_BltA_XeqP}  + other(X<P,X<A): {refl_BltA_other}")
print(f"other-case witness (xr=P+Q-B in [Q,min(P,A)]?): {witness_kinds}")

# ---- coupled monotonicity mechanism: does atomic swapR-in-(P,X,Q) monotone hold OFF binding? ----
# find a counterexample: (P,X,Q,A,B) <= (P',X',Q',A,B) coordinatewise but swapR decreases.
cex = None
R = 5
for A in range(R):
    for B in range(R):
        for P in range(R):
            for X in range(P+1):
                for Q in range(X+1):
                    for Pp in range(P, R):
                        for Xp in range(X, min(Pp,R-1)+1):
                            for Qp in range(Q, Xp+1):
                                y = swapR(P,X,Q,A,B); yp = swapR(Pp,Xp,Qp,A,B)
                                if y > yp:
                                    cex = ((P,X,Q,A,B),(Pp,Xp,Qp,A,B),y,yp); break
                            if cex: break
                        if cex: break
                    if cex: break
                if cex: break
            if cex: break
        if cex: break
    if cex: break
print(f"atomic swapR-mono OFF binding counterexample: {cex}")
