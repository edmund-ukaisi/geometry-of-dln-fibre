#!/usr/bin/env python3
# guards: swapR_mono_abstract, swapR_le_B_abstract, tie_subcase
# config: DECOUPLE monotonicity from profiles.  Over all (P,X,Q,A,B),(P',X',Q',A,B) with
#         P<=P', X<=X', Q<=Q', ranges valid (Q<=X<=P, X<=A, Q<=A, Q<=B), AND X a minimiser of
#         F_{P,Q,A,B} over [Q,min(P,A)], X' a minimiser of F_{P',Q',A,B} over [Q',min(P',A)]:
#         assert swapR(P,X,Q,A,B) <= swapR(P',X',Q',A,B).  If TRUE it is a pure swapR+minimiser
#         fact (provable). Also: (i) confirm Y<=B from the SAME minimiser hyp; (ii) isolate the
#         tie sub-case (P=P',Q=Q',X'=X+1 both minimisers) and check swapR still monotone there;
#         (iii) test whether the LINEAR neighbour inequalities alone (post case-split) pin Y<=Y'.
from itertools import product as iproduct

def swapR(P, X, Q, A, B):
    if A <= B and B - A <= P - X: return X + (B - A)
    if B < A and A - B <= X - Q: return X - (A - B)
    return P + Q - X
def F(P, x, Q, A, B): return (P - x) * (A - x) + (x - Q) * (B - Q)

def is_min(P, X, Q, A, B):
    m = min(P, A)
    if not (Q <= X <= m): return False
    return F(P, X, Q, A, B) == min(F(P, x, Q, A, B) for x in range(Q, m + 1))

R = 7
mono_fail = 0
YleB_fail = 0
tie_count = 0
tie_fail = 0
# collect the (X<P?,X<A?,X>Q?) and (X'<P'?,...) neighbour-inequality "profile" for mono cases
# to gauge omega feasibility: does {ranges,branch-conds,mono-coords,available neighbour-ineqs} => Y<=Y'?
examples = 0
for A in range(R):
    for B in range(R):
        for P in range(R):
            for X in range(Q0 := 0, P + 1):
                for Q in range(0, X + 1):
                    if not (X <= A and Q <= A and Q <= B): continue
                    if not is_min(P, X, Q, A, B): continue
                    Y = swapR(P, X, Q, A, B)
                    if Y > B: YleB_fail += 1
                    for Pp in range(P, R):
                        for Xp in range(X, min(Pp, R - 1) + 1):
                            for Qp in range(Q, Xp + 1):
                                if not (Xp <= A and Qp <= A and Qp <= B): continue
                                if not is_min(Pp, Xp, Qp, A, B): continue
                                Yp = swapR(Pp, Xp, Qp, A, B)
                                if Y > Yp:
                                    mono_fail += 1
                                    if mono_fail <= 8:
                                        print(f"  MONO-FAIL (P,X,Q,A,B)={(P,X,Q,A,B)}->{Y}  "
                                              f"(P',X',Q')={(Pp,Xp,Qp)}->{Yp}")
                                # tie sub-case
                                if P == Pp and Q == Qp and Xp == X + 1:
                                    tie_count += 1
                                    if Y > Yp: tie_fail += 1

print(f"swapR minimiser-monotonicity fails: {mono_fail}")
print(f"Y<=B fails (from minimiser hyp): {YleB_fail}")
print(f"tie sub-case (P=P',Q=Q',X'=X+1, both min): {tie_count}, mono-fails there: {tie_fail}")
print("ABSTRACT MONO HOLDS" if mono_fail == 0 else "ABSTRACT MONO FAILS")
