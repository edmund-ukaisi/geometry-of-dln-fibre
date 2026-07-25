#!/usr/bin/env python3
"""PNP hcover residual probe (exact): does the Schur clearing succeed for an ARBITRARY pivot
(not just the canonical (0,0))?  If yes, every full-fan chart is a VALID resolution chart, so
fan-completeness reduces to ENUMERATION in buildTree (a provenance question), not to whether
off-canonical charts exist.  Also confirm the shear coefficient bound (Codex's refinement:
degree-2 + |coeff| bound; here coeffs are +/-1, so sum|a| = #products = C)."""
import sympy as sp
import itertools

print("="*72)
print("Schur clearing succeeds for ANY pivot in a 3x3 block (=> every fan chart is valid)")
print("="*72)
A = sp.Matrix(3,3, lambda i,j: sp.Symbol(f'a{i}{j}'))
ok_all = True
coeff_bound_ok = True
for (pi,pj) in itertools.product(range(3),range(3)):
    # pivot (pi,pj) normalized to a unit (post-blowup pivot = 1); model by setting a_{pi,pj}=1 chart
    Ap = A.copy(); Ap[pi,pj] = 1
    # permute pivot to (0,0)
    rperm = [pi]+[i for i in range(3) if i!=pi]
    cperm = [pj]+[j for j in range(3) if j!=pj]
    P = Ap[rperm,cperm]        # pivot now at (0,0)=1
    C12 = P[0,1:]; C21 = P[1:,0]; C22 = P[1:,1:]
    Q1 = sp.eye(3); Q1[1,0]=-C21[0]; Q1[2,0]=-C21[1]
    Q2 = sp.eye(3); Q2[0,1]=-C12[0]; Q2[0,2]=-C12[1]
    res = sp.expand(Q1*P*Q2)
    Delta = sp.expand(C22 - C21*C12)
    target = sp.Matrix([[1,0,0],[0,Delta[0,0],Delta[0,1]],[0,Delta[1,0],Delta[1,1]]])
    if sp.expand(res-target) != sp.zeros(3,3):
        ok_all=False
    # coefficient bound: Delta entries = a - c*r, coeffs +/-1
    for e in list(Delta):
        p = sp.Poly(sp.expand(e), *sorted(e.free_symbols,key=str))
        if any(abs(c)!=1 for c in p.coeffs()):
            coeff_bound_ok=False
print(f"  Schur clearing Q1*A*Q2 = diag(1,Delta) for ALL 9 pivots: {ok_all}")
print(f"  shear coefficients all +/-1 (=> sum|a| = #products = C, Codex's bound): {coeff_bound_ok}")
print()
print("CONSEQUENCE: every full-fan chart (any pivot) is a genuine Schur-clearing resolution chart;")
print("fan-completeness = does buildTree ENUMERATE all pivots (provenance), NOT whether they exist.")
print("The loss K = ||prod C||_F^2 is invariant under row-perms(C^1) x col-perms(C^L), so the")
print("full fan is the SYMMETRY ORBIT of the col-pinned ledger charts (the #86(B) transport).")
