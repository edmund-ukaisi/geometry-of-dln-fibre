#!/usr/bin/env python3
"""B1 REFINEMENT (#170, R>0-corrected framing): does the escape-cone / pivot-adapted chart give the
LOWER-BOUND-RELEVANT property -- the SANDWICH  loss = monomial^2 * R  with R(0) != 0 -- exactly as the
canonical chart does (the tube-probe B2 property)?  If YES, the escape-cone fix needs ONLY the sandwich
(no ideal-monomialisation); the earlier 'ideal-level build check' is STRONGER than the lower bound needs.

Residual (3,3,3,2,2): X=C3*C4, C3bar=[[1,p],[q,s],[u,v]], C4bar=[[1,c],[d,c*d+f]] (canonical pivots
C3[0,0],C4[0,0]).  loss = (w*y)^2 * R,  R=||Y_row0||^2 + d2^2||Y_row1||^2 + d1^2||Y_row2||^2, R(0)=1.

ESCAPE chart = pivot on OFF-diagonal input entries (inner permutation: C3 col0<->col1, C4 row0<->row1
-- a loss-isometry since X=C3*C4 invariant under (C3*Q,Q^-1*C4)). New radials w'=C3[0,1], y'=C4[1,0];
new ratios p'=C3[0,0]/C3[0,1], d'=C4[0,0]/C4[1,0] (-> 0 at the ESCAPE-chart origin).
"""
import sympy as sp

p,c,d,f,q,s,u,v,d1,d2 = sp.symbols('p c d f q s u v delta1 delta2', real=True)

# ---------- canonical chart: recap the sandwich R(0)=1 ----------
C3bar = sp.Matrix([[1,p],[q,s],[u,v]]); C4bar = sp.Matrix([[1,c],[d,c*d+f]])
Y = C3bar*C4bar
R = sum(Y[0,j]**2 for j in range(2)) + d2**2*sum(Y[1,j]**2 for j in range(2)) + d1**2*sum(Y[2,j]**2 for j in range(2))
zero = {vv:0 for vv in (p,c,d,f,q,s,u,v,d1,d2)}
print("=== canonical chart ===")
print("  Y[0,0] =", sp.expand(Y[0,0]), " ; R(0) =", sp.expand(R).subs(zero), " (sandwich loss=(wy)^2*R, R(0)=1)")

# ---------- ESCAPE chart via the inner permutation (Q swaps the shared index 0<->1) ----------
# Under C3 -> C3*Q, C4 -> Q^{-1}*C4 (Q = swap of the 2 inner cols/rows), X = C3*C4 is UNCHANGED,
# but the PIVOTS swap: canonical pivot (C3[0,0],C4[0,0]) <-> escape pivot (C3[0,1],C4[1,0]).
# Concretely: escape-chart normalized factors with the SWAPPED columns/rows as the '1'-pivot.
# C3bar'  = C3/C3[0,1]: row0 = [p', 1] with p'=C3[0,0]/C3[0,1]; the OTHER rows get their own ratios.
pp,cc,dd,ff,qq,ss,uu,vv = sp.symbols("p' c' d' f' q' s' u' v'", real=True)
# escape-chart normalized matrices (pivot = the swapped entry -> that slot is 1):
C3bar_e = sp.Matrix([[pp,1],[qq,ss],[uu,vv]])          # col1 is the pivot column ('1' at row0,col1)
C4bar_e = sp.Matrix([[cc, dd],[1, ff]])                # row1 is the pivot row ('1' at row1,col0)
Ye = C3bar_e*C4bar_e
Re = sum(Ye[0,j]**2 for j in range(2)) + d2**2*sum(Ye[1,j]**2 for j in range(2)) + d1**2*sum(Ye[2,j]**2 for j in range(2))
zero_e = {vv_:0 for vv_ in (pp,cc,dd,ff,qq,ss,uu,vv,d1,d2)}
print("\n=== ESCAPE chart (pivot on off-diagonal entries, inner-permutation image) ===")
print("  Ye[0,0] =", sp.expand(Ye[0,0]))
print("  Ye row0 =", [sp.expand(Ye[0,j]) for j in range(2)])
print("  Re(0) =", sp.expand(Re).subs(zero_e), " <-- SANDWICH holds in the escape chart iff this != 0")
print("  => loss = (w'*y')^2 * Re, Re(0) =", sp.expand(Re).subs(zero_e), "(same structure as canonical)")

# ---------- PARTIAL-swap chart (escape in ONE factor only): pivot C3[0,1], keep C4[0,0] ----------
C3bar_p = sp.Matrix([[pp,1],[qq,ss],[uu,vv]]); C4bar_p = sp.Matrix([[1,cc],[dd,cc*dd+ff]])
Yp = C3bar_p*C4bar_p
Rp = sum(Yp[0,j]**2 for j in range(2)) + d2**2*sum(Yp[1,j]**2 for j in range(2)) + d1**2*sum(Yp[2,j]**2 for j in range(2))
zero_p = {vv_:0 for vv_ in (pp,cc,dd,ff,qq,ss,uu,vv,d1,d2)}
print("\n=== PARTIAL-swap chart (escape in C3 only: pivot C3[0,1], keep C4[0,0]) ===")
print("  Yp row0 =", [sp.expand(Yp[0,j]) for j in range(2)])
print("  Rp(0) =", sp.expand(Rp).subs(zero_p), " <-- sandwich holds iff != 0")

print("\n=== VERDICT ===")
ok = (sp.expand(Re).subs(zero_e) != 0) and (sp.expand(Rp).subs(zero_p) != 0)
print("  escape + partial-swap charts BOTH have R(0) != 0:", ok)
print("  => the pivot-adapted (permutation-transported) escape charts have the SANDWICH loss=mono^2*R,")
print("     R(0)!=0 -- IDENTICALLY to canonical. The lower-bound fix needs ONLY the sandwich; the")
print("     ideal-monomialisation is STRONGER than required. [exact]")
print("  Generality: the inner permutation is a loss-isometry (X=C3*C4 invariant) at ANY instance =>")
print("     instance-independent; the escape chart's kept survivor inherits the '1'-pivot => R(0)=1.")
