#!/usr/bin/env python3
"""B1 #170 -- tie probe4 (shear-outermost det=monomial) to probe5 (matched R(0)=1): does the
matched escape chart (blow-up on the off-diagonal pivot pair, shear/normalization ADAPTED to it)
give BOTH  det Dg = coordinate monomial  AND  loss = monomial^2 * R with R(0)!=0 (the SANDWICH)?
in ONE computation, exact (sympy). Residual (3,3,3,2,2): loss = ||[X_r0, d2 X_r1, d1 X_r2]||^2, X=C3*C4.
"""
import sympy as sp

# ESCAPE chart = blow-up with the MATCHED off-diagonal pivot pair (C3[0,1], C4[1,0]) = radials A,B;
# normalization ADAPTED (the '1' sits at the pivot slot) -- the shear-outermost / permutation-transported chart.
A,B,pp,qq,ss,uu,vv,cc,dd,ff,d1,d2 = sp.symbols('A B p1 q1 s1 u1 v1 c1 d1r f1 delta1 delta2', real=True)
# C3 = A * [[p',1],[q',s'],[u',v']]   (pivot C3[0,1]=A)
C3 = A*sp.Matrix([[pp,1],[qq,ss],[uu,vv]])
# C4 = B * [[c',d'],[1,f']]           (pivot C4[1,0]=B)
C4 = B*sp.Matrix([[cc,dd],[1,ff]])
X = C3*C4
# residual generators (weighted) and loss
gens = [X[0,0],X[0,1], d2*X[1,0],d2*X[1,1], d1*X[2,0],d1*X[2,1]]
loss = sum(g**2 for g in gens)

# --- factor loss = (A*B)^2 * R and check R(0) ---
R = sp.simplify(loss/(A*B)**2)
zero = {v:0 for v in (pp,qq,ss,uu,vv,cc,dd,ff,d1,d2)}
R0 = sp.expand(R).subs(zero)
print("=== matched escape chart: loss = (A*B)^2 * R ===")
print("  X[0,0]/(A*B) =", sp.expand(X[0,0]/(A*B)), " (kept survivor: p1*c1 + 1 -> 1 at origin)")
print("  R(0) =", R0, "  => SANDWICH loss=(A*B)^2*R, R(0)!=0 :", R0!=0)

# --- Jacobian det of the chart map (source (A,B,p',..,f') -> C3,C4 entries) = coordinate monomial? ---
src = [A,pp,qq,ss,uu,vv, B,cc,dd,ff]
tgt = [C3[0,0],C3[0,1],C3[1,0],C3[1,1],C3[2,0],C3[2,1], C4[0,0],C4[0,1],C4[1,0],C4[1,1]]
Jdet = sp.factor(sp.Matrix([[sp.diff(t,s) for s in src] for t in tgt]).det())
fa = Jdet.as_ordered_factors()
coordmono = all((f.is_Number or f.is_Symbol or (f.is_Pow and f.args[0].is_Symbol)) for f in fa)
print("\n=== chart Jacobian det ===")
print("  det Dg =", Jdet, "  coordinate-monomial:", coordmono, "(= A^? * B^?, the blow-up radials)")

print("\n=== VERDICT ===")
print("  matched escape chart has BOTH det Dg = coordinate monomial AND loss = monomial^2 * R, R(0)=1")
print("  => it is a VALID SANDWICH chart. The B1 fix needs ONLY the sandwich; the shear-outermost /")
print("     pivot-adapted (matched) order supplies both det-monomial (probe4) and R(0)!=0 (here).")
print("  The shear is a unipotent bijection fixing the origin with D(shear)(0)=I, so applying it last")
print("  cannot destroy R(0) (a value-at-0 of the kept survivor) -- it only re-monomialises the det.")
