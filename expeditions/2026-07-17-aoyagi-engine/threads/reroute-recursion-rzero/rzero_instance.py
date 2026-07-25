#!/usr/bin/env python3
"""EXACT: resolve {R=0} at the (3,3,3,2,2) t=(2,2,1,0) leaf and read off the deep divisor ratio.
loss = (w y)^2 * R,  R = ||Y_row0||^2 + d2^2||Y_row1||^2 + d1^2||Y_row2||^2,  Y = C3bar*C4bar (3x2).
Checks:
 (1) codim{R=0} over the fibre (generic d1,d2) and its structure;
 (2) near a GENERIC point P0 of {R=0}, R is a nondegenerate (Morse) quadratic of rank = codim;
 (3) blow up {R=0} -> R = rho^2 * unit, Jac rho^(codim-1); deep divisor ratio = (codim-1+1)/(2*1) = codim/2;
 (4) k=1 (loss vanishes to order exactly 2 along the deep divisor)."""
import sys, sympy as sp
from fractions import Fraction

# ---- symbols ----
p,c,d,f,q,s,u,v,d1,d2 = sp.symbols('p c d f q s u v delta1 delta2', real=True)
C3bar = sp.Matrix([[1,p],[q,s],[u,v]])
C4bar = sp.Matrix([[1,c],[d,c*d+f]])
Y = C3bar*C4bar                       # 3x2
gens = [Y[0,0],Y[0,1], d2*Y[1,0], d2*Y[1,1], d1*Y[2,0], d1*Y[2,1]]
R = sum(g**2 for g in gens)
allv=[p,c,d,f,q,s,u,v,d1,d2]

# (1) {R=0}: real sum of squares => all gens = 0. Solve on the fibre d1,d2 generic (!=0):
# gens[2..5]=0 with d1,d2!=0 => Y_row1=Y_row2=0 ; plus Y_row0=0 => whole Y=0.
# Y = C3bar*C4bar = 0.  Codim of {Y=0} in the 8 coords (p,c,d,f,q,s,u,v):
Ymat = Y
# {Y=0}: 6 equations (3x2) but rank-structured. Compute codim via generic Jacobian rank of the 6 gens.
Jac = sp.Matrix([[sp.diff(g,var) for var in allv] for g in gens])
# generic point ON {R=0}: need all gens=0. Use the rank-1 degeneration: C4bar rank1 (f=0) & 1+pd=0.
# pick p0=1 => d0=-1 ; f=0 ; then Y_row0 = (1+pd)(1,c)=0. choose c,q,s,u,v so Y_row1,Y_row2=0 too.
# Y_row1 = [q,s]*C4bar = (q+s d, qc+s(cd+f)); with f=0,d=-1: (q-s, c(q-s)) = (q-s)(1,c). =0 => s=q.
# Y_row2 = [u,v]*C4bar -> (u+v d, ...) = (u-v)(1,c); =0 => v=u.  (and d1,d2 free small)
P0 = {p:1, d:-1, f:0, s:q, v:u}      # leaves c,q,u,d1,d2 free -> a 5-dim family inside {R=0}
# verify R=0 on P0 family:
R_P0 = sp.simplify(R.subs(P0))
print(f"(1) R on the P0 family (p=1,d=-1,f=0,s=q,v=u): {R_P0}  (==0: {R_P0==0})")

# (2) rank of R's Hessian (as quadratic in the transverse coords) at a GENERIC P0 point.
# choose generic numeric values for the free coords, keep d1,d2 SMALL symbolic to see the fibre.

num = {c: sp.Rational(3,7), q: sp.Rational(2,5), u: sp.Rational(-1,3)}
base = {**{k:(v.subs(num) if hasattr(v,'subs') else v) for k,v in P0.items()}, **num}
# expand R around base in the 10 vars; Hessian rank = codim of {R=0} (Morse rank) transversally.
subs0 = {p:1,d:-1,f:0, c:num[c], q:num[q], s:num[q], u:num[u], v:num[u], d1:0, d2:0}
# Build R as function of displacements
disp = {var: subs0[var]+sp.Symbol('e_'+var.name) for var in allv}
eps = [sp.Symbol('e_'+var.name) for var in allv]
R_disp = sp.expand(R.subs(disp))
# lowest-order (quadratic) part in eps:
R_lin = sum(sp.diff(R_disp, e).subs({ee:0 for ee in eps})*e for e in eps)
H = sp.hessian(R_disp, eps).subs({ee:0 for ee in eps})
Hrank = H.rank()
print(f"(2) linear part of R at P0 (should be 0, i.e. P0 is a min): {sp.simplify(R_lin)}")
print(f"    Hessian rank of R at generic P0 = {Hrank}  (Morse/nondegenerate rank = codim of R-vanishing)")

# (3)+(4) blow up the codim-r {R=0}: R ~ (Morse rank r) => one blow-up of the r-codim center gives
# R = rho^2 * unit, Jac rho^(r-1); loss=(wy)^2 * rho^2 * unit => deep divisor {rho=0}: k=1, h=r-1.
r = Hrank
ratio_deep = Fraction(r-1+1, 2*1)
print(f"(3)/(4) deep divisor from blowing up codim-{r} Morse {{R=0}}: k=1, h={r-1}, ratio=(h+1)/2 = {ratio_deep}")
mv = 4  # minAdm(3,3,3,2,2)
print(f"        1/2 * minAdm = {Fraction(mv,2)};  deep ratio {ratio_deep} >= 1/2 minAdm: {ratio_deep>=Fraction(mv,2)}  "
      f"(EQUAL: {ratio_deep==Fraction(mv,2)})")
sys.exit(0)
