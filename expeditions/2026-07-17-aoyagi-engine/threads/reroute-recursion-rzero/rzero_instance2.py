#!/usr/bin/env python3
"""FIXED generic point of {R=0}. On the leaf, {R=0} (all 6 gens=0) with generic q,s,u,v:
Y_row1,Y_row2 !=0  =>  forces delta1=delta2=0 AND Y_row0=0 (=> 1+pd=0, f=0). codim 4.
Near it R ~ ||Y_row0||^2 + d1^2||Y_row2||^2 + d2^2||Y_row1||^2 = 4 independent squares (Morse rank 4)."""
import sys, sympy as sp
from fractions import Fraction
p,c,d,f,q,s,u,v,d1,d2 = sp.symbols('p c d f q s u v delta1 delta2', real=True)
C3bar = sp.Matrix([[1,p],[q,s],[u,v]]); C4bar = sp.Matrix([[1,c],[d,c*d+f]])
Y = C3bar*C4bar
gens=[Y[0,0],Y[0,1], d2*Y[1,0],d2*Y[1,1], d1*Y[2,0],d1*Y[2,1]]
R=sum(g**2 for g in gens); allv=[p,c,d,f,q,s,u,v,d1,d2]
# generic base point on {R=0}: 1+pd=0 (p=1,d=-1), f=0, delta1=delta2=0, GENERIC c,q,s,u,v
base = {p:sp.Rational(1), d:sp.Rational(-1), f:0, d1:0, d2:0,
        c:sp.Rational(3,7), q:sp.Rational(2,5), s:sp.Rational(-3,4), u:sp.Rational(5,6), v:sp.Rational(-1,2)}
print("Y_row1,Y_row2 at base (should be nonzero):",
      [sp.simplify(Y[1,j].subs(base)) for j in range(2)], [sp.simplify(Y[2,j].subs(base)) for j in range(2)])
print("R at base (==0):", sp.simplify(R.subs(base)))
eps=[sp.Symbol('e_'+x.name) for x in allv]
disp={x: base[x]+e for x,e in zip(allv,eps)}
R_disp=sp.expand(R.subs(disp))
R_lin=sum(sp.diff(R_disp,e).subs({ee:0 for ee in eps})*e for e in eps)
H=sp.hessian(R_disp,eps).subs({ee:0 for ee in eps}); r=H.rank()
print("linear part at base (==0 => min):", sp.simplify(R_lin))
print(f"Hessian rank (Morse rank = codim of {{R=0}}) = {r}")
ratio=Fraction(r-1+1,2); print(f"blow up codim-{r} Morse {{R=0}}: k=1, h={r-1}, DEEP RATIO=(h+1)/2 = {ratio}")
print(f"1/2 minAdm = 2 ; deep ratio >= 1/2 minAdm: {ratio>=2} ; EQUAL: {ratio==2}")

# Cross-check codim{R=0} globally via the vanishing ideal's generic Jacobian rank at base:
J=sp.Matrix([[sp.diff(g,x) for x in allv] for g in gens]).subs(base)
print(f"generic Jacobian rank of the 6 residual gens at base = {J.rank()}  (=> codim {{R=0}} = {J.rank()})")
sys.exit(0)
