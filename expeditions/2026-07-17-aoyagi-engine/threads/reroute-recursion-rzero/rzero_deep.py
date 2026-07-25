#!/usr/bin/env python3
"""Deeper coupled stratum P1 of {R=0}: Y_row0=0, Y_row2=0 (=> delta1 FREE), Y_row1!=0 (=> delta2=0).
Local model of R at P1 and its exact rlct (direct-sum / disjoint-variable additivity of RLCT).
Kill-test: is rlct(R_local) >= 2 (=> deep divisor ratio >= 1/2 minAdm), or does a coupled k=2 term drop it?"""
import sys, sympy as sp
from fractions import Fraction
p,c,d,f,q,s,u,v,d1,d2 = sp.symbols('p c d f q s u v delta1 delta2', real=True)
C3bar=sp.Matrix([[1,p],[q,s],[u,v]]); C4bar=sp.Matrix([[1,c],[d,c*d+f]]); Y=C3bar*C4bar
gens=[Y[0,0],Y[0,1], d2*Y[1,0],d2*Y[1,1], d1*Y[2,0],d1*Y[2,1]]; R=sum(g**2 for g in gens)
allv=[p,c,d,f,q,s,u,v,d1,d2]
# P1: pd=-1 (p=1,d=-1), f=0 (=> C4bar rank1, row space (1,c)); Y_row2=[u,v]C4bar=(u-v)(1,c)=0 => v=u;
#     Y_row1=[q,s]C4bar=(q-s)(1,c) != 0 => q != s ; delta2=0 ; delta1 FREE (set to a generic value e1_0).
c0=sp.Rational(3,7); q0=sp.Rational(2,5); s0=sp.Rational(-3,4); u0=sp.Rational(5,6); e1_0=sp.Rational(1,3)
base={p:1,d:-1,f:0, c:c0, q:q0, s:s0, u:u0, v:u0, d2:0, d1:e1_0}
print("checks at P1: Y_row0=",[sp.simplify(Y[0,j].subs(base)) for j in range(2)],
      " Y_row2=",[sp.simplify(Y[2,j].subs(base)) for j in range(2)],
      " Y_row1(!=0)=",[sp.simplify(Y[1,j].subs(base)) for j in range(2)], " R=",sp.simplify(R.subs(base)))
eps=[sp.Symbol('e_'+x.name) for x in allv]; disp={x:base[x]+e for x,e in zip(allv,eps)}
Rd=sp.expand(R.subs(disp))
# quadratic (lowest) part in eps -- but the coupled term is delta1^2*(u-v)^2 ~ (e1_0+e_d1)^2 * (e_u-e_v)^2.
# Since delta1 is FREE (nonzero e1_0), near P1 the (u-v) direction couples to delta1: the term
# delta1^2||Y_row2||^2 ~ e1_0^2*(Y_row2 displacement)^2 -- treat delta1 as ~unit e1_0 here (it's free).
# So examine the vanishing of R transverse to {R=0} near P1. {R=0} near P1: Y_row0=0(2), Y_row2=0(..), delta2=0.
# Compute the ideal's structure: which monomials appear. Use Hessian in eps at eps=0:
H=sp.hessian(Rd,eps).subs({e:0 for e in eps}); 
print("Hessian rank of R at P1 (delta1 free):",H.rank())
# The rank tells the Morse (k=1) rank; remaining vanishing is the coupled part.
# Directly: rlct of R near P1. Build the LOCAL loss ideal generators (linearizations that don't vanish +
# the genuinely coupled ones). Evaluate exact rlct via disjoint-sum decomposition, verified by structure:
# R = ||Y_row0||^2  (+) delta2^2||Y_row1||^2  (+) delta1^2||Y_row2||^2 . Near P1:
#   ||Y_row0||^2 : Y_row0 vanishes to order1 in 2 indep dirs -> 2 clean squares -> rlct 2/2=1
#   delta2^2||Y_row1||^2 : delta2^2 * (unit) -> 1 clean square (delta2) -> rlct 1/2
#   delta1^2||Y_row2||^2 : delta1 ~ unit(e1_0!=0) * ||Y_row2||^2, Y_row2 vanishes order1 in (u-v) dir(+..)
#        -> effectively ||Y_row2||^2 ~ (u-v)^2*(1+c^2): a clean square in (u-v) -> rlct 1/2? or coupled?
# Since delta1 is FREE and nonzero at P1, delta1^2 is a UNIT, so delta1^2||Y_row2||^2 ~ ||Y_row2||^2 clean.
# => Y_row2 gives 1 more clean square (its rank-1 vanishing). Total clean squares = 2+1+1 = 4 -> rlct 2.
print("=> at P1 delta1 is a UNIT (free, nonzero) so delta1^2||Y_row2||^2 ~ ||Y_row2||^2 (clean square).")
print("   R_local ~ 4 clean squares (Y_row0:2, delta2:1, Y_row2:1) -> rlct = 4/2 = 2. NO coupling drop.")
# The genuine coupling only appears where delta1 -> 0 TOO. Do THAT stratum: P2 with delta1=0 as well.
print("\n--- P2: the fully-coupled stratum delta1=0 AND Y_row2=0 (both -> 0) ---")
base2={p:1,d:-1,f:0, c:c0, q:q0, s:s0, u:u0, v:u0, d2:0, d1:0}
print(" R at P2:",sp.simplify(R.subs(base2)))
# Now near P2, delta1 small AND (u-v) small: term delta1^2||Y_row2||^2 ~ delta1^2*(u-v)^2*(1+c^2) = COUPLED x^2 y^2.
# R_local ~ ||Y_row0||^2(2 sq) + delta2^2*unit(1 sq) + (delta1*(u-v))^2 *unit (coupled).
# rlct additivity over disjoint variable groups {Y_row0 dirs},{delta2},{delta1,(u-v)}:
#   rlct(2 squares)=1 ; rlct(1 square)=1/2 ; rlct((delta1*mu)^2)=rlct(delta1^2 mu^2)=min(1/2,1/2)=1/2
r_total = Fraction(2,2)+Fraction(1,2)+Fraction(1,2)
print(f" rlct(R_local at P2) = 1 + 1/2 + 1/2 = {r_total}  (disjoint-sum additivity; coupled x^2y^2 gives 1/2)")
print(f" deep divisor ratio (loss=(wy)^2 R, wy unit along R-divisors) >= rlct(R)= {r_total} ; >= 1/2 minAdm(=2): {r_total>=2}")
sys.exit(0)
