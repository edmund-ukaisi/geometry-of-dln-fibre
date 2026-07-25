#!/usr/bin/env python3
"""TUBE-COVER PROBE #169, step 1: distinguish the SINGLE pivot-quotient unit (1+pd)
from the FULL residual R (sum of squares) at the (3,3,3,2,2) t=(2,2,1,0) leaf.

Faithful residual from threads/28-twoblock-diagb + g-coupled-33322-separated.py:
  C3bar=[[1,p],[q,s],[u,v]] (3x2, radial w),  C4bar=[[1,c],[d,c*d+f]] (2x2, radial y),
  Y = C3bar*C4bar (3x2),  residual ideal = <Y_row1, d2*Y_row2, d1*Y_row3>,
  loss = (w*y)^2 * R,  R = ||Y_row1||^2 + d2^2 ||Y_row2||^2 + d1^2 ||Y_row3||^2, R(0)=1.

KEY DISTINCTION UNDER TEST:
 - pivot-quotient unit u = Y[0,0] = 1+pd. {u=0} is CODIM 1.
 - full residual R. {R=0} is what the RLCT LOWER BOUND actually needs bounded below.
Hypothesis: {R=0} is HIGH codim (the kept-row "1"s prevent simultaneous vanishing),
so the codim-1 tube {u~0} is largely LOSS-REGULAR (a red herring for the lower bound).
"""
import sympy as sp

p,c,d,f,q,s,u,v,d1,d2,w,y = sp.symbols('p c d f q s u v delta1 delta2 w y', real=True)
C3bar = sp.Matrix([[1,p],[q,s],[u,v]])
C4bar = sp.Matrix([[1,c],[d,c*d+f]])
Y = C3bar*C4bar
print("Y =")
sp.pprint(sp.expand(Y))

unit = sp.expand(Y[0,0])                       # = 1+pd
R = sum(Y[0,j]**2 for j in range(2)) \
  + d2**2*sum(Y[1,j]**2 for j in range(2)) \
  + d1**2*sum(Y[2,j]**2 for j in range(2))
R = sp.expand(R)
print("\npivot-quotient unit Y[0,0] =", unit, "  {u=0} is codim 1")
print("R(0) =", R.subs({v_:0 for v_ in (p,c,d,f,q,s,u,v,d1,d2)}), " (kept-row '1' => R is a unit at origin)")

# ---- (1) Is {R=0} nonempty in the chart, and what codim? ----
# R = 0 (real, sum of squares) <=> every summand = 0:
#   Y[0,0]=Y[0,1]=0 ; d2*Y[1,0]=d2*Y[1,1]=0 ; d1*Y[2,0]=d1*Y[2,1]=0.
print("\n=== {R=0} structure (real: each square =0) ===")
gens_R = [Y[0,0], Y[0,1], d2*Y[1,0], d2*Y[1,1], d1*Y[2,0], d1*Y[2,1]]
print("R=0  <=>  all of:", [sp.expand(g) for g in gens_R])

# GENERIC couplings d1,d2 != 0: forces Y = 0 (whole 3x2 matrix).
# Y=0 with C3bar[0,:]=[1,p] (rank>=1, indeed C3bar injective as 2->3 generically) => C4bar=0,
# contradicting C4bar[0,0]=1.  So {R=0} EMPTY for generic d1,d2.
# Verify: solve Y=0.
solY = sp.solve([Y[i,j] for i in range(3) for j in range(2)], [p,c,d,f,q,s,u,v], dict=True)
print("solve(Y==0 as matrix) over the chart affine coords:", solY, " (empty => Y never 0 here)")

# ---- (2) Codim of {R=0} in the degenerate slices ----
# d1=d2=0 slice: R = Y[0,0]^2+Y[0,1]^2. {R=0} = {1+pd=0, c+p(cd+f)=0}.
print("\n=== d1=d2=0 slice: R = Y[0,0]^2 + Y[0,1]^2 ===")
R00 = sp.expand(Y[0,0]**2+Y[0,1]**2)
# on 1+pd=0 => d=-1/p ; then Y[0,1]=c+p(cd+f)= c + p(c(-1/p)+f)= c - c + p f = p f
Y01_on = sp.simplify(Y[0,1].subs(d, -1/p))
print("Y[0,1] on {d=-1/p} =", Y01_on, " => =0 needs p*f=0; but 1+pd=0 needs p!=0 => f=0.")
print("  {R=0, d1=d2=0} = {pd=-1, f=0}: codim 2 in this slice (+d1=d2=0 => codim 4 overall).")

# ---- (3) THE DECISIVE CHECK: on the codim-1 tube {u=1+pd ~ 0}, is the loss REGULAR? ----
# loss = (w*y)^2 * R. On {1+pd=0} minus {R=0}, R>0, so loss singular only where w*y=0.
# Take a GENERIC point on {1+pd=0}: does R stay bounded below? Evaluate R on a slice of {1+pd=0}.
print("\n=== on the tube {1+pd=0}: is R bounded below (=> loss-regular away from w*y=0)? ===")
import random
random.seed(1)
mins=[]
for _ in range(6):
    # random point with 1+pd=0: pick p!=0, set d=-1/p, others random small
    pv=random.uniform(0.3,1.5); dv=-1.0/pv
    sub={p:pv,d:dv,c:random.uniform(-0.5,0.5),f:random.uniform(-0.5,0.5),
         q:random.uniform(-0.5,0.5),s:random.uniform(-0.5,0.5),
         u:random.uniform(-0.5,0.5),v:random.uniform(-0.5,0.5),
         d1:random.uniform(-0.5,0.5),d2:random.uniform(-0.5,0.5)}
    Rval=float(R.subs(sub))
    mins.append(Rval)
    print(f"  1+pd=0 pt (p={pv:.2f},d={dv:.2f}): R = {Rval:.4f}  (loss/(wy)^2)")
print(f"  min R on sampled tube = {min(mins):.4f}  (>0 => tube is loss-regular where wy!=0)")
