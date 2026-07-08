"""
FLIP probe 1 -- is r1carrier's C7 dense-torus witness RELEVANT to the RLCT resolution?

r1carrier's obstruction (C7): {rank(A_{1,b}.A2) <= 1} has a dense-torus point
Qb* = [[1,1,2,1],[1,1,2,1]] (rank 1, all entries nonzero), invisible to coordinate blow-ups,
so a NON-coordinate (determinantal) center is forced to principalise det(Qb Qb^T).

But the RLCT of the DLN loss ||prod C||^2 is the LOCAL rlct at the DEEPEST point (origin, all C=0),
resolving the loss ZERO locus {prod C = 0} near 0 (Aoyagi Thm 4 domination).  det(Qb Qb^T) only
appears in the MEASURE-ATOM route (integrate the corank block Gamma OUT over full space -> Gram CoV
Gamma |-> Gamma.Qb, Jacobian det(Qb Qb^T)^{-p/2}).  Aoyagi's PUBLISHED recursion never forms it.

DECISIVE CHECK: is the C7 witness a SINGULARITY of the loss (prod C = 0), or a positive-loss point?
If positive-loss, the resolution (which resolves {prod C = 0} only) NEVER touches it -> C7 irrelevant.
"""
import sympy as sp
from itertools import combinations

print("="*80)
print("F1 : is the corank-residual loss  ||C.Qtilde + Gamma.Qb||^2  ZERO at the C7 witness?")
print("="*80)
# The corank residual after the front peel (corank-2): Gamma free 2x2, Qb = 2x4 product tail,
# C.Qtilde a fixed cross-term (C = non-pivot rows of the front layer times deeper).
# r1carrier's C7 witness is Qb* rank 1 all-nonzero.  Take a GENERIC nonzero cross term CQ.
Qb_star = sp.Matrix([[1,1,2,1],[1,1,2,1]])   # rank 1, dense torus (all entries nonzero)
print("Qb* =", Qb_star.tolist(), " rank =", Qb_star.rank())
# row space of Qb* is span{[1,1,2,1]} (1-dim).  Gamma.Qb* has BOTH rows in row-space(Qb*).
Gam = sp.Matrix(2,2, sp.symbols('g0:4', real=True))
GQ = sp.expand(Gam*Qb_star)
print("Gamma.Qb* =", GQ.tolist(), " (each row is a multiple of [1,1,2,1])")
# Generic cross term CQ (rows NOT in row-space(Qb*)):
CQ = sp.Matrix([[0,1,0,0],[0,0,0,1]])         # generic: rows not proportional to [1,1,2,1]
loss = sp.expand(sum((CQ+GQ)[i,j]**2 for i in range(2) for j in range(4)))
# Can loss = 0 for some Gamma?  Solve CQ + Gamma.Qb* = 0 i.e. Gamma.Qb* = -CQ.
sols = sp.solve([ (CQ+GQ)[i,j] for i in range(2) for j in range(4)], list(Gam), dict=True)
print("solve  C.Qtilde + Gamma.Qb* = 0  for Gamma:", sols, " (empty => loss > 0 for ALL Gamma)")
# minimise loss over Gamma (least squares): if min > 0, the witness is a POSITIVE-loss point.
grad = [sp.diff(loss, g) for g in Gam]
crit = sp.solve(grad, list(Gam), dict=True)
print("critical Gamma (least-squares):", crit)
if crit:
    lmin = sp.simplify(loss.subs(crit[0]))
    print("MIN loss over Gamma at the C7 witness =", lmin,
          " => witness is a", "POSITIVE-LOSS (smooth) point" if lmin!=0 else "singularity")

print()
print("="*80)
print("F2 : the loss SINGULARITY locus {prod C = 0} vs the product-rank-drop {rank(prod)<=k}")
print("="*80)
print("The DLN loss is ||prod C||^2; its zero locus is {prod C = 0} = {rank(prod)=0}.")
print("The C7 witness has prod tail Qb* of RANK 1 (not 0) with ALL entries nonzero: prod != 0 there,")
print("so ||.||^2 > 0 -- a SMOOTH point of the loss, NOT on the singularity {prod=0}.")
print("Aoyagi Thm 4: rlct = local rlct at the DEEPEST point (origin, all C=0), resolving {prod C=0}.")
print("=> the determinantal locus {rank Qb <= 1} (which carries C7) is a POSITIVE-loss locus the")
print("   resolution of {prod C = 0} never needs to touch.  det(Qb Qb^T) is an ATOM-ROUTE object only.")

print()
print("="*80)
print("F3 : matrix-level box cutoff -- pure-vs-atom-adj scalar result at the ACTUAL corank-2 widths")
print("="*80)
print(" (does the BOX Gamma-integral stay finite as Qb -> rank-1, given a positive core?)")
# Box Gamma-integral of the corank residual, with a positive core c0>0 (the pivot Morse energy):
# I(Qb) = int_{Gamma in box} (c0 + ||Gamma.Qb||^2)^{-c'} dGamma.
# The atom (full-space, NO core) gives det(Qb Qb^T)^{-p/2} -> divergent on {rank Qb<=1}.
# The box integral WITH the core c0>0 is bounded by c0^{-c'} * vol(box) -- FINITE for ALL Qb, incl. rank-1.
import numpy as np
def box_gamma_integral(Qb, c0, cprime, N=60, R=1.0):
    # crude midpoint quadrature of int_{[-R,R]^4} (c0 + ||Gamma Qb||^2)^{-c'} dGamma, Gamma 2x2
    xs = (np.arange(N)+0.5)/N*2*R - R
    dv = (2*R/N)**4
    Qb = np.array(Qb, float)
    tot = 0.0
    for a in xs:
      for b in xs:
        for c in xs:
          for d in xs:
            G = np.array([[a,b],[c,d]])
            v = c0 + np.sum((G@Qb)**2)
            tot += v**(-cprime)
    return tot*dv
Qb_full = np.array([[1,0,0,0],[0,1,0,0]], float)   # rank 2
Qb_rk1  = np.array([[1,1,2,1],[1,1,2,1]], float)    # rank 1 (C7 witness)
for cp in [0.9, 1.5, 1.9]:
    Ifull = box_gamma_integral(Qb_full, c0=1.0, cprime=cp, N=40)
    Irk1  = box_gamma_integral(Qb_rk1 , c0=1.0, cprime=cp, N=40)
    print(f"  c'={cp}: box-Gamma-integral  full-rank Qb = {Ifull:.4f}   rank-1 Qb = {Irk1:.4f}"
          f"   (both FINITE with core c0=1 -- NUMERIC guide only, not a certificate)")
print("  -> WITH a positive core the box integral is trivially <= c0^{-c'}*vol(box) < inf for EVERY Qb.")
print("     The atom's det(Qb Qb^T)^{-p/2} divergence needs the core ABSENT (full-space, no cutoff).")
print("     [numeric is a GUIDE; the exact statement: box <= c0^{-c'} vol(box) is an exact bound.]")
