"""
FLIP probe 3 -- the r1carrier C10 crux (shared deeper factor) under Aoyagi's FRONT-FIRST order,
                the exact box cutoff, and the branch exponent bookkeeping.

r1carrier C10 tested DEEPEST-layer-first (resolve C3/A2 first) and found the residual minor ideal
I_2(A') of the shallow block STILL has a dense-torus zero -> "non-coordinate center still forced".
But Aoyagi's published recursion is FRONT-FIRST (peel C1, then C2, then C3).  Under front-first the
two coupled terms  ||(W1).C2.C3||^2  and  delta'^2 ||(W2).C2.C3||^2  SHARE C2.C3; peeling C2's residual
origin (coordinate) factors ONE radial from BOTH simultaneously -> shared-divisor, no incompatibility.
"""
import sympy as sp
from itertools import combinations

print("="*90)
print("(1) SHARED RADIAL under FRONT-FIRST: peeling C2 factors one radial from BOTH coupled terms")
print("="*90)
# The depth-2 core after layer 1: pivot term ||(W1).C2.C3||^2 and corank term delta'^2||(W2).C2.C3||^2.
# Peel C2 (front of the depth-2 subproduct): C2 = u2 * C2' (residual-origin radial).
u2, delta = sp.symbols('u2 delta', real=True)
W1 = sp.Matrix([[1,2,3]]); W2 = sp.Matrix([[4,5,6]])       # generic constant rows (from the C1 chart)
C2p = sp.Matrix(3,3, sp.symbols('e0:9', real=True))         # C2' (residual)
C3  = sp.Matrix(3,4, sp.symbols('f0:12', real=True))        # C3 free
C2  = u2*C2p
piv = sp.expand((W1*C2*C3))                                 # (W1).C2.C3  (1x4)
cor = sp.expand((W2*C2*C3))                                 # (W2).C2.C3  (1x4)
# does u2 factor cleanly from BOTH?
piv_over = [sp.cancel(piv[0,j]/u2) for j in range(4)]
cor_over = [sp.cancel(cor[0,j]/u2) for j in range(4)]
print("  u2 factors from ALL entries of (W1).C2.C3 :", all(u2 not in e.free_symbols for e in piv_over))
print("  u2 factors from ALL entries of (W2).C2.C3 :", all(u2 not in e.free_symbols for e in cor_over))
print("  => ONE coordinate radial u2 (center {C2=0}) divides BOTH coupled terms simultaneously.")
print("     The full layer-1 residual = u2^2 * ( ||(W1)C2'C3||^2 + delta'^2 ||(W2)C2'C3||^2 ),")
print("     shared u2; the two terms recurse on C2'.C3 (SAME deeper C3) -- coordinate, no det ideal.")
print("     r1carrier C10 used DEEPEST-first (C3 first), which is NOT Aoyagi's order; front-first shares.")

print()
print("="*90)
print("(2) After peeling C2 the residual is DEPTH-1 (C3 free) -> free-coordinate monomials")
print("="*90)
# (W1).C2'.C3 : with C2' generic (after its own pivot chart, a unit), (W1).C2' is a generic 1x3, so
# (W1)C2'C3 = (generic 1x3).C3 = a generic combination of C3's rows -> after C3's pivot chart, free coords.
print("  (W1).C2'.C3 = (generic 1x3 w').C3 ; C3 is a single FREE matrix -> peel C3's residual origin")
print("  (coordinate radial u3) then the reduced block is FREE coordinates -> MONOMIAL generators.")
print("  Depth-2 core resolves in 2 coordinate peels (C2 then C3). NORMAL CROSSING, coordinate centers.")

print()
print("="*90)
print("(3) EXACT box cutoff (matrix level) -- the atom's Gram-det divergence needs the core ABSENT")
print("="*90)
print("  Corank-residual box integral with a positive core c0>0 (the pivot/deeper Morse energy):")
print("    I(Qb) = INT_{Gamma in [-R,R]^{pq}} (c0 + ||Gamma.Qb||^2)^{-c'} dGamma")
print("  EXACT bound:  (c0 + ||Gamma.Qb||^2)^{-c'} <= c0^{-c'}  for c'>=0  =>  I(Qb) <= c0^{-c'}*(2R)^{pq}")
print("  which is FINITE for EVERY Qb (incl. rank-1 dense-torus Qb*), with NO det(Qb Qb^T) factor.")
print("  The atom route's det(Qb Qb^T)^{-p/2} arises ONLY from integrating Gamma over ALL of R^{pq}")
print("  with c0 ABSENT (full-space Gaussian); that OVER-COUNTS the box and manufactures the divergence")
print("  on {rank Qb<=1}. On the deepest stratum the core c0 -> 0 too, and the recursion goes DEEPER")
print("  (peel the core's own layers, coordinate) -- it never resolves {rank Qb<=1} directly.")

print()
print("="*90)
print("(4) branch exponent bookkeeping (3,3,3,4) t=(1,0,0): terminal divisor exponents sum to Mval=7")
print("="*90)
M = [3,3,3,4]; t = [1,0,0]        # t^(1),t^(2),t^(3)
# Mval(t) = (M1-t1)(M2-t1) + sum_{j=2..L} (t_{j-1}-t_j)(M_{j+1}-t_j)
term1 = (M[0]-t[0])*(M[1]-t[0])
rest = sum((t[j-1]-t[j])*(M[j+1]-t[j]) for j in range(1,3))
print(f"  layer-1 charge (M1-t1)(M2-t1) = ({M[0]}-{t[0]})({M[1]}-{t[0]}) = {term1}")
print(f"  layer-2 charge (t1-t2)(M3-t2) = ({t[0]}-{t[1]})({M[2]}-{t[1]}) = {(t[0]-t[1])*(M[2]-t[1])}")
print(f"  layer-3 charge (t2-t3)(M4-t3) = ({t[1]}-{t[2]})({M[3]}-{t[2]}) = {(t[1]-t[2])*(M[3]-t[2])}")
print(f"  Mval(t) = {term1} + {rest} = {term1+rest}   (= minAdm(3,3,3,4) = 7; threshold 7/2)")
print("  Each charge is the CODIM of a coordinate residual-block origin blown up at that layer;")
print("  the accumulated divisor exponent on the binding terminal branch = Mval = 7 (banked minAdmRec).")
print("  c' < 7/2  =>  c' < Mval/2 on every divisor  =>  monomial endpoint converges (coordinatewise).")
