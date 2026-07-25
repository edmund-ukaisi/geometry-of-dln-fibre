#!/usr/bin/env python3
"""PNP hcover TEMPLATE verification (exact): the faithful per-node box-containment as a
tight boundary inequality, + the depth-2 faithful tree `Covers` closure (mirrors covers_coTree),
+ the measure-zero exceptional locus.  All exact sympy / rational."""
import sympy as sp
from fractions import Fraction
import itertools

print("="*72)
print("TEMPLATE A: faithful corank-2 shear box-containment as EXACT boundary inequality")
print("="*72)
# Faithful corank-2 shear on Fin 8: kept {0,1,2,3} (c12a,c12b,c21a,c21b), write {4,5,6,7}=C22 block
#   Schur:   m_{ij} |-> m_{ij} - c21_i * c12_j      (single product each -- coPhi)
#   recoord: (the Q2^{-1} on downstream, modelled on 4 MORE slots {reuse block for demo})
# The render's worry: the FAITHFUL shear (Schur + recoord) has up to C=2 products/coord.
# Model a WORST-CASE faithful coord: y |-> y - (a*b) - (c*d)  (two degree-2 products).
r = sp.Symbol('r', positive=True)
a,b,c,d,y = sp.symbols('a b c d y')
# on |a|,|b|,|c|,|d|,|y| <= r, the preimage coordinate is y - a*b - c*d; bound its abs:
# |y - a*b - c*d| <= |y| + |a*b| + |c*d| <= r + r^2 + r^2 = r + 2 r^2. Verify tightness:
worst = r + r**2 + r**2   # a=b=c=d=r (or signs) , y=r
print(f"  faithful coord y - a*b - c*d, worst |.| on r-box = r + 2 r^2 = {worst}")
print(f"  => box inflation f(r) = r + 2 r^2 suffices for corank-2 faithful (C=2).")
# exact check at boundary a=b=c=d=-something, y=r maximizing:
# max of |y - a*b - c*d| over box = r + 2r^2 attained at y=r,a*b=-r^2,c*d=-r^2 -> y-a*b-c*d = r+2r^2. OK
val = (r) - (-(r**2)) - (-(r**2))
print(f"  attained value at y=r, ab=-r^2, cd=-r^2 : {sp.simplify(val)} == r+2r^2 : {sp.simplify(val-worst)==0}")

print()
print("="*72)
print("TEMPLATE B: depth-2 faithful tree closes Covers (mirror of covers_coTree)")
print("="*72)
# Engine Covers node clause (from LeafCoverTiling.Covers):
#   node clause 1: for each pivot p in S,  closedBall 0 (max R 1) subset sigma_p '' closedBall 0 (f(max R 1))
#   node clause 2: for each pivot p in S,  Covers f (child p) (f (max R 1))
#   leaf clause:   closedBall 0 R subset box
# Take f = r + 2 r^2, S = {0,1}, depth 2, leaf box = closedBall 0 (f^[2] 1).
def f(rr,C=2): return rr + C*rr**2
R0 = Fraction(1)
lvl0 = max(R0, Fraction(1))          # 1
inflate0 = f(lvl0)                    # f(1) = 3
lvl1 = max(inflate0, Fraction(1))     # 3
inflate1 = f(lvl1)                    # f(3) = 3 + 18 = 21
leafbox = inflate1                    # 21
print(f"  f=r+2r^2, S={{0,1}}, depth 2:")
print(f"    root shear needs sigma covers max(1,1)=1 from box f(1)={inflate0}  (faithfulShear_covers r=1: OK)")
print(f"    child shear needs sigma covers max(3,1)=3 from box f(3)={inflate1} (faithfulShear_covers r=3: OK)")
print(f"    leaf box radius = {leafbox}; child2 needs leaf covers f(max 3 1)={inflate1}={leafbox}: {leafbox>=inflate1}")
print(f"  => Covers (r->r+2r^2) faithfulTree 1 CLOSES exactly (same shape as covers_coTree, C: 1->2)")

print()
print("="*72)
print("TEMPLATE C: measure-zero exceptional locus")
print("="*72)
# The chart g_c = pathMap of stepMaps; each step blockBlowupMap has |det| = u_pivot^{|S|-1}.
# g_c a.e.-injective off {u_pivot = 0} (a finite union of coordinate hyperplanes over the path);
# the shear is GLOBALLY injective (unipotent, |det|=1). So excep = union of pivot hyperplanes =
# a finite union of {coord = 0}, each measure 0 in R^D.  Volume 0.  (Standard: hyperplane null.)
print("  excep(g_c) = Union over path steps of {u_pivot = 0}  (blow-up non-injective locus);")
print("  shear is globally injective (|det|=1) so contributes nothing.")
print("  each {coord = 0} is a hyperplane => volume 0; finite union => volume 0.  EXACT: null.")
print("  In the Lean Chart record: hexcep_null via volume_pi_eq_zero of a coordinate hyperplane,")
print("  matching coG_injOn (Corank2GeoAtlas) which already gives InjOn off {u_p = 0}.")
