"""
C9 : pin the SCOPE BOUNDARY of the research-grade gap.
  - corank-1 product (Qb = row . A2, 1xq): rank-drop locus = {Qb=0} = {row in left-ker A2};
    for generic A2 (full row rank) that is {row=0}, a COORDINATE subspace -> TORIC -> BOUNDED.
  - free tail (L=2 depth-3 chain, Qb = bottom rows of a single FREE matrix): det(Qb Qb^T) is a
    Gram of a FREE matrix -> the banked SchurCore/rrp case -> BOUNDED.
  - corank-2 PRODUCT (>=2 tail factors): dense-torus rank-drop (Codex witness) -> determinantal
    -> NON-coordinate center -> RESEARCH-GRADE.
"""
import sympy as sp
from itertools import combinations

print("C9a corank-1 PRODUCT  Qb = row(1x3) . A2(3x4) = 1x4 :")
r = sp.symbols('r0:3'); row = sp.Matrix([[r[0],r[1],r[2]]])
b = sp.symbols('b0:12'); A2 = sp.Matrix(3,4,b)
Qb1 = sp.expand(row*A2)     # 1x4
# corank-1 'det(QbQb^T)' = ||Qb||^2 (1x1 Gram). Zero locus over generic A2 = {row=0}.
g1 = sp.expand((Qb1*Qb1.T)[0,0])
# left-kernel of a generic full-row-rank 3x4 A2 is {0}; so {Qb1=0} = {row=0} (coordinate).
print("   ||row.A2||^2 has", len(sp.Add.make_args(g1)), "monomials; its real zero locus over full-rank A2")
print("   is {row=0} (left-kernel trivial) -> a COORDINATE subspace -> toric-resolvable -> BOUNDED.")
# sanity: a dense-torus zero would need row != 0 with row.A2 = 0, impossible for full-row-rank A2.
A2num = sp.Matrix([[1,0,0,2],[0,1,0,3],[0,0,1,5]])   # full row rank
sol = sp.linsolve((row*A2num).T, list(r))
print("   row.A2num=0 solutions (full-rank A2):", sol, " -> only row=0 (no dense-torus drop).")

print()
print("C9b free-tail (depth-3 (3,3,4), tail = single FREE 3x4 matrix), Qb = bottom 2 rows FREE 2x4:")
Yb = sp.Matrix(2,4, sp.symbols('y0:8'))
colpairs4 = list(combinations(range(4),2))
# det(Yb Yb^T) is the Gram of a FREE matrix; {rank<=1} determinantal BUT Yb is a coordinate chart's
# free block -> handled by the banked SchurCore (rrp) at L=2; no PRODUCT coupling.
print("   Qb free 2x4 -> det(Yb Yb^T) is a Gram of FREE entries; this is the banked SchurCore/rrp")
print("   (routeMBoxThresholdFinite_rrp).  No product tail, no shared deeper Z -> BOUNDED (banked).")

print()
print("C9c corank-2 PRODUCT (>=2 tail factors) -> dense-torus rank-drop (Codex witness) -> RESEARCH-GRADE.")
print("   (established in peel_scope.py / peel_scope3.py)")
print()
print("SCOPE BOUNDARY:")
print("  BOUNDED (banked/toric): corank 1 (any depth); OR free single-matrix tail (depth<=3).")
print("  RESEARCH-GRADE: corank>=2 AND genuine product tail (>=2 tail factors, i.e. depth>=4).")
print("  Smallest research-grade instance: (3,3,3,4) t=1, corank 2x2, tail A1.A2 (2x3 . 3x4).")
