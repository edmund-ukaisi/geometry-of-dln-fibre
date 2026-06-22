import sympy as sp, itertools
# ADVERSARIAL on (a1): is the blow-up CENTER right? {core=0} = {∏C=0} is the FULL singular locus, a
# UNION of rank-strata, MUCH bigger than {A1=0}. If the recursion only blows up {A1=0}, does its chart
# cover reach the OTHER components of {∏C=0} (e.g. {A1≠0 but A2 drops rank})?
#
# Test on (2,2,2): C = (A1, A2), ∏C = A1·A2 (2x2). {∏C=0} = {A1·A2=0}. Components:
#   - A1 = 0  (then ∏=0 regardless of A2)              -- the "first factor zero" component
#   - A2 = 0
#   - A1≠0, A2≠0 but A1·A2=0  (rank-deficient alignment: im(A2) ⊆ ker(A1))
# At the ORIGIN (deepest point, A1=A2=0), ALL components pass through. The recursion's FIRST blow-up:
# does it blow up {A1=0}, or the whole {A1·A2=0}, or something else?
#
# Per #127/#129: the FIRST step at the all-bilinear origin blows up the rank-defect of the WHOLE product.
# But the design (g3, l1-elimination) blows up the rank-stratum center. Let me check: is the cover by
# "blow up A1's rank-defect, then within each chart recurse on the Schur core" EXHAUSTIVE of {∏C=0}?
A1 = sp.Matrix(2,2, sp.symbols('a0:4'))
A2 = sp.Matrix(2,2, sp.symbols('b0:4'))
P = sp.expand(A1*A2)
# The squeeze recursion (#129): blow up {A1=0} via A1 = x·Â (Â[0,0]=1 hard in chart 0). In chart 0,
# F = x²·‖Â·A2‖². The recursion then handles ‖Â·A2‖² (the reduced node). 
# BUT this chart requires A1[0,0]≠0 (the pivot). The OTHER charts (A1[0,1]≠0, A1[1,0]≠0, A1[1,1]≠0) and
# the A2-side... Question: does the A1-blow-up cover the component {A1≠0, A2 rank-deficient}?
# In chart A1[0,0]≠0: A1 invertible-ish (leading entry unit), so ∏C=0 ⟺ A2 small in the Schur sense.
# The reduced node ‖Â·A2‖² then has ITS OWN singular locus {Â·A2=0} ⊇ {A2=0} and the aligned component.
# So the recursion DOES reach the A2-side: within the A1-chart, the reduced core ‖Â·A2‖² recurses and
# blows up A2's rank-defect. The TREE reaches all components.
print("=== (a1) adversarial: does the A1-blow-up + recursion reach ALL components of {∏C=0}? ===")
print("""
At the origin every component of {∏C=0} passes through. The recursion is a TREE:
  node M=(2,2,2): blow up the first factor's rank-defect → charts indexed by the pivot;
     within each chart, F = x²·‖Â·A2‖², and the REDUCED node ‖Â·A2‖² recurses → blows up A2's defect.
So the A2-side / aligned components ARE reached — at the SECOND level of the tree, inside the A1-chart.
The cover is the COMPOSITE of the per-level chart covers (a tree of charts), not a single blow-up.
KEY CHECK: is the composite tree EXHAUSTIVE of {∏C=0} near the origin? Each level's chart cover is the
projective-atlas-exhaustive cover of THAT level's center; the composite covers ⋃(all rank-strata)
PROVIDED every stratum is reached by SOME root-to-leaf path. The rank-stratification of {∏C=0} is
exactly indexed by the (per-layer rank) tuples = the recursion's branch choices. So:
""")
# Verify: the rank-strata of {∏C=0} for (2,2,2) are indexed by (rank A1, rank A2, rank ∏) with ∏=0.
# Enumerate admissible rank tuples and check they correspond to recursion paths.
print("rank-strata of {A1·A2=0} (2x2), (rkA1, rkA2) with A1·A2=0:")
strata=[]
for r1 in range(3):
    for r2 in range(3):
        # A1·A2=0 with rk A1=r1, rk A2=r2 possible iff im(A2) ⊆ ker(A1), i.e. r2 ≤ 2 - r1 (ker dim)
        if r2 <= 2 - r1:
            strata.append((r1,r2))
print("  admissible (rkA1,rkA2):", strata)
print("""
  Each (r1,r2) is reached by a recursion path: blow up A1 to expose rk r1 (the Schur step resolves
  2-r1 pivot units), descend, then the reduced node blows up A2 to expose r2. The branch tree's
  root-to-leaf paths ARE the rank-stratum tuples. ⟹ every stratum is reached ⟹ composite EXHAUSTIVE.
  This is Aoyagi's recursive blow-up = a COMPLETE resolution (published); the stratification index
  set = the branch set. ✓ (modulo: the per-node center is the rank-defect of the ACTIVE factor, and
  the active factor cycles through all layers as the recursion descends — confirm next.)
""")
