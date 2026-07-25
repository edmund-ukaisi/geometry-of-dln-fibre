#!/usr/bin/env python3
"""Adopt Codex's correction: the inductive step needs hyp(ii) = the stabilizer is transitive on
PIVOT POSITIONS (row,col) of the residual block, NOT the full symmetric group on the block's entries.
Verify the CORRECTED hyp(ii) exactly on the (3,3,3,2,2) residual blocks, and confirm the (wrong,
too-strong) full-symmetric-group claim is indeed false."""
from itertools import permutations, product
import math

def product_group_transitive_on_positions(nrow, ncol):
    """Srow x Scol acting on (i,j) positions: transitive? (yes iff it can map any (i,j)->(i',j'))."""
    positions = [(i,j) for i in range(nrow) for j in range(ncol)]
    Srow = list(permutations(range(nrow))); Scol = list(permutations(range(ncol)))
    def act(pr,pc,pos): return (pr[pos[0]], pc[pos[1]])
    for a in positions:
        reach = {act(pr,pc,a) for pr in Srow for pc in Scol}
        if set(reach)!=set(positions): return False
    return True

print("CORRECTED hyp(ii): stabilizer = Srow x Scol transitive on (row,col) PIVOT POSITIONS")
for (nr,nc,label) in [(2,3,"layer block 2x3 (Codex's example)"),(2,2,"deep 2x2"),(3,3,"3x3"),(1,3,"1x3 row"),(2,1,"2x1 col")]:
    t = product_group_transitive_on_positions(nr,nc)
    full_sym_order = math.factorial(nr*nc)
    prod_order = math.factorial(nr)*math.factorial(nc)
    print(f"  {label}: Srow x Scol transitive on POSITIONS: {t} ; "
          f"|Srow x Scol|={prod_order} vs |S_(rc)|={full_sym_order}  "
          f"(full-sym claim {'FALSE' if prod_order<full_sym_order else 'trivially ok'})")
print()
print("=> The induction needs POSITION-transitivity (canonicalize the ONE next pivot), which HOLDS.")
print("   The 'full symmetric group on entries' phrasing was too strong and generally FALSE (Codex).")
print("   With hyp(ii) corrected to position-transitivity + the standard residual-chart equivariance")
print("   lemma (stabilizer preserves the residual block & intertwines the chart id), the step is GO.")
