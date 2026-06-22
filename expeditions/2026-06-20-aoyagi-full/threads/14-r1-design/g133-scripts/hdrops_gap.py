"""
SHARP (iii) sub-point: the Lean ChainDimSplit.hdrops requires 0 < sum(drop), i.e. the SUM OF WIDTHS
strictly drops at each recursion step. Is that always achievable at a NONTERMINAL node, or can a
nonterminal node have sum(drop)=0 (width measure flat) -- forcing reliance on the chain-length lex
measure instead?

A recursion STEP (one node) blows up ONE layer's rank defect and produces a reduced chain. The drop at
that step = the dims removed. If the chosen layer has block size 0 (no rank defect, e.g. full-rank or
no-drop), the WIDTH does not drop -- but the node still makes progress by CONSUMING a layer (chain
length L -> L-1). So a step CAN have sum(drop)=0 while still being progress.

Implication for the Lean ChainDimSplit: hdrops (0 < sum drop) is the termination guard. If a genuine
node has sum(drop)=0, then EITHER:
  (a) that node is terminal (smooth leaf, no recursion), OR
  (b) the recursion must descend on a SHORTER chain (chain-length measure), which the width-sum
      ChainDimSplit.hdrops does NOT capture.

Find a chain + minimizer where the FIRST recursion step has width-drop 0 (so hdrops would FAIL if the
recursion fired at that node). M=(3,2,1) t=(2,0): layer-1 block size 0 (t_1=2=min(3,2)=full). The
descent's FIRST nontrivial drop is at layer 2. So a recursion that peels layer-by-layer hits a
width-flat node at layer 1.
"""
import sys; sys.path.insert(0,'/tmp/pp3')
from mval import Adm, Mval

def first_step_widthdrop(M, t):
    """Width dropped by the FIRST recursion step (blow up layer 1's rank defect to t_1).
    drop at layer 1 ~ the residual block (M[0]-t_1)(M[1]-t_1); if 0, width-sum flat at step 1."""
    return (M[0]-t[0])*(M[1]-t[0])

print("Nodes where the FIRST recursion step has WIDTH-DROP 0 (hdrops would be vacuous/fail there):\n")
flagged=[]
for M in [(3,2,1),(2,2,2),(4,3,2),(5,4,3,2),(3,3,3),(2,2,2,2)]:
    M=list(M)
    for t in Adm(M):
        wd=first_step_widthdrop(M,t)
        if wd==0:
            flagged.append((tuple(M),t,wd,Mval(M,t)))
for f in flagged:
    print(f"  M={f[0]} t={f[1]}: layer-1 width-drop={f[2]} (FLAT)  Mval={f[3]}")
print()
print("INTERPRETATION (Lean-grade): the WIDTH-SUM measure (ChainDimSplit.hdrops: 0<sum drop) is NOT")
print("strictly decreasing at every node -- a full-rank / no-drop layer gives width-drop 0. The")
print("recursion's true well-founded measure is LEXICOGRAPHIC (chain length, then width sum): chain")
print("length L strictly decreases by 1 each step regardless of width drop. So:")
print(" - if the Lean recursion is structured 'one layer per node', hdrops (width-only) is INSUFFICIENT")
print("   as the termination guard at a full-rank/no-drop layer; the chain-length measure carries it.")
print(" - if the Lean recursion only recurses at GENUINE drops (skipping no-drop layers in one node),")
print("   then each recursion node DOES drop width >=1, and hdrops is fine -- but then a single node may")
print("   peel several layers, which the per-node squeeze must accommodate.")
print()
print("=> SCOPED CONDITION for hdrops to be the sufficient guard: the recursion node must coincide with")
print("   a GENUINE rank-defect blow-up (block size >=1). For full-rank/no-drop layers, EITHER fold them")
print("   into the next genuine-drop node, OR carry the lexicographic (chain-length) measure. This is a")
print("   Lean structuring point, NOT a math obstruction (the descent terminates either way).")
