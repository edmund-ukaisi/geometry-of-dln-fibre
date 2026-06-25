"""Does ANY node-local n_raw recover minAdm for L>=3?  And does the reduced-chain telescope close?

The recursion the integration route (g156) actually uses descends child = red M = (M0-1,M1-1,tail),
the SAME schurStateRed, but bills the node as  min( M0*M1 , nReg + minAdm(child) )  for SOME nReg.
For the identity to hold with child=red M we NEED  nReg = minAdm(M)-minAdm(child) = d  on the binding
branch.  We showed d depends on the WHOLE tail (depth), so nReg is NOT computable from the node's local
(M0,M1,M_last) data.  But is it computable from the node's FULL chain M (a global per-node functional)?
Trivially yes: nReg(M) := minAdm(M)-minAdm(red M) ALWAYS makes min(mk, nReg+minAdm(red M)) = minAdm,
because minAdm<=mk and nReg+minAdm(red M)=minAdm.  So the telescope CLOSES with nReg := d --
but d is DEFINED via minAdm, not via a free-Morse geometry.  That is circular as a PROOF route
(you'd need to KNOW minAdm to compute the node bill).

So the real question: is there an INDEPENDENT geometric quantity (computable from the loss resolution
at the node, without already knowing minAdm) equal to d?  Candidates from the structure:
  (c1) M_last                      -- the L=2 Morse count (FALSE for L>=3)
  (c2) the rank of the deepest product block = 0 here (all-zero), no help
  (c3) nReg = r(H0+Hlast - r) at the per-node deepest -- but r=0 at all-zero -> nReg=0 (FALSE, d>=1)
  (c4) the FIRST-layer-only marginal codim from dropping ONE pivot in BOTH M0 and M1:
       count = (M0)+(M1) - 1 ??? test
  (c5) min over admissible first-exponent of the first-block marginal.

Test c4/c5 and see if any LOCAL closed form = d for all L.
"""
from itertools import product
from minadm import min_adm, argmin_adm, mval, adm_list

def red(M):
    M=list(M); M[0]-=1; M[1]-=1; return tuple(M)

def d_of(M): return min_adm(M)-min_adm(red(M))

# Candidate LOCAL formulas for d:
def c4(M): return M[0]+M[1]-1
def c5(M): return min(M[0],M[1])  # the admBound for first block
def c6(M):
    # first-block contribution at the argmin: (M0-t1)(M1-t1)-((M0-1-t1)(M1-1-t1)) summed? messy
    return None

print("Is d a LOCAL function of (M0,M1,M_last)?  Counterexample search:")
# Group binding nodes by (M0,M1,M_last); if d varies within a group -> NOT local.
from collections import defaultdict
groups=defaultdict(set)
for L in range(2,6):
    for w in product(range(1,5),repeat=L+1):
        M=tuple(w)
        if M[0]<1 or M[1]<1: continue
        if min_adm(M)>=M[0]*M[1]: continue   # binding only
        groups[(M[0],M[1],M[-1])].add(d_of(M))
nonlocal_groups = {k:v for k,v in groups.items() if len(v)>1}
print(f"  groups (M0,M1,M_last) with >1 distinct d (=> NOT node-local): {len(nonlocal_groups)} of {len(groups)}")
for k,v in list(nonlocal_groups.items())[:8]:
    print(f"    (M0,M1,M_last)={k}: d takes values {sorted(v)}")

print("\nConclusion: if many groups show multiple d, no LOCAL (node-only) n_raw exists for L>=3.")
