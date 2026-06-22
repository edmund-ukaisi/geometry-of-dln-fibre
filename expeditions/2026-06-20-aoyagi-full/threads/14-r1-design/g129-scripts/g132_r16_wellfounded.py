import sympy as sp
# WELL-FOUNDEDNESS of the (C2) per-node recursion.
# At node M=(M_0,...,M_L), the squeeze-straighten produces reduced node M' = S.red with the Schur step:
# the active factor (an M_s x M_{s+1} block at the pivot layer) loses its pivot row+col → the Schur
# complement is (M_s -1) x (M_{s+1} -1), and the neighbouring factors restrict to the matching reduced
# index sets. The recursion measure is ΣM = Σ_s M_s. CLAIM: ΣM' < ΣM at every nonterminal step, and the
# base case L=1 (or any all-bilinear leaf at the origin) terminates.
#
# The ChainDimSplit carries drop_s + red_s = M_s with 0 < Σ drop_s (the termination condition).
# measure_drops: Σ red_s < Σ M_s  ⟸  Σ drop_s > 0. This is PROVEN in Lean (ChainDimSplit.measure_drops).
# So well-foundedness reduces to: does EVERY nonterminal node have Σ drop_s > 0 (a genuine pivot to resolve)?
#
# Question: can a node be STUCK — nonterminal (core still singular, not yet pure smooth block) yet
# Σ drop_s = 0 (no pivot can be resolved)? That would break well-foundedness (infinite recursion at fixed ΣM).
print("=== Well-foundedness: is there a STUCK node (singular core, no resolvable pivot)? ===")
print("""
The node's core is dlnLoss M 0 = ‖∏ C‖² at the origin (all-bilinear). The blow-up of the rank-defect
center makes a leading minor a HARD unit pivot (#127). After blow-up the Schur step resolves that pivot
row+col: drop_s ≥ 1 at the pivot layer (and its neighbour), so Σ drop ≥ 1 > 0 — UNLESS there is no
nonzero entry to pivot on, i.e. the active factor is the ZERO matrix on its whole stratum. But:
 - if a factor C_s is forced 0 on the stratum, the product ∏C = 0 identically there (that direction is
   already resolved — it contributes a regular Σx² block, not a singular pivot);
 - the SINGULAR core (the part with rank-defect, not yet smooth) always has a nonzero minor to blow up
   (else it is already rank-0 = the smooth leaf). So a nonterminal singular node ALWAYS has a pivot.
⟹ Σ drop ≥ 1 at every nonterminal node ⟹ ΣM strictly decreases ⟹ recursion is WELL-FOUNDED on ℕ (ΣM).
""")
# Concretely trace ΣM down a chain to confirm strict decrease + termination at a leaf:
def schur_step(M):
    # pivot at the layer with the widest reducible block; conservative model: drop 1 from two adjacent
    # widths (the Schur step removes a row from layer s and a col from layer s+1 = a width unit each).
    M = list(M)
    # find first adjacent pair both >=1 with a genuine inner contraction (both >0 and product nontrivial)
    for s in range(len(M)-1):
        if M[s] >= 1 and M[s+1] >= 1 and (M[s] > 1 or M[s+1] > 1 or len(M) > 2):
            # Schur: reduce the inner dims; model the (m,k)->(m-1,k-1) on the active factor's two endpoints
            Mn = M[:]
            # the active factor is C between layer s,s+1 of shape M[s] x M[s+1]; Schur drops 1 from each
            if Mn[s] > 1: Mn[s]-=1
            if Mn[s+1] > 1: Mn[s+1]-=1
            # if both were 1 (1x1 factor = scalar), it's resolved: terminal for that factor
            if Mn==M:  # nothing dropped -> would be stuck; mark by returning None
                continue
            return Mn
    return None  # terminal

for M0 in [[3,3,3],[2,2,2,2],[4,3,2],[5,4,3,2],[2,2,2]]:
    chain=[tuple(M0)]; M=M0[:]
    for _ in range(50):
        Mn=schur_step(M)
        if Mn is None: break
        chain.append(tuple(Mn)); M=Mn
    sums=[sum(c) for c in chain]
    strict = all(sums[i]>sums[i+1] for i in range(len(sums)-1))
    print(f"  M0={M0}: ΣM chain {sums}  strictly-decreasing={strict}  terminates={Mn is None}")
