<task>
Design review (adversarial) of a recursive resolution-of-singularities construction for a
deep-linear-network RLCT computation. Stress the NODE TAXONOMY for exhaustiveness and the TERMINATION
measure. Find a layer structure the taxonomy misses, or confirm it is exhaustive.

SETUP. The "core" is F = ‖C_L · … · C_1‖²_F, a product of real matrix factors C_s : M_s × M_{s+1},
at the origin (all C_s = 0). Goal: rlctAtOn(F) at 0 = ½·min over the admissible rank strata of their
codimension (= ½·minAdm Mval). The construction is a TREE of coordinate charts (Aoyagi-style recursive
blow-ups + Schur-complement reductions); the value is ⨅ over chart leaves of the monomial threshold
min_j (h_j+1)/(2k_j).

THE NODE TAXONOMY (the branch logic, claimed exhaustive over layer structures):
- C1 (coupled blow-up): a layer with a genuine rank-defect of the active factor that couples to the
  next factor — blow up the rank-defect center; in each affine chart a hard-unit pivot appears, a
  Schur-complement step decouples F into (regular squares) + ‖reduced chain‖² (smaller chain), recurse.
- C2 (full-rank pass-through): the active factor is FULL rank but the PRODUCT still drops rank (the
  rank drop is in a LATER factor) — pass the full-rank factor through (absorb it) and descend so the
  later-factor drop is resolved. [Witness it is needed: M=(1,2,1), C1=(x1,x2) full rank, C1·C2=0.]
- C3 (NC-completion, k_E≥2): turning the union of exceptional divisors into a normal-crossing
  arrangement can require intersection blow-ups where one exceptional coordinate absorbs two factors'
  vanishing, giving multiplicity k_E≥2 (e.g. x²y² blown up at the origin → u⁴v²). The Jacobian
  discrepancy compensates so the RATIO stays codim/2; the lower bound uses the multiplicity-control
  inequality m·k ≤ h+1, NOT k_E=1.
- C4 (Fubini pinch): a width-1 / rank-pinch / s=0 inner layer makes the core a PRODUCT of separate
  smooth blocks (‖C1·C2‖²=‖C1‖²‖C2‖² for a rank-1 bottleneck) — resolve by Fubini product-min, NOT a
  coupled blow-up (which would leave an empty Schur complement and stall).

TERMINATION: the measure is lex(depth L, ΣM = Σ_s M_s). Either L drops (a factor fully
resolved/passed through, C2) or L same and ΣM drops (a Schur rank-reduction, C1). Base: L=1, F=‖C_1‖²
a pure smooth block, rlct = (#entries)/2.

THE VALUE ARGUMENT (S-min): ⨅ over leaves = ½·minAdm Mval via le_antisymm:
  (C≥) every leaf threshold ≥ ½·minAdm Mval [uniform, via multiplicity-control m·k≤h+1];
  (C=∃) one leaf (the path to the minimising stratum) achieves = ½·minAdm Mval.
</task>

<output_contract>
1. Is the node taxonomy C1–C4 EXHAUSTIVE over layer structures? Construct a layer configuration it
   misses, or argue exhaustiveness (every node is exactly one of coupled / full-rank-pass-through /
   pinch-separating, with NC-completion as a post-pass). Watch for: mixed nodes (partial rank drop +
   partial pass-through), multiple simultaneous pinches, rank drops spanning ≥2 layers.
2. Is lex(L, ΣM) a SOUND well-founded termination measure? Does every node type strictly decrease it?
   Any node that decreases neither L nor ΣM (a stuck node)?
3. Is the (S-min) value argument sound — (C≥) uniform lower bound + (C=∃) one achiever? Any leaf that
   could undershoot ½·minAdm (a divisor with ratio < minAdm/2 that the multiplicity-control misses)?
4. Overall: is this a complete, terminating, value-correct construction? Name the load-bearing facts;
   if a gap, name the layer structure that breaks it.
</output_contract>

<grounding_rules>
- Reason structurally / by exact algebra; do not rely on numerics for the load-bearing claims.
- Distinguish a divisor's multiplicity k_E (F-vanishing order) from the codim of its center.
- "Admissible rank strata" = weakly-decreasing prefix-rank tuples t_j = rank(C_1..C_j), t_L = 0.
- Be adversarial on exhaustiveness: try to build a node that is none of C1–C4, or a mix that the
  branch logic can't classify, before concluding.
</grounding_rules>
