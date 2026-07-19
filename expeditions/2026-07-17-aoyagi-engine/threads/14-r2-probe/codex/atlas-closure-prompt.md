<task>
Independent adversarial review of a resolution-of-singularities COVER argument (Aoyagi 2023, deep
linear networks). Try to BREAK it; do not trust my framing beyond the exact definitions.

SETUP. A recursion builds a tree of blow-ups. Fix a width vector M=(M^1,...,M^{L+1}), running-min
r_S = min(M^1..M^S). Each internal tree node is ONE blow-up of a smooth coordinate CENTER of
codimension d_center:
  - "Case 1" node: d_center = J1*(M^{S+1}-J) + 1  (a J1×(M^{S+1}-J) block of residual entries + one
    divisor coordinate u).
  - "Case 2" node: d_center = (r_S - J)*(M^{S+1}-J)  (a residual block, no u).
A codim-d blow-up of the ambient at a coordinate center is covered by its d STANDARD AFFINE PIVOT
CHARTS in the max-modulus normalization:
    pivotChart_i(u)_k = u_i           (k = i)
                      = u_i * u_k      (k != i),   domain {|u_i|<=R, |u_k|<=1 (k!=i)}.
Each per-node chart is then post-composed with a per-node unit-triangular UNIPOTENT gauge ψ (a
Schur-complement/shear: d_ij -> d_ij - d_i1*d_1j on the residual interior, det Dψ = 1, ψ a
polynomial bijection). So the per-node local map is  ψ ∘ (pivotChart embedded in the ambient).
The tree's LEAF charts are the root->leaf COMPOSITIONS of these per-node maps. The claim to be
covered ("image-cover"): the union of leaf-chart images contains a neighbourhood of the zero-locus
{prod(M,A)=0} inside the unit box.

A SEPARATE combinatorial fact (established elsewhere, take as given): the recursion also tracks a
"profile" (a symmetric quotient) and emits, per Case-1 node, only TWO representative children (a
"1(1)" u-pivot chart and a "1(2)" corner d-pivot chart); the other d_center-2 block-pivot charts are
NOT separately emitted as profile-children (they collapse to the same profile). At interior width
bottlenecks (r_S drops below r_2 at an interior layer) some admissible rank strata are "stranded":
they are never cleared to the deepest (t̃=0) profile, appearing only at t̃>0 leaves.

QUESTIONS (adjudicate each independently; compute where useful):
1. Does the FULL d_center pivot family image = the cube [-R,R]^{d_center} exactly (cover + bounded)?
   Give the argument. Does a PROPER sub-family (e.g. only the u-pivot + the corner d-pivot, i.e. 2 of
   d_center charts) still cover, or is there a point/direction it misses? Exhibit any miss.
2. Does post-composing the unipotent gauge ψ PRESERVE the image-cover (does ψ∘family still cover a
   neighbourhood of the target)? Any way ψ could create a gap?
3. Does the root->leaf COMPOSITION (fold) preserve the cover, given each node covers its region?
4. The stranding: are the stranded strata's POINTS geometrically UNCOVERED (a real image-cover gap),
   or are they covered by some (t̃>0) leaf chart whose image still contains them (so only the
   deepest-monomialization read, not the cover, is affected)? Which?
5. BOTTOM LINE: is the image-cover SOUND? If it depends on a precondition, name the single most
   load-bearing one. If emitting only the 2 representative charts per node (not the full d_center
   family) is what the constructed tree actually does, what exactly breaks and where?
</task>

<output_contract>
Per question: verdict + the decisive argument or counterexample. Mark [PROVED]/[COMPUTED]/[CONJECTURED].
End with the single load-bearing precondition for the cover to hold, and whether the 2-representative
emission suffices. Keep it tight.
</output_contract>

<grounding_rules>
- Use ONLY the definitions above; compute exactly (integer/rational) if useful. State any interpretation.
- Distinguish COMPUTED from CONJECTURED. Do not defer to my framing; I withhold my own conclusion.
</grounding_rules>
