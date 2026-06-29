<task>
Lean 4 + Mathlib, deep-linear-net RLCT formalisation. I need a DECORRELATED soundness check on a
determinant-route design (Route b) over OPAQUE matrix widths, after a competing route (F1) was just
found UNSOUND. Facts (all verified by reading code):

THE CHART: an interior achiever chart `phi_M : (Fin N → ℝ) → (Fin N → ℝ)` (N = flatDim M, opaque). It
factors as `phi = Q ∘ Frame ∘ Kparam` (det via the chain rule `det_comp`):
- Q: a LINEAR measure-preserving coordinate reshape, |det| = 1.
- Kparam: the LDU lens (reparametrizes each per-boundary Schur K-core to LDU pivots; |det| = a monomial
  in the diagonal pivots, banked: lduCoreDeriv_det).
- Frame: a FUSED bilinear map assembling the whole chain. The chain has L layers A_0..A_{L-1}, with the
  recursion A_k = chainA(N_k, W_k, C(k+1)), C(k+1) = Bmat(k+1)·chainQ(N_{k+1}) + u·Rmat(k+1), leaf
  C_L = u·Rfin. So A_k's accumulator C(k+1) couples boundaries k..L (sequential coupling).

WHY F1 (the competing route) DIED: F1 tried `phi = composeFold [disjoint per-boundary conjBlockFactors]`
(each factor acts on one boundary's block via an abstract CLE, identity elsewhere). UNSOUND: the chain
accumulator C(k+1) couples boundaries k..L, so a composeFold of DISJOINT factors cannot reproduce the
chain product's cross-boundary mixed partials. Confirmed structurally.

ROUTE b (the revert target): the det of the FUSED Frame's Fréchet derivative `DFrame : (Fin N → ℝ) →L
(Fin N → ℝ)` is a BLOCK-TRIANGULAR determinant. Mathlib: `Matrix.BlockTriangular.det` — for a grading
`b : Fin N → α` (LinearOrder α) with off-block-vanishing (`b j < b i → M i j = 0`), `det M = ∏_{a ∈
image b} det(toSquareBlock b a)`. The claim: under a LAYER-FILTRATION grading (grade each flat coord by
WHICH chain layer / boundary it belongs to), DFrame is block-triangular, and the cross-boundary coupling
(the C(k+1) accumulator) lives in the OFF-DIAGONAL (upper) blocks — which BlockTriangular.det DISCARDS
(det = ∏ diagonal-block dets only). So the coupling is det-IRRELEVANT.

The (3,3,3,3) precedent (worked, t≥2): Frame3333Deriv_det proves |det DFrame3333| via
Matrix.BlockTriangular.det over a hand-tuned SCC grading frameB : Fin 27 → ℕ (image {0..12}, literal
index lists, bespoke Fin-k ≃ {a // frameB a = k} equivs). The diagonal blocks are the K-coupling
(7×7, det = (z1z4−z2z3)²), the radial blocks (det z0), the z9 block. This does NOT transport to opaque
widths (literal indices). The repo HAS a banked variable-length telescope (listProd_clm_abs_det:
|det ∏ fs| = ∏|det fs_i|, full-ambient, no casts) but the per-layer block-tri det is NOT yet general.
</task>

<output_contract>
Answer in 4 short sections:

1. KILL-TEST: is Route b SOUND over opaque widths? Specifically: does a LAYER-FILTRATION grading
   (b_coord = the chain-layer/boundary the coord belongs to) make DFrame block-triangular ∀M, with the
   C(k+1)-coupling in the OFF-diagonal blocks (det-irrelevant)? Or is there a configuration where the
   coupling leaks into a DIAGONAL block (det-relevant), breaking the block-tri det? Pay attention to the
   DIRECTION of the chain coupling (A_k reads C(k+1) reads boundaries ≥ k+1) — does this give a CLEAN
   one-sided (upper or lower) triangular structure, or a two-sided coupling that defeats block-tri?

2. The DIAGONAL BLOCKS: under the layer grading, what is each diagonal block, and is its det the right
   per-layer monomial (the Schur frame |det K_k|^{r+c} + the LDU pivot monomial + the radial)? Does the
   per-layer diagonal block CONTAIN the K-coupling (so its det is the |det K|^{r+c} the cert needs), or
   does the K-coupling span multiple layers (breaking the per-layer factorization)?

3. The OPAQUE-WIDTH BLOCK-TRI DET in Lean (the cost center): the (3,3,3,3) uses literal frameB +
   bespoke Fin-k≃subtype equivs. For opaque Fin (Wext M k): is the cleanest path (a) a single global
   grading b : Fin N → ℕ (the layer index) + Matrix.BlockTriangular.det + toSquareBlock reindexed by a
   GENERAL Fin (block-size) ≃ {a // b a = layer} builder; or (b) a det_comp CHAIN of per-layer
   "insertion" CLMs (each block-diagonal-with-identity-elsewhere, via listProd_clm_abs_det), avoiding a
   single global grading? Which is less brittle over opaque widths? (The pivotBlowupOnDeriv_det precedent
   uses Equiv.swap + Finset.card_equiv to avoid literal equivs — does that pattern transfer?)

4. The SINGLE biggest risk / kill-condition for Route b, and the cheapest discriminating check before
   the cold build.
</output_contract>

<grounding_rules>
You have only my summary, not the code. Mark any step depending on an unstated fact "ASSUMPTION: …".
Distinguish "follows from your summary" vs "verify X". No Lean code blocks >5 lines.
</grounding_rules>
