<task>
Adjudicate a determinant-factorization design for a Lean proof. A structured chart phi: R^N -> R^N (a DLN
achiever chart) is built from a decoder with a GAUGE-FIXED pivot: at one matrix block position (call it the
E(0,0) slot of the pivot boundary) there is a LITERAL 1 (not a free coordinate). The radial scalar u (a
separate coordinate) multiplies the whole R/Rfin block family, so the chart output at the E(0,0) position is
"... + u·1 = ... + u" (ADDITIVE in u), while at the other free R/Rfin coords it is "... + u·(free coord)"
(MULTIPLICATIVE). Derive the answer; the sympy facts are exact.
</task>

<facts_exact_sympy>
Verified EXACTLY at N=8 (2,2,2) and N=18 (3,3,3) on the ACTUAL fixed-pivot decoder:
- A naive contract "smulRmatRfin u (decoder x) = decoder(pivotBlowupOn x)" is FALSE (the literal 1: u·1 ≠ 1).
- BUT the CHART-LEVEL factorization phi = B ∘ pivotBlowupOn(active, p) HOLDS, where:
    * active = {structPivot} ∪ {the FREE E-coords (excluding the fixed (0,0) anchor)} ∪ {leaf coords};
      card(active) = minAdm exactly.
    * pivotBlowupOn(active, p): u->u; x_i -> u·x_i for i in active\{p}; else fixed.
    * B is the "de-radialized chart": it reads the free E-coords and leaf DIRECTLY (un-scaled), and reads
      the E(0,0) output ADDITIVELY from the pivot coordinate wu (i.e. B's output there is "... + wu").
- With this B: det DB = engine product (|K|^{r+c}·∏|q|^{...}), u-FREE, and FULL RANK (nonzero). 
  det Dphi = det(DB)·u^{minAdm-1}. (Verified: full chart det is a single u^{minAdm-1} monomial times engine.)
So the additive u·1 at the gauge-fixed E(0,0) is ABSORBED INTO B (B is affine in wu), NOT a radial blow-up
target; the radial map is PURE multiplicative pivotBlowupOn on {E-free ∪ leaf}.
</facts_exact_sympy>

<questions>
1. Is it sound that the gauge-fixed E(0,0) (the additive u·1) is handled by B being AFFINE in the pivot
   coordinate wu (B reads wu additively at that output), rather than by the radial blow-up? I.e. the radial
   map is pure pivotBlowupOn on the MULTIPLICATIVE actives {E-free ∪ leaf} (NOT including the E(0,0) slot,
   which has no free coord), and B absorbs the additive pivot term. Does this make B a genuine local iso
   (det DB = engine ≠ 0) — confirm the additive wu does not collapse B's rank?
2. The contract for the map identity is then NOT "decoder commutes with blowup" (the false hslot) but the
   CHART-level "phi = B ∘ pivotBlowupOn(active,p)" with B := phi-de-radialized (E(0,0) read additively,
   others read at the blown coord). Is this the right contract, and does it avoid the u·1 ≠ 1 obstruction
   (because B is NOT decoder(blowup) — it reads the E(0,0) from the pivot slot additively)?
3. The count: active = {pivot} ∪ {E-free} ∪ {leaf}, card = minAdm. The E(0,0) anchor is NOT in active (it's
   the fixed 1). So #active - 1 (the blow-up exponent) = (#E-free + #leaf) = minAdm - 1. Confirm this is the
   correct budget (the fixed-pivot gauge removes exactly ONE coordinate, the E(0,0), which is the radial
   pivot's additive image, keeping the exponent minAdm-1).
</questions>

<output_contract>
For each question: a direct verdict + the reason. Flag any residual soundness risk (e.g. whether B being
affine-in-wu could still hide a rank drop at special points, or whether the additive term needs the pivot
coordinate to be distinct from all active coords). Mark proof vs heuristic.
</output_contract>

<grounding_rules>
The sympy facts are exact (det computed symbolically/at exact rationals). Reason about the linear-algebra
soundness (chain rule + det_comp + B full rank). Don't rubber-stamp; if "B affine in wu" hides a degeneracy,
say so.
</grounding_rules>
