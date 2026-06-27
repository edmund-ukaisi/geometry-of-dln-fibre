<task>
I am red-teaming a Lean 4 + Mathlib formalisation of a measure-theory finiteness result. Two specific
soundness questions. Answer mathematically; I am NOT asking you to write Lean.

CONTEXT. We bound a fibre integral for deep-linear-network loss. Definitions (entrywise, real matrices):
- frobSq M = ∑_{i,j} (M i j)^2   (squared Frobenius norm).
- rmatMul X Y i j = ∑_k X i k * Y k j   (genuine matrix product), X: p×n, Y: n×q.
- matBox p n T = { X : Fin p → Fin n → ℝ | ∀ i k, X i k ∈ [-T, T] }   (CLOSED box).
- Lebesgue volume throughout.

KEY LANDED LEMMA (proven sorry-free, I verified #print axioms = [propext, Classical.choice, Quot.sound]):
  fibre_lintegral_mul_le : for 1≤p, 1≤n, 1≤q, T>0, 0<c'<p/2, and ANY fixed Y : Fin n → Fin q → ℝ,
    ∫⁻_{X ∈ matBox p n T} ofReal((frobSq (rmatMul X Y))^(-c'))
      ≤ fibreConst p n q T c' * ofReal((frobSq Y)^(-c')),
  where fibreConst is a Y-independent finite constant (= ofReal((n*q)^c') * Kbound_p * spectator-vol).
  Proof outline: pick max-abs entry (ℓ,j) of Y INSIDE the proof via Finset.exists_max_image; per-row
  shear u_i := (XY)_{ij}/Y_{ℓj} is det-1 (volume-preserving); frobSq(XY) ≥ Y_{ℓj}^2 · ∑_i u_i^2 (drop
  other cols + pull pivot out) and Y_{ℓj}^2 ≥ frobSq Y/(nq) (mean ≤ max); the ∑u_i^2 box integral is
  the p-dim radial Morse integral ∫(∑u_i^2)^{-c'}, finite for c'<p/2. The Y=0 case: both sides 0 (0^{-c'}
  =0 since c'>0). The pivot-zero set {∑u_i^2=0} is shown Lebesgue-null and the pointwise rpow domination
  holds a.e. off it.

QUESTION 1 (the iterated assembly). We then claim:
  triple_fibre_lt_top : for 0<c'<2,
    ∫⁻_{A2 ∈ matBox 2 2 1} ∫⁻_{A1 ∈ matBox 4 2 1} ∫⁻_{A0 ∈ matBox 4 4 1}
      ofReal((frobSq (rmatMul (rmatMul A0 A1) A2))^(-c')) < ⊤.
  Proof: A0-fibre uses associativity rmatMul(rmatMul A0 A1)A2 = rmatMul A0 (rmatMul A1 A2), then
  fibre_lintegral_mul_le with (p,n,q)=(4,4,2), Y = rmatMul A1 A2 → ≤ C0 · ofReal(frobSq(A1·A2)^{-c'}).
  A1-fibre: fibre_lintegral_mul_le with (p,n,q)=(4,2,2), Y=A2 → ≤ C1 · ofReal(frobSq A2^{-c'}).
  A2 leaf: ∫_{matBox 2 2 1} ofReal(frobSq(A2)^{-c'}) < ⊤ (a 4-dim sum-of-squares Morse integral, c'<2).
  Pull the Y-independent constants C0,C1 out through the inner lintegrals (lintegral_const_mul').
  Is the threshold c'<2 (= p/2 with p=4) CORRECT for ALL THREE steps, i.e. is the binding constraint
  really p=4 at every layer and NOT n or q? Is there any subtlety where Tonelli/the constant-pull or the
  associativity rewrite could fail or silently weaken the bound? Is c'<2 tight (matches ½·minAdm=2)?

QUESTION 2 (whether triple_fibre_lt_top SUFFICES for the headline). The headline target (currently a
single `sorry`) is:
  routeMCore_M4422_threshold_lt_top : for c' : NNReal with (c':ℝ) < minAdm/2 = 2,
    ∫⁻_{x ∈ routeMBaseNbhd} ofReal(|routeMCore M4422 x|^(-(c':ℝ))) < ⊤,
  where routeMCore M4422 = dlnLoss M4422 0 ∘ (paramsEquivFlat).symm, dlnLoss M4422 0 A = frobSq(prod A)
  (proven), prod A = rmatMul(rmatMul A0 A1) A2 entrywise (proven, A0:4×4, A1:4×2, A2:2×2), and
  routeMBaseNbhd = (-1,1)^28 is the OPEN box (Set.univ.pi (fun _ => Ioo (-1) 1)) in flat coords, while
  triple_fibre_lt_top integrates over the product of CLOSED boxes matBox 4 4 1 × matBox 4 2 1 × matBox 2 2 1.
  paramsEquivFlat is a measure-preserving equiv Params M4422 ≃ᵐ (Fin 28 → ℝ).

  Enumerate EVERY mathematical step needed to get from triple_fibre_lt_top to the headline, and for EACH
  say whether it is genuine routine measure-theory bookkeeping (TRUE and standard) or a hidden math gap:
  (a) |routeMCore| = routeMCore (frobSq ≥ 0, so the abs is identity) — sound?
  (b) the c'=0 boundary: triple_fibre_lt_top REQUIRES 0<c', but the headline allows c'=0 (NNReal ≥ 0).
      Is c'=0 trivially finite separately (integrand becomes 1 over a bounded box)? Confirm.
  (c) OPEN box (-1,1)^28 vs the CLOSED matBox product [-1,1]^28: the integrand is the same; is the
      open-vs-closed swap justified because the boundary (a finite union of coordinate hyperplanes
      intersected with the box) is Lebesgue-null? Any subtlety with the (-c') power blowing up on the
      boundary set {prod=0} that could make the boundary contribute? (Note prod=0 is itself a positive-
      codim set INSIDE the box, already handled inside triple_fibre by the a.e. argument; the question is
      only the box-boundary swap.)
  (d) the paramsEquivFlat reshape: the 28 flat coords ↔ (A0:16, A1:8, A2:4) entries, and the single
      28-dim box integral = the 3-fold iterated integral via Tonelli + a measure-preserving reindex
      (Fin 28 → ℝ) ≃ᵐ (Fin 16→ℝ)×(Fin 8→ℝ)×(Fin 4→ℝ) then arrowProd splits. Is this a genuine MP +
      Tonelli composition with no orientation/Jacobian issue (it is a pure coordinate PERMUTATION, det
      ±1)? Any risk the flat coordinate ORDER mismatches the (A0,A1,A2) entry order so the reindex is
      not the identity-up-to-permutation I claim?
  Then give a single verdict: is the `sorry` HONESTLY SCOPED as "Params-reshape + Tonelli + boundary-null
  bookkeeping", or does any of (a)-(d) hide genuine unproven mathematical content (a real gap, not just
  Lean labour)?
</task>

<output_contract>
Two sections, QUESTION 1 and QUESTION 2.
- QUESTION 1: one paragraph verdict (threshold correct? any subtlety?) + explicit confirmation each of
  the 3 steps binds at p=4 not n/q.
- QUESTION 2: a numbered list (a)-(d), each one line: SOUND-BOOKKEEPING or GAP, with the one-sentence
  reason. Then a final one-line verdict: HONESTLY-SCOPED or HIDES-A-GAP.
Be terse. No Lean code.
</output_contract>

<grounding_rules>
Distinguish what is mathematically certain from what you are inferring from my description. If a step's
soundness depends on a fact about Mathlib's definitions I have not given you (e.g. exactly how volume on
(Fin 28 → ℝ) decomposes), say so and mark it INFERENCE. Do not assume my outline is correct — if the
threshold or a step looks wrong, say which and why with a concrete reason.
</grounding_rules>
