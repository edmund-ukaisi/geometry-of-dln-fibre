<task>
Lean 4 + Mathlib v4.29. I need the SINGLE cleanest proof that one specific map is measure-preserving
for Lebesgue `volume`. I have spent too long searching; give me the shortest concrete Lean proof.

THE MAP. Fix naturals p, n, a coordinate ℓ : Fin n, and real coefficients c : Fin n → ℝ with c ℓ = 1.
Define the "per-row shear" on the matrix type `Fin p → Fin n → ℝ`:
  Φ : (Fin p → Fin n → ℝ) → (Fin p → Fin n → ℝ)
  Φ X = fun i k => if k = ℓ then (∑ k', X i k' * c k') else X i k
Because c ℓ = 1, the ℓ-coordinate of each row becomes  X i ℓ + ∑_{k'≠ℓ} X i k' * c k'  (a shear), all
other coords unchanged. Same map in every row (c is row-independent). This is det-1 (per-row triangular),
hence volume-preserving. I want `MeasurePreserving Φ volume volume`.

WHAT I HAVE:
  - measurePreserving_shearAt {N} (i : Fin (N+1)) (g : (Fin N → ℝ) → ℝ) (hg : Measurable g) :
      MeasurePreserving (fun x : Fin (N+1) → ℝ =>
        Function.update x i (x i + g (fun k => x (i.succAbove k)))) volume volume
    (a single-coordinate shear on a FLAT Fin(N+1)→ℝ).
  - MeasurePreserving.comp, MeasurePreserving.symm, volume_measurePreserving_piCongrLeft (reindex by
    an Equiv), measurePreserving_piFinSuccAbove, Real.map_linearMap_volume_pi_eq_smul_volume_pi
    ({f : (ι→ℝ)→ₗ[ℝ] ι→ℝ}(hf: det f ≠ 0): map f volume = ofReal|det f|⁻¹ • volume), with ι Finite.
  - Matrix.transvection + det_transvection_of_ne (det = 1).
  - Mathlib `Measure.pi`, the matrix type carries volume = Measure.pi over rows (each row volume on Fin n→ℝ).

OPTIONS I see (pick ONE and write the full proof, ~15-40 lines):
 (A) The map is `Pi.map` over rows: Φ X i = rowShear (X i), where
     rowShear : (Fin n → ℝ) → (Fin n → ℝ), rowShear r = fun k => if k=ℓ then ∑ k' r k' c k' else r k.
     If `rowShear` is MP on (Fin n → ℝ) (via measurePreserving_shearAt at coordinate ℓ, with the affine
     part g = ∑_{k'≠ℓ} (coord k')·c k'), is there a Mathlib lemma turning "g MP on β" into
     "(fun X i => g (X i)) MP on (ι → β)" for the product measure Measure.pi (fun _:ι => volume)?
     If such a pi-pointwise-MP lemma exists, NAME IT (verify it exists) and give the 2-line proof.
     If it does NOT exist, say so and prove the helper from scratch (the cheapest way — maybe via
     `MeasurePreserving` of `MeasurableEquiv.piCongrRight`? does Mathlib have a piCongrRight measurable
     equiv whose components are MeasurableEquivs, with a measure-preserving statement?).
 (B) Reindex `Fin p → Fin n → ℝ ≃ᵐ (Fin p × Fin n) → ℝ` (curry) which IS `ι → ℝ` with ι=Fin p × Fin n
     Finite, express Φ as a LinearMap, prove det = 1, apply map_linearMap_volume_pi. How do I get det=1
     cleanly (the shear matrix is block-diagonal over rows, each block a transvection-product upper-
     triangular with unit diagonal)? Is `Matrix.det_of_upperTriangular` + a reindex to make it triangular
     the move, or is there a slicker "1 + strictly-upper" nilpotent det=1 lemma?

CRITICAL: tell me which option is SHORTEST in Lean lines and give that proof concretely. I care about
minimal mechanism. If (A) needs a pi-pointwise-MP helper that Mathlib lacks, the helper proof is part of
your answer.
</task>

<output_contract>
  1. VERDICT: option (A) or (B), one line why it is shortest.
  2. The full Lean proof of `MeasurePreserving Φ volume volume` for the chosen option, including any
     helper lemma, written to compile against Mathlib v4.29 (flag any lemma name you are <90% sure of
     with "VERIFY NAME").
  3. The exact statement of the helper "pi-pointwise MP" lemma if option (A), with whether it is in
     Mathlib (name) or must be proven (then the proof).
</output_contract>

<grounding_rules>
  Do not assert a Mathlib lemma exists unless you are confident; mark uncertain names "VERIFY NAME".
  If the pi-pointwise-MP helper genuinely is not in Mathlib, the cheapest from-scratch proof is the
  deliverable — do not hand-wave it.
</grounding_rules>
