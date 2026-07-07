import DLNFibre.DLN.RLCT.Validate.RouteMSJGammaAtom
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankStep

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCorankPeel` — the integral-level corank-block morse peel

The **integral weld** of the R-BLOWUP crux (`corankStep` / `frobSq_schur_block_split`,
`RouteMSJCorankStep` / `RouteMSJChartAlgebra`) onto the banked anisotropic corank atom
(`gammaAtom_aniso_shifted_eq`, `RouteMSJGammaAtom`). The pointwise Schur block split leaves the loss as

    frobSq (A₀ · Q) = frobSq (A · Q̃_p) + frobSq (C · Q̃_p + Γ · Q_b),

`Γ = schurCompl A B C D` the corank block (`p × q`, `p = M₀ − t`, `q = M₁ − t`), with the pivot energy
`frobSq (A · Q̃_p)` and the cross-shift `C · Q̃_p` both **`Γ`-free**. This module integrates the single
freed corank block `Γ` over its `p × q` coordinates against the residual-power engine.

The per-step result — for coupling `Q_b` of full row rank (`Q_b Q_bᵀ` positive definite) and `c'` above
the block Morse threshold `pq/2`:

    ∫_{Γ ∈ ℝ^{p×q}} (w + ‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{−c'} dΓ
      = det(Q_b Q_bᵀ)^{−p/2} · Cresid(pq) c'
          · (w + ‖A·Q̃_p‖² + ‖C·Q̃_p·(I − P)‖²)^{−(c' − pq/2)},   P = Q_bᵀ (Q_b Q_bᵀ)⁻¹ Q_b.

This is Aoyagi's per-boundary exponent shift `c' ↦ c' − pq/2` at block dimension `a = pq = (M₀−t)(M₁−t)`:
the corank block peels, contributing the coupling Jacobian `det(Q_b Q_bᵀ)^{−p/2}` and dropping the deeper
core to the shifted exponent. The held pivot energy `frobSq (A · Q̃_p)` rides in the additive core
(strictly positive whenever `w > 0`), never divided by the block resolution — the exact integral shadow of
the sequential-independence invariant `corankStep_prefactor`.

The Schur-split specialisation (the explicit tie to `corankStep`) is `corankBlock_morsePeel_eq` at
`Apiv := A · Q̃_p`, `Ccross := C · Q̃_p`, `Qb := Q.submatrix Sum.inr id`, `Q̃_p := Q_p + ⅟A · B · Q_b` —
a mechanical instantiation of the general lemma below.

## What this weld is, and is NOT (fidelity)

This is the *inner* per-chart `Γ`-integral of `sjJointResolution` (the deferred analytic core of the
general-`L` `(S,J)` peel). It produces the per-step charge exactly, and its `< ⊤` corollary is the
per-step finiteness the recursion's inner integral needs. It does NOT: (i) enlarge/shear the corank box
`{Γ | Γ + C A⁻¹ B ∈ box}` onto the full space (a separate MP step, `measurePreserving_shearSub`; the
box-restricted `_setLE` / `_lt_top` bounds below survive without it — a subset integral is `≤` the
full-space value); (ii) discharge the OUTER tail-parameter `A'`-integral carrying the accumulated Gram
residual `det(Q_b Q_bᵀ)^{−p/2}` and the shifted core — that is the `(S,J)` double induction, the standing
gap (`sjJointResolution`, untouched).

Rides only the banked `gammaAtom_aniso_shifted_eq` (itself axiom-clean, S2-free); no `monomial_rlct`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-! ## The corank-block morse peel — the exact full-space per-step charge -/

/-- **The corank-block morse peel (EXACT, full space).** Integrating the freed corank block
`Γ : Fin p → Fin q → ℝ` against the Schur residual `frobSq (Ccross + Γ · Q_b)`, on the strictly-positive
core `w + frobSq Apiv` (the deeper loss `w > 0` plus the held pivot energy `Apiv = A · Q̃_p`), with the
coupling `Q_b` of full row rank (`Q_b Q_bᵀ` positive definite) and `c'` above the block threshold `pq/2`:

    ∫_{Γ} (w + ‖Apiv‖² + ‖Ccross + Γ·Q_b‖²)^{−c'} dΓ
      = det(Q_b Q_bᵀ)^{−p/2} · Cresid(pq) c' · (w + ‖Apiv‖² + ‖Ccross·(I − P)‖²)^{−(c' − pq/2)}.

`gammaAtom_aniso_shifted_eq` (`R := Q_b`, `S := Ccross`) with the pivot energy folded into the additive
core; the block peels at threshold `pq/2`, giving the exponent shift `c' ↦ c' − pq/2`. -/
theorem corankBlock_morsePeel_eq {p q n r : ℕ}
    (Apiv : Matrix (Fin r) (Fin n) ℝ) (Ccross : Matrix (Fin p) (Fin n) ℝ)
    (Qb : Matrix (Fin q) (Fin n) ℝ) (hG : (Qb * Qbᵀ).PosDef)
    (c' : ℝ) (hc' : (p * q : ℝ) / 2 < c') (w : ℝ) (hw : 0 < w) :
    ∫⁻ Γ : Fin p → Fin q → ℝ,
        ENNReal.ofReal ((w + frobSq Apiv + frobSq (Ccross + (Matrix.of Γ) * Qb)) ^ (-c'))
      = ENNReal.ofReal ((Qb * Qbᵀ).det ^ (-(p : ℝ) / 2) * Cresid (p * q) c'
          * (w + frobSq Apiv
              + frobSq (Ccross * (1 - Qbᵀ * (Qb * Qbᵀ)⁻¹ * Qb))) ^ (-(c' - (p * q : ℝ) / 2))) := by
  have hw' : (0 : ℝ) < w + frobSq Apiv := add_pos_of_pos_of_nonneg hw (frobSq_nonneg _)
  have hbridge : ∀ Γ : Fin p → Fin q → ℝ,
      ENNReal.ofReal ((w + frobSq Apiv + frobSq (Ccross + (Matrix.of Γ) * Qb)) ^ (-c'))
        = ENNReal.ofReal
            (((w + frobSq Apiv) + frobSq ((Matrix.of Γ) * Qb + Ccross)) ^ (-c')) := by
    intro Γ; rw [add_comm ((Matrix.of Γ) * Qb) Ccross]
  rw [lintegral_congr hbridge,
    gammaAtom_aniso_shifted_eq Qb Ccross hG c' hc' (w + frobSq Apiv) hw']

/-- **The corank-block morse peel, set-restricted bound (any domain).** Over ANY sub-domain `s` of the
corank coordinates (in particular the shear-image box `{Γ | Γ + C A⁻¹ B ∈ box}` the peel actually
integrates), the integral is bounded by the exact full-space per-step charge value. `lintegral_mono_set`
(`s ⊆ univ`) + `setLIntegral_univ` + `corankBlock_morsePeel_eq`: a subset integral is `≤` the full-space
value, so the box need not be enlarged/sheared to obtain a finite bound. -/
theorem corankBlock_morsePeel_setLE {p q n r : ℕ}
    (Apiv : Matrix (Fin r) (Fin n) ℝ) (Ccross : Matrix (Fin p) (Fin n) ℝ)
    (Qb : Matrix (Fin q) (Fin n) ℝ) (hG : (Qb * Qbᵀ).PosDef)
    (c' : ℝ) (hc' : (p * q : ℝ) / 2 < c') (w : ℝ) (hw : 0 < w)
    (s : Set (Fin p → Fin q → ℝ)) :
    ∫⁻ Γ in s,
        ENNReal.ofReal ((w + frobSq Apiv + frobSq (Ccross + (Matrix.of Γ) * Qb)) ^ (-c'))
      ≤ ENNReal.ofReal ((Qb * Qbᵀ).det ^ (-(p : ℝ) / 2) * Cresid (p * q) c'
          * (w + frobSq Apiv
              + frobSq (Ccross * (1 - Qbᵀ * (Qb * Qbᵀ)⁻¹ * Qb))) ^ (-(c' - (p * q : ℝ) / 2))) := by
  calc ∫⁻ Γ in s,
          ENNReal.ofReal ((w + frobSq Apiv + frobSq (Ccross + (Matrix.of Γ) * Qb)) ^ (-c'))
      ≤ ∫⁻ Γ in Set.univ,
          ENNReal.ofReal ((w + frobSq Apiv + frobSq (Ccross + (Matrix.of Γ) * Qb)) ^ (-c')) :=
        lintegral_mono_set (Set.subset_univ s)
    _ = ∫⁻ Γ,
          ENNReal.ofReal ((w + frobSq Apiv + frobSq (Ccross + (Matrix.of Γ) * Qb)) ^ (-c')) :=
        setLIntegral_univ _
    _ = _ := corankBlock_morsePeel_eq Apiv Ccross Qb hG c' hc' w hw

/-- **The per-step corank integral is finite (the recursion's inner-integral finiteness).** Over any
domain `s`, the corank integral is `< ⊤` — the exact per-step charge value on the RHS of
`corankBlock_morsePeel_setLE` is a real `ENNReal.ofReal`, hence finite (`ENNReal.ofReal_lt_top`). This is
the shape the outer `(S,J)` recursion consumes for the inner `Γ`-integral: once the coupling `Q_b` is of
full row rank and `c'` is above the block threshold `pq/2`, the freed corank block contributes only a
finite per-step factor. -/
theorem corankBlock_morsePeel_lt_top {p q n r : ℕ}
    (Apiv : Matrix (Fin r) (Fin n) ℝ) (Ccross : Matrix (Fin p) (Fin n) ℝ)
    (Qb : Matrix (Fin q) (Fin n) ℝ) (hG : (Qb * Qbᵀ).PosDef)
    (c' : ℝ) (hc' : (p * q : ℝ) / 2 < c') (w : ℝ) (hw : 0 < w)
    (s : Set (Fin p → Fin q → ℝ)) :
    ∫⁻ Γ in s,
        ENNReal.ofReal ((w + frobSq Apiv + frobSq (Ccross + (Matrix.of Γ) * Qb)) ^ (-c')) < ⊤ :=
  lt_of_le_of_lt
    (corankBlock_morsePeel_setLE Apiv Ccross Qb hG c' hc' w hw s) ENNReal.ofReal_lt_top

end DLNFibre.DLN.RLCT
