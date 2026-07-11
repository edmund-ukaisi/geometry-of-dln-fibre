import DLNFibre.DLN.RLCT.Validate.RouteMSJFreedPeel

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJInnerDescent` — reachable measure bedrock for the freed-`Γ` descent

**Thread `genm-sj5-descent`, buildplan §6 piece (b) — the reachable inner-`Γ`/domain-measure half.**
Bedrock for filling `innerCorankDescent_lt_top` (the §5 freed-`Γ` triple hole,
`RouteMSJDecoratedPeelStep`). Lands, sorry-free, the measure-theoretic primitives the inner-`Γ` layer
of the `(S,J)` descent consumes but which are NOT yet banked.

## What lands here (all sorry-free, axiom-clean)

* **`volume_genBox_lt_top`** — the entry box `genBox (Fin a) (Fin b) T` is a product of compact `Icc`s,
  hence finite volume (the `matBox_volume_lt_top` route at the `genBox` def).
* **`measure_shearbox_lt_top`** — the shear-image box `{Γ | Γ + schurShift x ∈ genBox (Fin a) (Fin b)
  T}` is a TRANSLATED product box (each coordinate `Γ i j ∈ [−T − s i j, T − s i j]`, `s = schurShift
  x`), hence still compact / finite volume. **This discharges the `hs : volume s < ⊤` obligation of the
  banked `freedSchurLoss_inner_bounded_lt_top` on the ACTUAL peel domain** — previously ASSUMED, since
  the shear domain depends on the outer `x`.
* **`freedSchurLoss_inner_bounded_le`** — the VALUE bound `∫_{Γ∈s} (freedSchurLoss x Γ Q)^{−c'} ≤
  (frobSq (P·Q̃ₚ))^{−c'} · volume s` (the first two calc steps of the banked `_bounded_lt_top`, kept as
  the explicit value the OUTER descent integrates rather than collapsed to `< ⊤`). The pivot energy
  `w = frobSq (P·Q̃ₚ)` lower-bounds `freedSchurLoss` (drop the nonneg corank term), so with `−c' ≤ 0`
  the integrand is bounded by the constant `w^{−c'}`.
* **`freedSchurLoss_inner_bounded_shear_lt_top`** — the banked bounded branch specialised to the peel's
  shear-image domain: per outer `(A',x)` with pivot energy `w > 0`, the inner `Γ`-integral over the
  actual shearbox is finite for any `c' ≥ 0`. Composes `freedSchurLoss_inner_bounded_lt_top` with
  `measure_shearbox_lt_top`.

## What is NOT here (the standing `(S,J)` double induction — the isolated hole)

These bank the inner-`Γ` / domain-measure primitives. They do NOT close the OUTER `(A', x)` integral:
that finiteness — the JOINT `{w = 0}` resolution (a.e.-positivity is insufficient; the outer integral
blows up as `w → 0`, design cert) and the ledger change-of-variables to `sjLoss_terminal` carrying the
accumulated Gram/pivot decoration — is the unbuilt `(S,J)` monomial double induction, left as the
isolated `innerCorankDescent_lt_top` `sorry` in `RouteMSJDecoratedPeelStep` (untracked; canonical stays
0-sorry).

S2-FREE: compact-box volume + the banked bounded branch; no `monomial_rlct`. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-! ## The entry box and the shear-image box have finite volume -/

/-- **The entry box `genBox (Fin a) (Fin b) T` has finite volume.** It is the product of compact
intervals `[−T, T]` over the `a · b` matrix entries (`isCompact_univ_pi`), so finite by
`IsCompact.measure_lt_top`. The `genBox` analogue of `matBox_volume_lt_top`. -/
theorem volume_genBox_lt_top {a b : ℕ} (T : ℝ) :
    volume (genBox (Fin a) (Fin b) T) < ⊤ := by
  have heq : genBox (Fin a) (Fin b) T
      = Set.univ.pi (fun _ : Fin a => Set.univ.pi (fun _ : Fin b => Set.Icc (-T) T)) := by
    ext X; simp only [genBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [heq]
  exact (isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))).measure_lt_top

/-- **The shear-image box has finite volume.** `{Γ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) T}` is
the translated product box `∏_{i,j} [−T − (schurShift x) i j, T − (schurShift x) i j]` (each coordinate
constraint `−T ≤ Γ i j + s i j ≤ T` is `−T − s i j ≤ Γ i j ≤ T − s i j`), a product of compact
intervals — finite volume. This is the domain the peel's inner `Γ`-integral runs over; it discharges
the `hs` obligation of `freedSchurLoss_inner_bounded_lt_top` on the real domain. -/
theorem measure_shearbox_lt_top {t a b : ℕ} (x : SJOuter t a b) (T : ℝ) :
    volume {Γ : Fin a → Fin b → ℝ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) T} < ⊤ := by
  have heq : {Γ : Fin a → Fin b → ℝ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) T}
      = Set.univ.pi (fun i : Fin a => Set.univ.pi (fun j : Fin b =>
          Set.Icc (-T - schurShift x i j) (T - schurShift x i j))) := by
    ext Γ
    simp only [genBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Pi.add_apply,
      Set.mem_Icc]
    constructor
    · intro h i j
      obtain ⟨h1, h2⟩ := h i j
      exact ⟨by linarith, by linarith⟩
    · intro h i j
      obtain ⟨h1, h2⟩ := h i j
      exact ⟨by linarith, by linarith⟩
  rw [heq]
  exact (isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))).measure_lt_top

/-! ## The inverse-free pivot energy (the `{w = 0}` locus is a clean bilinear condition) -/

/-- **The pivot energy is inverse-free.** For an invertible pivot `P`, the `P⁻¹` in the pivot block
`P · Q̃ₚ = P · (Q_p + P⁻¹·B₁₂·Q_b)` cancels: `P · Q̃ₚ = P·Q_p + B₁₂·Q_b`. So the pivot energy
`w = frobSq (P·Q̃ₚ) = frobSq (P·Q_p + B₁₂·Q_b)` is a bilinear form in `(P, B₁₂)` with NO matrix inverse —
`w = frobSq ([P | B₁₂] · Q)`, `[P | B₁₂]` the `t × M₁` front row and `Q` the `M₁`-row tail product. Its
zero locus `{w = 0} = {P·Q_p + B₁₂·Q_b = 0}` is therefore a clean bilinear condition (not a rational
one), which is what the JOINT `{w=0}` outer resolution reads. `P` is a unit on the peel domain
(`outerDom`'s `IsUnit` component), so this rewrite applies pointwise there. Proof: `mul_add` +
`Matrix.mul_nonsing_inv_cancel_left`. -/
theorem pivotEnergy_inverse_free {t b q : ℕ} (P : Matrix (Fin t) (Fin t) ℝ) (hP : IsUnit P)
    (B12 : Matrix (Fin t) (Fin b) ℝ) (Qp : Matrix (Fin t) (Fin q) ℝ) (Qb : Matrix (Fin b) (Fin q) ℝ) :
    P * (Qp + P⁻¹ * B12 * Qb) = P * Qp + B12 * Qb := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  rw [Matrix.mul_add]
  congr 1
  rw [Matrix.mul_assoc P⁻¹ B12 Qb]
  exact Matrix.mul_nonsing_inv_cancel_left P (B12 * Qb) hdet

/-! ## The bounded-branch value bound and its shear-domain specialisation -/

/-- **The bounded-branch VALUE bound.** For a fixed outer triple `x` and tail `Q`, over ANY domain `s`,
given the pivot energy `w = frobSq (P·Q̃ₚ)` strictly positive and `0 ≤ c'`, the freed corank integral is
bounded by the explicit value `w^{−c'} · volume s`. The pivot energy lower-bounds `freedSchurLoss` for
every `Γ` (drop the nonneg corank term), so with `−c' ≤ 0` the integrand is `≤` the constant `w^{−c'}`
(`Real.rpow_le_rpow_of_nonpos`) whose set-integral is `w^{−c'} · volume s`. This is the value the OUTER
`(S,J)` descent integrates on the `c' ≤ a·b/2` (atom-inapplicable) charts — the `< ⊤` collapse of the
banked `freedSchurLoss_inner_bounded_lt_top`, kept as a bound. -/
theorem freedSchurLoss_inner_bounded_le {t a b q : ℕ}
    (x : SJOuter t a b) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) (c' : ℝ) (hc0 : 0 ≤ c')
    (hpiv : 0 < frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)))
    (s : Set (Fin a → Fin b → ℝ)) :
    ∫⁻ Γ in s, ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c'))
      ≤ ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
          + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))) ^ (-c'))
        * volume s := by
  have hle : ∀ Γ : Fin a → Fin b → ℝ,
      frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
          + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
        ≤ freedSchurLoss x Γ Q := by
    intro Γ
    unfold freedSchurLoss
    exact le_add_of_nonneg_right (frobSq_nonneg _)
  calc ∫⁻ Γ in s, ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c'))
      ≤ ∫⁻ _Γ in s, ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))) ^ (-c')) := by
        refine lintegral_mono (fun Γ => ENNReal.ofReal_le_ofReal ?_)
        exact Real.rpow_le_rpow_of_nonpos hpiv (hle Γ) (neg_nonpos.mpr hc0)
    _ = ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))) ^ (-c'))
          * volume s := setLIntegral_const s _

/-- **The bounded branch on the actual shear-image peel domain.** For a fixed outer triple `x` and tail
`Q`, given the pivot energy `w = frobSq (P·Q̃ₚ)` strictly positive and `0 ≤ c'`, the freed inner
`Γ`-integral over the peel's shear-image box `{Γ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) T}` is
finite. Composes the banked `freedSchurLoss_inner_bounded_lt_top` with the shear-domain finite volume
`measure_shearbox_lt_top` — the peel-domain instance of the atom-inapplicable branch, with the domain
measurability/finiteness now discharged (not assumed). -/
theorem freedSchurLoss_inner_bounded_shear_lt_top {t a b q : ℕ}
    (x : SJOuter t a b) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) (c' : ℝ) (hc0 : 0 ≤ c')
    (hpiv : 0 < frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)))
    (T : ℝ) :
    ∫⁻ Γ in {Γ : Fin a → Fin b → ℝ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) T},
        ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c')) < ⊤ :=
  freedSchurLoss_inner_bounded_lt_top x Q c' hc0 hpiv _ (measure_shearbox_lt_top x T)

/-! ## The atom-branch value bound (the good-cell inner-Γ peel, kept as a value) -/

/-- **The atom-branch VALUE bound (the good-cell inner-Γ peel).** The `_le` value form of the banked
`freedSchurLoss_inner_peel_lt_top`: on the same interface (`c' > a·b/2`, coupling `Q_b Q_bᵀ` PosDef,
pivot energy `w = frobSq (P·Q̃ₚ) > 0`), the freed inner `Γ`-integral over ANY domain `s` is bounded by
the EXACT per-step atom value — the Gram Jacobian `det(Q_b Q_bᵀ)^{−a/2}` times the constant
`Cresid (a·b) c'` times the shifted core `(w + frobSq (C·Q̃ₚ·(I − P_{Q_b})))^{−(c' − a·b/2)}`,
`P_{Q_b} = Q_bᵀ (Q_b Q_bᵀ)⁻¹ Q_b`. Welds `freedSchurLoss` onto the atom shape (`Apiv := 0`,
`Ccross := C·Q̃ₚ`) exactly as `_peel_lt_top`, then applies the banked `corankBlock_morsePeel_setLE`
(the `≤`-value form) rather than the `< ⊤` collapse. **This is the value the OUTER `(S,J)` descent
integrates over `(A', x)` on the good (`c' > a·b/2`, full-rank) cells** — the Γ-block charge `a·b/2` is
peeled, the exponent shifts to `c' − a·b/2` on the reduced core, and the accumulated Gram divisor
`det(Q_b Q_bᵀ)^{−a/2}` rides into the ledger. The `frobSq (0 : …)` summand is `0` (`frobSq_empty_rows`),
kept only to match the banked atom shape verbatim; downstream may drop it. -/
theorem freedSchurLoss_inner_peel_le {t a b q : ℕ}
    (x : SJOuter t a b) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) (c' : ℝ)
    (hc' : (a * b : ℝ) / 2 < c')
    (hG : ((Q.submatrix Sum.inr id) * (Q.submatrix Sum.inr id)ᵀ).PosDef)
    (hpiv : 0 < frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)))
    (s : Set (Fin a → Fin b → ℝ)) :
    ∫⁻ Γ in s, ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c'))
      ≤ ENNReal.ofReal
          (((Q.submatrix Sum.inr id) * (Q.submatrix Sum.inr id)ᵀ).det ^ (-(a : ℝ) / 2)
            * Cresid (a * b) c'
            * (frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
                  + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
                + frobSq (0 : Matrix (Fin 0) (Fin q) ℝ)
                + frobSq (Matrix.of x.2 * (Q.submatrix Sum.inl id
                    + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)
                  * (1 - (Q.submatrix Sum.inr id)ᵀ
                      * ((Q.submatrix Sum.inr id) * (Q.submatrix Sum.inr id)ᵀ)⁻¹
                      * (Q.submatrix Sum.inr id))))
              ^ (-(c' - (a * b : ℝ) / 2))) := by
  have hatom := corankBlock_morsePeel_setLE
    (Apiv := (0 : Matrix (Fin 0) (Fin q) ℝ))
    (Ccross := Matrix.of x.2 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
    (Qb := Q.submatrix Sum.inr id) hG c' hc'
    (w := frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))) hpiv s
  rw [show (∫⁻ Γ in s, ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c')))
      = ∫⁻ Γ in s, ENNReal.ofReal
          ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
                + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
            + frobSq (0 : Matrix (Fin 0) (Fin q) ℝ)
            + frobSq (Matrix.of x.2 * (Q.submatrix Sum.inl id
                  + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)
                + (Matrix.of Γ) * Q.submatrix Sum.inr id)) ^ (-c')) from ?_]
  · exact hatom
  · refine lintegral_congr (fun Γ => ?_)
    congr 2
    rw [frobSq_empty_rows]
    unfold freedSchurLoss
    ring

end DLNFibre.DLN.RLCT
