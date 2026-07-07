import DLNFibre.DLN.RLCT.Validate.RadialResidualPower
import DLNFibre.DLN.RLCT.Validate.MatMulFibre

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual` — the corank-block residual-power atom

The **isotropic corank-block residual-power bound**: the general `p × q` matrix form of the banked
`radial_morse_residual_power_le` (which is stated for a flat `Fin (m+1) → ℝ` Morse block). For a
matrix block `D : Fin p → Fin q → ℝ` (the peel's corank block `Γ`) sitting on a strictly-positive
core value `w > 0` (the reduced top-`t`-rows loss `P_tail`), and `c'` above the block's Morse
threshold `pq/2`, the box integral carries a RESIDUAL POWER `w^{−(c' − pq/2)}` of the core:

    ∫_{[−T,T]^{p×q}} (frobSq D + w)^{−c'} dD  ≤  ofReal( Cresid (p·q) c' · w^{−(c' − pq/2)} ).

This is the exponent-SHIFTED corank-block peel: the `pq`-dim block `D` peels at threshold `pq/2` and
leaves the core at the shifted exponent `c'' = c' − pq/2` — Aoyagi's per-step exponent shift
`c' ↦ c' − ½(M₀−t)(M₁−t)` at the block dimension `a = (M₀−t)(M₁−t) = p·q` (`peelExp`). The reduction
is the measure-preserving flatten `Fin p → Fin q → ℝ ≃ᵐ Fin (p·q) → ℝ` (`eMatFlat`, the `2×2`→`Fin 4`
`e22` generalised), sending `frobSq D = ∑ₖ (eMatFlat D k)²` and `matBox p q T ↔ morseBox (p·q) T`, then
`radial_morse_residual_power_le`. S2-FREE (rides only the banked `RadialResidualPower` Japanese-bracket
finiteness).

## Scope — what this atom is, and is NOT (fidelity)

This is the **isotropic** corank residual: the corank block enters `frobSq D` (its own Frobenius norm).
In the general-`L` peel the corank block enters `frobSq (Γ · Q_bot)` — an **anisotropic** quadratic
form coupling to the tail's bottom rows `Q_bot`. This atom is the isotropic special case (`Q_bot`
regularised to isometry); recovering the anisotropic form is a linear change of variables `Γ ↦ Γ·Q_bot`
whose Jacobian is the coupling factor `P_full`-type term — the (S,J)-resolution content, NOT this atom.

## The unsound route this atom does NOT enable (finding, `genm-sjpeel-blow`)

The naive **pointwise-in-`A'`** inner-fibre bound
`∫_{A₀∈box} frobSq(A₀·Q)^{−c'} ≤ C·∑_t P_tail_t(Q)^{−(c'−a/2)}·P_full(Q)^{−a/2}` is FALSE for
`c' ≥ M₀/2` on (and near) the rank-deficient-`Q` locus: for rank-deficient `Q` the LHS DIVERGES (the
`A₀`-column integral `∫‖A₀·u‖^{−2c'}` over the rank direction `u` is non-integrable once `2c' ≥ M₀`),
while the RHS stays finite, so the ratio `→ ∞` approaching the locus and NO uniform `C` exists. Hence
`sjBoundaryPeel` CANNOT be discharged by `lintegral_mono_ae` on a pointwise bound (contra the first
design sketch); its honest proof is the per-pivot-chart radial blow-up **integrated over each chart**
(coupling `A₀` and `A'` — the (S,J) content), consuming this isotropic atom on the corank block after
the anisotropy is removed. (Analytic + numeric certificate: `r1u_pointwise_stress.py`; decorrelated
Codex xhigh corroboration: `codex/brick-answer.md`.)
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## The `p × q → Fin (p·q)` measure-preserving flatten (the `e22` generalisation) -/

/-- **The block flatten reindex** `((i : Fin p) × Fin q) ≃ Fin (p·q)` — the `sig22EquivFin4`
generalisation: `sigmaEquivProd` then `finProdFinEquiv` (no `finCongr`, the target is already `p·q`). -/
noncomputable def sigFlatEquiv (p q : ℕ) : ((_ : Fin p) × Fin q) ≃ Fin (p * q) :=
  (Equiv.sigmaEquivProd (Fin p) (Fin q)).trans finProdFinEquiv

/-- **The matrix-block flatten** `(Fin p → Fin q → ℝ) ≃ᵐ (Fin (p·q) → ℝ)` (MP), the `e22`
generalisation: `piCurry` (Sigma uncurry) then `arrowCongr'` (the `sigFlatEquiv` reindex). -/
noncomputable def eMatFlat (p q : ℕ) : (Fin p → Fin q → ℝ) ≃ᵐ (Fin (p * q) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin p) (_ : Fin q) => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr' (sigFlatEquiv p q) (MeasurableEquiv.refl ℝ))

/-- `eMatFlat p q D i = D ((sigFlatEquiv p q).symm i).1 ((sigFlatEquiv p q).symm i).2` (the flatten
reads the matrix entry at the decoded Sigma index). -/
theorem eMatFlat_apply (p q : ℕ) (D : Fin p → Fin q → ℝ) (i : Fin (p * q)) :
    eMatFlat p q D i = D ((sigFlatEquiv p q).symm i).1 ((sigFlatEquiv p q).symm i).2 := rfl

/-- `eMatFlat p q` is measure-preserving (`piCurry` MP then `arrowCongr'` MP). -/
theorem measurePreserving_eMatFlat (p q : ℕ) :
    MeasurePreserving (eMatFlat p q)
      (volume : Measure (Fin p → Fin q → ℝ)) (volume : Measure (Fin (p * q) → ℝ)) := by
  unfold eMatFlat
  refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr' (sigFlatEquiv p q)
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))
  exact (measurePreserving_piCurry (fun (_ : Fin p) (_ : Fin q) => ℝ)
    (fun _ _ => (volume : Measure ℝ))).symm _

/-- `frobSq D = ∑ₖ (eMatFlat p q D k)²` — the flatten reindexes the `p·q` entries (`Equiv.sum_comp`
over `sigFlatEquiv.symm`, then `Fintype.sum_sigma`). -/
theorem frobSq_eq_flatSum (p q : ℕ) (D : Fin p → Fin q → ℝ) :
    frobSq D = ∑ k, (eMatFlat p q D k) ^ 2 := by
  rw [show (∑ k, (eMatFlat p q D k) ^ 2)
      = ∑ k, (D ((sigFlatEquiv p q).symm k).1 ((sigFlatEquiv p q).symm k).2) ^ 2 from
    Finset.sum_congr rfl (fun k _ => by rw [eMatFlat_apply])]
  rw [Equiv.sum_comp (sigFlatEquiv p q).symm (fun kj : (_ : Fin p) × Fin q => (D kj.1 kj.2) ^ 2)]
  unfold frobSq
  rw [Fintype.sum_sigma]

/-- `matBox p q T = eMatFlat p q ⁻¹' morseBox (p·q) T` — the block box is the flat cube pulled back. -/
theorem matBox_eq_eMatFlat_preimage (p q : ℕ) (T : ℝ) :
    matBox p q T = eMatFlat p q ⁻¹' morseBox (p * q) T := by
  ext D
  simp only [matBox, morseBox, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    true_implies]
  constructor
  · intro h i; rw [eMatFlat_apply]; exact h _ _
  · intro h i j
    have := h (sigFlatEquiv p q ⟨i, j⟩)
    rw [eMatFlat_apply] at this
    simpa [Equiv.symm_apply_apply] using this

/-! ## The corank-block residual-power bound -/

/-- **The isotropic corank-block residual-power bound (S2-FREE) — the peel's Γ-block atom.** For a
`p × q` matrix block `D` (`p, q ≥ 1`) added to a strictly-positive core `w > 0`, with `c'` above the
block threshold `pq/2`, the box integral carries a residual power `w^{−(c' − pq/2)}` of the core:

    ∫_{matBox p q T} (frobSq D + w)^{−c'} dD  ≤  ofReal( Cresid (p·q) c' · w^{−(c' − pq/2)} ).

The `p × q → Fin (p·q)` measure-preserving flatten (`eMatFlat`, `frobSq_eq_flatSum`,
`matBox_eq_eMatFlat_preimage`) transports this to the banked flat Morse residual
`radial_morse_residual_power_le`. This is the exponent-shift `c' ↦ c' − ½·a` at block dimension
`a = p·q = (M₀−t)(M₁−t)` (`peelExp`). -/
theorem matBox_corank_residual_le (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (c' : ℝ)
    (hc' : (p * q : ℝ) / 2 < c') (T : ℝ) (hT : 0 < T) (w : ℝ) (hw : 0 < w) :
    ∫⁻ D in matBox p q T, ENNReal.ofReal ((frobSq D + w) ^ (-c'))
      ≤ ENNReal.ofReal (Cresid (p * q) c' * w ^ (-(c' - (p * q : ℝ) / 2))) := by
  obtain ⟨m, hm⟩ : ∃ m, p * q = m + 1 := ⟨p * q - 1, by have := Nat.mul_pos hp hq; omega⟩
  have hbridge : ((m : ℝ) + 1) = (p : ℝ) * (q : ℝ) := by
    rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, ← hm]; push_cast; ring
  -- transport the block box-lintegral onto the flat Morse box via `eMatFlat` (MP)
  have hmp := measurePreserving_eMatFlat p q
  have hpremeas : MeasurableSet (eMatFlat p q ⁻¹' morseBox (p * q) T) :=
    (morseBox_measurableSet (p * q) T).preimage (eMatFlat p q).measurable
  have hrwfrob : ∀ D : Fin p → Fin q → ℝ, ENNReal.ofReal ((frobSq D + w) ^ (-c'))
      = (fun x : Fin (p * q) → ℝ => ENNReal.ofReal ((∑ i, (x i) ^ 2 + w) ^ (-c'))) (eMatFlat p q D) :=
    fun D => by rw [frobSq_eq_flatSum p q D]
  calc ∫⁻ D in matBox p q T, ENNReal.ofReal ((frobSq D + w) ^ (-c'))
      = ∫⁻ x in morseBox (p * q) T, ENNReal.ofReal ((∑ i, (x i) ^ 2 + w) ^ (-c')) := by
        rw [matBox_eq_eMatFlat_preimage p q T,
          setLIntegral_congr_fun hpremeas (fun D _ => hrwfrob D),
          hmp.setLIntegral_comp_preimage_emb (eMatFlat p q).measurableEmbedding
            (fun x => ENNReal.ofReal ((∑ i, (x i) ^ 2 + w) ^ (-c'))) (morseBox (p * q) T)]
    _ = ∫⁻ x in morseBox (m + 1) T, ENNReal.ofReal ((∑ i, (x i) ^ 2 + w) ^ (-c')) := by rw [hm]
    _ ≤ ENNReal.ofReal (Cresid (m + 1) c' * w ^ (-(c' - (m + 1 : ℝ) / 2))) :=
        radial_morse_residual_power_le m c' (by rw [hbridge]; exact hc') T hT w hw
    _ = ENNReal.ofReal (Cresid (p * q) c' * w ^ (-(c' - (p * q : ℝ) / 2))) := by
        rw [hm, hbridge]

end DLNFibre.DLN.RLCT
