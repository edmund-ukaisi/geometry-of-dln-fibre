import DLNFibre.Core.Aoyagi.OrderChain
import DLNFibre.DLN.RLCT.Foundations.AdmTight
import DLNFibre.DLN.Aoyagi.ClosedForm
import DLNFibre.DLN.RLCT.Validate.MinAdmCCodim
import DLNFibre.Core.CThetaValue

/-!
# `DLN.Aoyagi.OrderRealizeSortedBox` — P6.2 Tier-3 (3a) SORTED-BOX CORE

The last factor of the realization order-iso: on **sorted** widths `D` (monotone, positive), the
poset of `Mval`-minimising admissible profiles is order-isomorphic to the box-partition lattice
`BoxPart ℓ a`, where `ℓ = qipM D` and `a = sbResidueA D` (Aoyagi's residue on the active prefix).

**Route (reuses the banked QIP water-filling — the pivotal fact is NOT re-derived).**
For monotone `D` the `MinAdmCCodim.eOfT/tOfE` maps give a value-preserving bijection
`Adm D ↔ qipFeasible D` with `Mval D T = Gqip D (eOfT D T)`; a *binding* profile's increment vector
`eOfT D T` is therefore a `Gqip`-minimiser, and `CThetaValue.sumSq_eq_abs_characterization` pins its
`qipT`-coordinates to `{0, sgn δ}` — the "binding steps are `{C−1, C}`" pivotal fact. The profile
order transports to the box order via the counting/position duality; the iso is assembled with
`OrderIso.ofHomInv` (monotone both ways + mutual inverse ⟹ order-iso, so the order-reflection
"hazard" is discharged for free).

**Upstream of `OrderRealize`.** This module imports only Core/Foundations/ClosedForm + the QIP
machinery (never `OrderRealize`), so `OrderRealize` can `import` it and discharge its
`bindingSet_sorted_orderIso_boxPart` sorry. The iso is stated over a general monotone-positive `D`
via the primitives (`Adm`/`Mval`/`BoxPart`/`qipM`); seat-E instantiates at `D = sortedWidths M`,
where `bindingSet (sortedWidths M)`, `ell M 0`, `residueA M 0` are defeq to the primitive forms.
-/

namespace DLNFibre.DLN.Aoyagi.SortedBox

open Finset
open DLNFibre.DLN.RLCT DLNFibre.Core DLNFibre.Core.Aoyagi.OrderChain

variable {L : ℕ}

/-! ## The active prefix ceiling `C` and residue `a` (matching `ClosedForm.ceilingM`/`residueA` at
`D = sortedWidths M`, `r = 0`) -/

/-- Aoyagi's ceiling `C = ⌈S/ℓ⌉ = (S + ℓ − 1) / ℓ` on the active prefix (`S = qipS D`,
`ℓ = qipM D`). Defeq to `ClosedForm.ceilingM M 0` at `D = sortedWidths M`. -/
noncomputable def sbCeil (D : Fin (L + 1) → ℕ) : ℤ :=
  (qipS D + (qipM D : ℤ) - 1) / (qipM D : ℤ)

/-- Aoyagi's residue `a = S − (C − 1)·ℓ` on the active prefix. Defeq to `ClosedForm.residueA M 0` at
`D = sortedWidths M`. -/
noncomputable def sbResidueA (D : Fin (L + 1) → ℕ) : ℤ :=
  qipS D - (sbCeil D - 1) * (qipM D : ℤ)

/-! ## Bridge: `eOfT` is the profile's descent-increment vector, and its `qipT` reads the step -/

/-- The **binding-minimiser structure** (the pivotal fact — Aoyagi Lemma 4–5, via the banked QIP
water-filling). For monotone `D` (`1 ≤ L`) and a binding profile `T` (admissible, `Mval`-minimal),
the increment vector `e = eOfT D T` is a `Gqip`-minimiser whose `qipT`-coordinates over the active
prefix `qipLow D` are `{0, sgn δ}`-valued with exactly `|δ|` nonzero — i.e. the active steps take
exactly two values. -/
theorem binding_qipT_pair (D : Fin (L + 1) → ℕ) (hmono : Monotone D) (hL : 1 ≤ L)
    (hne : (qipFeasible D).Nonempty) {T : Fin L → ℕ}
    (hT : T ∈ Adm D) (hbind : Mval D T = (Adm D).inf' (Adm_nonempty D) (Mval D)) :
    (∀ i ∈ qipLow D,
        qipT D (fun j ↦ (eOfT D T j : ℤ)) i = 0 ∨
        qipT D (fun j ↦ (eOfT D T j : ℤ)) i = (qipDelta D).sign) ∧
      ((qipLow D).filter (fun i ↦ qipT D (fun j ↦ (eOfT D T j : ℤ)) i ≠ 0)).card
        = (qipDelta D).natAbs := by
  -- `e := eOfT D T` is feasible and a `Gqip`-minimiser (`Gqip = cValue`).
  set e := eOfT D T with he
  have hfeas : e ∈ qipFeasible D := eOfT_mem_qipFeasible D hL hT
  have heq : Gqip D e = cValue D :=
    calc Gqip D e = Mval D T := (Mval_eq_Gqip D hmono hT).symm
      _ = (Adm D).inf' (Adm_nonempty D) (Mval D) := hbind
      _ = (qipFeasible D).inf' hne (Gqip D) :=
          inf'_Adm_Mval_eq_inf'_qipFeasible_Gqip D hmono hL hne
      _ = qipMin D hne := rfl
      _ = cValue D := qipMin_eq_cValue D hmono hne
  -- `e` is prefix-supported (`e i = 0` for `i ≥ m`), so `∑_{qipLow} e = D 0`.
  have hdrop := qipMinimiser_support D hmono hfeas heq
  have hfeasE : ∑ i, e i = D 0 := by
    simpa [qipFeasible, Finset.mem_finAntidiagonal] using hfeas
  have hsumLow : (∑ i ∈ qipLow D, (e i : ℤ)) = (D 0 : ℤ) := by
    have htail : (∑ i ∈ (qipLow D)ᶜ, (e i : ℤ)) = 0 := Finset.sum_eq_zero (fun i hi ↦ by
      simp only [qipLow, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] at hi
      simp only [hdrop i hi, Nat.cast_zero])
    have huniv : (∑ i, (e i : ℤ)) = (D 0 : ℤ) := by rw [← hfeasE]; push_cast; ring
    rw [← Finset.sum_add_sum_compl (qipLow D) (fun i ↦ (e i : ℤ)), htail, add_zero] at huniv
    exact huniv
  -- `∑_{qipLow} t = δ` and `∑_{qipLow} t² = |δ|`, so the equality case pins `t ∈ {0, sgn δ}`.
  have hsumT := sum_qipLow_qipT D (fun j ↦ (e j : ℤ)) hsumLow
  have hsqT := qipMinimiser_sumSq D hmono hL hfeas heq
  exact sumSq_eq_abs_characterization (qipLow D) (qipT D (fun j ↦ (e j : ℤ)))
    (qipDelta D) hsumT hsqT

/-! ## The order-isomorphism -/

/-- **THE SORTED-BOX ORDER-ISO** (general monotone-positive `D`). The binding-minimiser poset is
order-isomorphic to `BoxPart (qipM D) (sbResidueA D).toNat`. Seat-E instantiates at
`D = sortedWidths M` to discharge `OrderRealize.bindingSet_sorted_orderIso_boxPart` (all three of
`bindingSet (sortedWidths M)`, `ell M 0`, `residueA M 0` are defeq to the primitive forms here). -/
theorem sortedBox_orderIso (D : Fin (L + 1) → ℕ) (hmono : Monotone D) (hpos : ∀ s, 0 < D s) :
    Nonempty (↥{T : Fin L → ℕ | T ∈ Adm D ∧ Mval D T = (Adm D).inf' (Adm_nonempty D) (Mval D)}
      ≃o ↥(BoxPart (qipM D) ((sbResidueA D).toNat))) := by
  sorry -- map: enc-sorted-box (assembly)

end DLNFibre.DLN.Aoyagi.SortedBox
