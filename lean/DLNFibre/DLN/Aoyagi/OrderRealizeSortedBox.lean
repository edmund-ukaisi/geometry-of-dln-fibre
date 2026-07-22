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

/-- **Sign bridge (ceiling).** `C = qipRound + [δ > 0]`: the active-prefix ceiling is the QIP
rounding centre, bumped by one exactly when the residue is strictly positive (`⌈S/ℓ⌉` vs the nearest
integer `⌊S/ℓ + ½⌋`). Confines the `δ`-sign case-split; everything downstream is sign-free. -/
theorem sbCeil_eq (D : Fin (L + 1) → ℕ) (hN : 1 ≤ L) :
    sbCeil D = qipRound D + (if 0 < qipDelta D then 1 else 0) := by
  have hℓ1 : 1 ≤ qipM D := qipM_ge_one D hN
  rw [sbCeil]
  set ℓ : ℤ := (qipM D : ℤ) with hℓdef
  have hℓpos : 0 < ℓ := by rw [hℓdef]; exact_mod_cast hℓ1
  set q := qipRound D with hq
  set δ := qipDelta D with hδ
  have hSeq : qipS D = ℓ * q + δ := by rw [hδ, qipDelta, ← hℓdef, ← hq]; ring
  have hb := two_qipDelta_bounds D hN
  rw [← hℓdef, ← hδ] at hb
  by_cases hpos : 0 < δ
  · rw [if_pos hpos]
    exact (Int.ediv_emod_unique hℓpos (r := δ - 1) (q := q + 1)).mpr
      ⟨by rw [hSeq]; ring, by omega, by omega⟩ |>.1
  · rw [if_neg hpos, add_zero]
    exact (Int.ediv_emod_unique hℓpos (r := δ + ℓ - 1) (q := q)).mpr
      ⟨by rw [hSeq]; ring, by omega, by omega⟩ |>.1

/-- **Sign bridge (residue).** `a = δ + [δ ≤ 0]·ℓ`: `a = δ` when `δ > 0`, `a = δ + ℓ = ℓ − |δ|` when
`δ ≤ 0`. Hence `1 ≤ a ≤ ℓ`. Follows from `sbCeil_eq` by algebra. -/
theorem sbResidueA_eq (D : Fin (L + 1) → ℕ) (hN : 1 ≤ L) :
    sbResidueA D = qipDelta D + (if 0 < qipDelta D then 0 else (qipM D : ℤ)) := by
  rw [sbResidueA, sbCeil_eq D hN]
  by_cases hpos : 0 < qipDelta D
  · rw [if_pos hpos, if_pos hpos, qipDelta]; ring
  · rw [if_neg hpos, if_neg hpos, qipDelta]; ring

/-! ## Bridge: `eOfT` is the profile's descent-increment vector, and its `qipT` reads the step -/

/-- A binding profile's increment vector `eOfT D T` is feasible and a `Gqip`-minimiser
(`Gqip = cValue`): `Mval D T = Gqip D (eOfT D T)` (`Mval_eq_Gqip`) meets `minAdm = qipMin = cValue`. -/
theorem binding_minimiser (D : Fin (L + 1) → ℕ) (hmono : Monotone D) (hL : 1 ≤ L)
    (hne : (qipFeasible D).Nonempty) {T : Fin L → ℕ}
    (hT : T ∈ Adm D) (hbind : Mval D T = (Adm D).inf' (Adm_nonempty D) (Mval D)) :
    eOfT D T ∈ qipFeasible D ∧ Gqip D (eOfT D T) = cValue D := by
  refine ⟨eOfT_mem_qipFeasible D hL hT, ?_⟩
  calc Gqip D (eOfT D T) = Mval D T := (Mval_eq_Gqip D hmono hT).symm
    _ = (Adm D).inf' (Adm_nonempty D) (Mval D) := hbind
    _ = (qipFeasible D).inf' hne (Gqip D) :=
        inf'_Adm_Mval_eq_inf'_qipFeasible_Gqip D hmono hL hne
    _ = qipMin D hne := rfl
    _ = cValue D := qipMin_eq_cValue D hmono hne

/-- A binding profile's increments vanish past the active prefix: `eOfT D T i = 0` for `i ≥ ℓ`
(the minimiser drops to the `m`-face). -/
theorem binding_support (D : Fin (L + 1) → ℕ) (hmono : Monotone D) (hL : 1 ≤ L)
    (hne : (qipFeasible D).Nonempty) {T : Fin L → ℕ}
    (hT : T ∈ Adm D) (hbind : Mval D T = (Adm D).inf' (Adm_nonempty D) (Mval D)) :
    ∀ i : Fin L, qipM D ≤ (i : ℕ) → eOfT D T i = 0 := by
  obtain ⟨hfeas, heq⟩ := binding_minimiser D hmono hL hne hT hbind
  exact qipMinimiser_support D hmono hfeas heq

/-- The **binding-minimiser structure** (the pivotal fact — Aoyagi Lemma 4–5, via the banked QIP
water-filling). For monotone `D` (`1 ≤ L`) and a binding profile `T` (admissible, `Mval`-minimal),
the increment vector `e = eOfT D T` has `qipT`-coordinates over the active prefix `qipLow D` that are
`{0, sgn δ}`-valued with exactly `|δ|` nonzero — i.e. the active steps take exactly two values. -/
theorem binding_qipT_pair (D : Fin (L + 1) → ℕ) (hmono : Monotone D) (hL : 1 ≤ L)
    (hne : (qipFeasible D).Nonempty) {T : Fin L → ℕ}
    (hT : T ∈ Adm D) (hbind : Mval D T = (Adm D).inf' (Adm_nonempty D) (Mval D)) :
    (∀ i ∈ qipLow D,
        qipT D (fun j ↦ (eOfT D T j : ℤ)) i = 0 ∨
        qipT D (fun j ↦ (eOfT D T j : ℤ)) i = (qipDelta D).sign) ∧
      ((qipLow D).filter (fun i ↦ qipT D (fun j ↦ (eOfT D T j : ℤ)) i ≠ 0)).card
        = (qipDelta D).natAbs := by
  obtain ⟨hfeas, heq⟩ := binding_minimiser D hmono hL hne hT hbind
  set e := eOfT D T with he
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
  have hsumT := sum_qipLow_qipT D (fun j ↦ (e j : ℤ)) hsumLow
  have hsqT := qipMinimiser_sumSq D hmono hL hfeas heq
  exact sumSq_eq_abs_characterization (qipLow D) (qipT D (fun j ↦ (e j : ℤ)))
    (qipDelta D) hsumT hsqT

/-! ## The C-step subset and the profile-counting formula -/

/-- The **C-step subset** `A(T) ⊆ Fin L`: active-prefix indices `i < ℓ` whose step
`eOfT D T i + D_{i+1}` equals the ceiling `C`. On a binding profile `|A(T)| = a` (`stepA_card`). -/
noncomputable def stepA (D : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Finset (Fin L) :=
  (qipLow D).filter (fun i ↦ (eOfT D T i : ℤ) + (D i.succ : ℤ) = sbCeil D)

/-- The minimiser-independent **base increment** `w_j = (C − 1) − D_{j+1}` on the active prefix, `0`
off it. A binding profile's increment is `eOfT D T j = w_j + [j ∈ A(T)]` (`binding_incr_eq`). -/
noncomputable def wBase (D : Fin (L + 1) → ℕ) (j : Fin L) : ℤ :=
  if (j : ℕ) < qipM D then sbCeil D - 1 - (D j.succ : ℤ) else 0

/-- **The active step lies in `{C−1, C}`** on a binding profile (Aoyagi's two-value staircase). -/
theorem binding_sStep_bounds (D : Fin (L + 1) → ℕ) (hmono : Monotone D) (hL : 1 ≤ L)
    (hne : (qipFeasible D).Nonempty) {T : Fin L → ℕ}
    (hT : T ∈ Adm D) (hbind : Mval D T = (Adm D).inf' (Adm_nonempty D) (Mval D))
    {i : Fin L} (hi : i ∈ qipLow D) :
    sbCeil D - 1 ≤ (eOfT D T i : ℤ) + (D i.succ : ℤ) ∧
      (eOfT D T i : ℤ) + (D i.succ : ℤ) ≤ sbCeil D := by
  have hpair := (binding_qipT_pair D hmono hL hne hT hbind).1 i hi
  have hCe := sbCeil_eq D hL
  set s : ℤ := (eOfT D T i : ℤ) + (D i.succ : ℤ) with hs
  have hqt : qipT D (fun j ↦ (eOfT D T j : ℤ)) i = s - qipRound D := by rw [hs]; rfl
  rw [hqt] at hpair
  by_cases hd : 0 < qipDelta D
  · rw [if_pos hd] at hCe
    rw [Int.sign_eq_one_of_pos hd] at hpair
    rcases hpair with h | h <;> omega
  · rw [if_neg hd] at hCe
    have hsgn : (qipDelta D).sign = -1 ∨ (qipDelta D).sign = 0 := by
      rcases lt_trichotomy (qipDelta D) 0 with h1 | h1 | h1
      · exact Or.inl (Int.sign_eq_neg_one_of_neg h1)
      · exact Or.inr (by rw [h1]; rfl)
      · exact absurd h1 hd
    rcases hpair with h | h
    · omega
    · rcases hsgn with hs' | hs' <;> rw [hs'] at h <;> omega

/-- **Partial telescoping.** The prefix sum of the descent increments `eOfT D T` over `Iic c`
recovers the profile: `∑_{j ≤ c} eOfT D T j = D₀ − T_c` (the reverse round-trip of `tOfE`, localised
to a prefix). Over `ℤ` (honest differences on `Adm`, via `eOfT_cast`). -/
theorem prefix_telescope (D : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hT : T ∈ Adm D) :
    ∀ (n : ℕ) (hn : n < L),
      (∑ j ∈ Finset.Iic (⟨n, hn⟩ : Fin L), (eOfT D T j : ℤ)) = (D 0 : ℤ) - (T ⟨n, hn⟩ : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro hn
    have hsing : Finset.Iic (⟨0, hn⟩ : Fin L) = {⟨0, hn⟩} := by
      have hv : (⟨0, hn⟩ : Fin L).val = 0 := rfl
      ext x
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    rw [hsing, Finset.sum_singleton, eOfT_cast D hT]
    have h1 : expSurvivor D T (⟨0, hn⟩ : Fin L).castSucc = D 0 := by
      rw [show (⟨0, hn⟩ : Fin L).castSucc = (0 : Fin (L + 1)) from Fin.ext (by simp)]
      exact expSurvivor_zero D T
    have h2 : expSurvivor D T (⟨0, hn⟩ : Fin L).succ = T ⟨0, hn⟩ := expSurvivor_succ D T _
    rw [h1, h2]
  | succ m ih =>
    intro hn
    have hm : m < L := by omega
    have hv1 : (⟨m + 1, hn⟩ : Fin L).val = m + 1 := rfl
    have hv2 : (⟨m, hm⟩ : Fin L).val = m := rfl
    have hins : Finset.Iic (⟨m + 1, hn⟩ : Fin L)
        = insert (⟨m + 1, hn⟩ : Fin L) (Finset.Iic (⟨m, hm⟩ : Fin L)) := by
      ext x
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
      omega
    have hnotmem : (⟨m + 1, hn⟩ : Fin L) ∉ Finset.Iic (⟨m, hm⟩ : Fin L) := by
      simp only [Finset.mem_Iic, Fin.le_def]; omega
    rw [hins, Finset.sum_insert hnotmem, ih hm, eOfT_cast D hT]
    have h1 : expSurvivor D T (⟨m + 1, hn⟩ : Fin L).castSucc = T ⟨m, hm⟩ := by
      rw [show (⟨m + 1, hn⟩ : Fin L).castSucc = (⟨m, hm⟩ : Fin L).succ from Fin.ext (by simp)]
      exact expSurvivor_succ D T _
    have h2 : expSurvivor D T (⟨m + 1, hn⟩ : Fin L).succ = T ⟨m + 1, hn⟩ := expSurvivor_succ D T _
    rw [h1, h2]; ring

/-- Prefix-sum form for a general `c : Fin L`. -/
theorem prefix_telescope' (D : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hT : T ∈ Adm D) (c : Fin L) :
    (∑ j ∈ Finset.Iic c, (eOfT D T j : ℤ)) = (D 0 : ℤ) - (T c : ℤ) := by
  have := prefix_telescope D hT c.val c.isLt
  simpa using this

/-- **Increment decomposition.** On a binding profile, every descent increment splits into the
minimiser-independent base plus the C-step indicator: `eOfT D T j = wBase D j + [j ∈ A(T)]`. -/
theorem binding_incr_eq (D : Fin (L + 1) → ℕ) (hmono : Monotone D) (hL : 1 ≤ L)
    (hne : (qipFeasible D).Nonempty) {T : Fin L → ℕ}
    (hT : T ∈ Adm D) (hbind : Mval D T = (Adm D).inf' (Adm_nonempty D) (Mval D)) (j : Fin L) :
    (eOfT D T j : ℤ) = wBase D j + (if j ∈ stepA D T then 1 else 0) := by
  by_cases hjlow : (j : ℕ) < qipM D
  · have hjL : j ∈ qipLow D := by simp [qipLow, Finset.mem_filter, hjlow]
    have hb := binding_sStep_bounds D hmono hL hne hT hbind hjL
    have hw : wBase D j = sbCeil D - 1 - (D j.succ : ℤ) := by simp only [wBase, if_pos hjlow]
    by_cases hjA : j ∈ stepA D T
    · have hC : (eOfT D T j : ℤ) + (D j.succ : ℤ) = sbCeil D := (Finset.mem_filter.mp hjA).2
      rw [if_pos hjA, hw]; omega
    · have hCne : (eOfT D T j : ℤ) + (D j.succ : ℤ) ≠ sbCeil D := fun hC ↦
        hjA (Finset.mem_filter.mpr ⟨hjL, hC⟩)
      rw [if_neg hjA, hw]; omega
  · have hw : wBase D j = 0 := by simp only [wBase, if_neg hjlow]
    have hsupp : eOfT D T j = 0 := binding_support D hmono hL hne hT hbind j (by omega)
    have hjA : j ∉ stepA D T := fun h ↦ hjlow (by
      have := (Finset.mem_filter.mp h).1
      simpa only [qipLow, Finset.mem_filter, Finset.mem_univ, true_and] using this)
    rw [if_neg hjA, hw, hsupp]; simp

/-- **The profile-counting formula.** On a binding profile, the profile value is the corner `D₀`
minus the fixed base prefix minus the number of C-steps at or before `c`:
`T_c = D₀ − ∑_{j ≤ c} wBase j − |A(T) ∩ Iic c|`. Since the base is minimiser-independent, the
profile order becomes reverse count-domination (`binding_le_iff`). -/
theorem binding_profile_formula (D : Fin (L + 1) → ℕ) (hmono : Monotone D) (hL : 1 ≤ L)
    (hne : (qipFeasible D).Nonempty) {T : Fin L → ℕ}
    (hT : T ∈ Adm D) (hbind : Mval D T = (Adm D).inf' (Adm_nonempty D) (Mval D)) (c : Fin L) :
    (T c : ℤ) = (D 0 : ℤ) - (∑ j ∈ Finset.Iic c, wBase D j)
      - ((stepA D T ∩ Finset.Iic c).card : ℤ) := by
  have htel := prefix_telescope' D hT c
  have hcount : (∑ j ∈ Finset.Iic c, (if j ∈ stepA D T then (1 : ℤ) else 0))
      = ((stepA D T ∩ Finset.Iic c).card : ℤ) := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  have hsplit : (∑ j ∈ Finset.Iic c, (eOfT D T j : ℤ))
      = (∑ j ∈ Finset.Iic c, wBase D j) + ((stepA D T ∩ Finset.Iic c).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun j _ ↦ binding_incr_eq D hmono hL hne hT hbind j),
      Finset.sum_add_distrib, hcount]
  linarith [htel, hsplit]

/-- **The C-step count is the residue.** `|A(T)| = a` on a binding profile: the active steps split
into `a` copies of `C` and `ℓ − a` copies of `C − 1` (via the `{0, sgn δ}` count). -/
theorem stepA_card (D : Fin (L + 1) → ℕ) (hmono : Monotone D) (hL : 1 ≤ L)
    (hne : (qipFeasible D).Nonempty) {T : Fin L → ℕ}
    (hT : T ∈ Adm D) (hbind : Mval D T = (Adm D).inf' (Adm_nonempty D) (Mval D)) :
    (stepA D T).card = (sbResidueA D).toNat := by
  obtain ⟨hchar, hcount⟩ := binding_qipT_pair D hmono hL hne hT hbind
  have hCe := sbCeil_eq D hL
  have hres := sbResidueA_eq D hL
  have habs : |qipDelta D| ≤ (qipM D : ℤ) := abs_qipDelta_le_m D hL
  have hℓcard : (qipLow D).card = qipM D := qipLow_card D
  -- `stepA = {i ∈ qipLow : qipT i = [δ>0]}`.
  have hstepA : stepA D T
      = (qipLow D).filter (fun i ↦ qipT D (fun j ↦ (eOfT D T j : ℤ)) i
          = (if 0 < qipDelta D then (1 : ℤ) else 0)) := by
    apply Finset.filter_congr
    intro i _
    have hqt : qipT D (fun j ↦ (eOfT D T j : ℤ)) i
        = ((eOfT D T i : ℤ) + (D i.succ : ℤ)) - qipRound D := rfl
    rw [hqt, hCe]
    set k : ℤ := (if 0 < qipDelta D then (1 : ℤ) else 0)
    constructor <;> intro h <;> omega
  rw [hstepA]
  by_cases hd : 0 < qipDelta D
  · -- `δ > 0`: `{qipT = 1} = {qipT ≠ 0}`, card `= |δ| = a`.
    simp only [if_pos hd]
    have hnz : (qipLow D).filter (fun i ↦ qipT D (fun j ↦ (eOfT D T j : ℤ)) i = (1 : ℤ))
        = (qipLow D).filter (fun i ↦ qipT D (fun j ↦ (eOfT D T j : ℤ)) i ≠ 0) := by
      apply Finset.filter_congr
      intro i hi
      rcases hchar i hi with h | h
      · omega
      · rw [Int.sign_eq_one_of_pos hd] at h; omega
    rw [hnz, hcount]
    have hsr : sbResidueA D = qipDelta D := by rw [hres, if_pos hd]; ring
    rw [hsr]; omega
  · -- `δ ≤ 0`: `{qipT = 0}`, card `= ℓ − |δ| = a`.
    simp only [if_neg hd]
    have hpart := Finset.card_filter_add_card_filter_not (s := qipLow D)
      (p := fun i ↦ qipT D (fun j ↦ (eOfT D T j : ℤ)) i = 0)
    have heq2 : (qipLow D).filter (fun i ↦ ¬ (qipT D (fun j ↦ (eOfT D T j : ℤ)) i = 0))
        = (qipLow D).filter (fun i ↦ qipT D (fun j ↦ (eOfT D T j : ℤ)) i ≠ 0) := rfl
    rw [heq2, hcount, hℓcard] at hpart
    have hsr : sbResidueA D = qipDelta D + (qipM D : ℤ) := by rw [hres, if_neg hd]
    omega

/-- **Profile order = reverse count-domination.** On binding profiles `T, T'`, the pointwise order
`T ≤ T'` holds iff at every prefix `T'` has no more C-steps than `T`
(`|A(T') ∩ Iic c| ≤ |A(T) ∩ Iic c|`). The base prefix cancels in `binding_profile_formula`. -/
theorem binding_le_iff (D : Fin (L + 1) → ℕ) (hmono : Monotone D) (hL : 1 ≤ L)
    (hne : (qipFeasible D).Nonempty) {T T' : Fin L → ℕ}
    (hT : T ∈ Adm D) (hbind : Mval D T = (Adm D).inf' (Adm_nonempty D) (Mval D))
    (hT' : T' ∈ Adm D) (hbind' : Mval D T' = (Adm D).inf' (Adm_nonempty D) (Mval D)) :
    (∀ c, T c ≤ T' c) ↔
      ∀ c, (stepA D T' ∩ Finset.Iic c).card ≤ (stepA D T ∩ Finset.Iic c).card := by
  constructor
  · intro h c
    have hf := binding_profile_formula D hmono hL hne hT hbind c
    have hf' := binding_profile_formula D hmono hL hne hT' hbind' c
    have hle : (T c : ℤ) ≤ (T' c : ℤ) := by exact_mod_cast h c
    have : ((stepA D T' ∩ Finset.Iic c).card : ℤ) ≤ ((stepA D T ∩ Finset.Iic c).card : ℤ) := by
      linarith
    exact_mod_cast this
  · intro h c
    have hf := binding_profile_formula D hmono hL hne hT hbind c
    have hf' := binding_profile_formula D hmono hL hne hT' hbind' c
    have hc : ((stepA D T' ∩ Finset.Iic c).card : ℤ) ≤ ((stepA D T ∩ Finset.Iic c).card : ℤ) := by
      exact_mod_cast h c
    have : (T c : ℤ) ≤ (T' c : ℤ) := by linarith
    exact_mod_cast this

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
