import DLNFibre.Core.CThetaValue
import DLNFibre.Core.CThetaQIPConverse

/-!
# `DLNFibre.Core.CThetaThetaBridge` — `θ` at the Kostant layer: `numTop d 0 = cTheta d`

The paper's `θ` (Lehalleur–Rimányi 2024) is the number of **top-dimensional components** of the
zero-product locus, defined combinatorially as the **Kostant-side** minimiser count
`Core.CTheta.numTop d 0` (the number of Kostant partitions of `d` with corner `0` whose `codimForm`
attains `cCodim d 0`). The QIP/closed-form tide proved `θ = C(m, |δ|)` at the **QIP layer**
(`Core.CThetaValue.qipNumMinimisers_eq_cTheta`, counting `Gqip`-minimisers `e`). This file closes
the layer gap: for weakly-increasing `d`, the two minimiser counts coincide, so the paper's
Kostant-side `θ = numTop d 0` is the closed form `cTheta d`.

**The bridge.** For `Monotone d` the substitution `mOfE d e` (`Core.CThetaQIP`) and its inverse
`eOfm` on horizontal-lace partitions (`Core.CThetaQIPConverse`) are a value-preserving bijection

$$ \{\text{Kostant minimisers}\}\ \xrightarrow{\ \cong\ }\ \{\text{QIP minimisers}\},
   \qquad m \mapsto \mathrm{eOfm}\,m,\quad e \mapsto \mathrm{mOfE}\,d\,e. $$

The two sides have **equal cardinality** by `Finset.card_bij'`:
* `cCodim d 0 = qipMin d` (the QIP value equality, `cCodim_eq_qipMin`), so the two minimiser
  *predicates* agree across the bijection;
* a Kostant minimiser is horizontal-lace (`minimiser_isHL`), hence in the `mOfE`-image with witness
  `eOfm m` (`mOfE_surj_of_hl`), giving `mOfE d (eOfm m) = m` (the left inverse);
* `eOfm (mOfE d e) = e` always (`mOfE`'s low column reads `e` back, `eOfm_mOfE`), the right inverse;
* `codimForm (mOfE d e) = Gqip d e` (`codimForm_mOfE`) carries minimiser ↔ minimiser.

Composing the count equality with `qipNumMinimisers_eq_cTheta` gives `numTop d 0 = cTheta d`.

**Scope (name = content).** This is the **combinatorial** `θ`: a minimiser count of a ℤ-quadratic
form over Kostant partitions. The **aggregate** geometric reading — `θ` as the count of
top-dimensional GEOMETRIC components of the closed locus `Σ̄^r` — is PROVED:
`numTop d r = #{top-dimensional irreducible components of Σ̄^r}`
(`Core.CCodimZeroStrict.numTop_eq_ncard_topComponents`, unconditional), over the orbit
stratification (`Core.SigmaStratification` / `Core.SigmaComponents`); the per-orbit codimension
reading is PROVED in `Core.CThetaGeometric` (the discharged Voigt lemma). Nothing here asserts those
geometric readings directly. The nonemptiness bridge `kostant_nonempty_iff_qipFeasible_nonempty`
lets the two `Nonempty` hypotheses pass between layers.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Finset

variable {N : ℕ}

/-! ## The right inverse `eOfm (mOfE d e) = e` and the nonemptiness bridge -/

/-- **`eOfm` inverts `mOfE` on the nose.** `eOfm (mOfE d e) = e` for every `e`: `eOfm m i` reads
the low column `m (0, i.castSucc)`, which on `mOfE d e` is the first branch (value `e i`). No
hypotheses. -/
theorem eOfm_mOfE (d : Fin (N + 1) → ℕ) (e : Fin N → ℕ) : eOfm (mOfE d e) = e := by
  funext i
  have hi : ((i.castSucc : Fin (N + 1)) : ℕ) < N := by rw [Fin.val_castSucc]; exact i.isLt
  rw [eOfm, mOfE_zero_lt hi]
  congr 1

/-- **Nonemptiness bridge.** For weakly-increasing `d`, the Kostant partitions of `d` with corner
`0` are nonempty iff the QIP feasible set is: `mOfE d e` (feasible `e`) ∈ Kostant, and `eOfm m` is
feasible for any Kostant `m` (corner-`0` ⟹ `∑ eOfm = d 0`; no HL needed — `eOfm` feasibility holds
for every Kostant `m`). -/
theorem kostant_nonempty_iff_qipFeasible_nonempty (d : Fin (N + 1) → ℕ) (hd : Monotone d) :
    (kostantPartitions d 0).Nonempty ↔ (qipFeasible d).Nonempty := by
  constructor
  · rintro ⟨m, hm⟩
    -- `eOfm m` is feasible: `∑ eOfm m = d 0` by `kostantAt … 0` (corner `0` drops the last term).
    refine ⟨eOfm m, ?_⟩
    rw [qipFeasible, Finset.mem_finAntidiagonal]
    rw [mem_kostantPartitions] at hm
    obtain ⟨-, -, hk, hcorner⟩ := hm
    have h0 := hk 0
    rw [kostantAt] at h0
    have hfilter : (Finset.univ.filter
          (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ 0 ∧ (0 : Fin (N + 1)) ≤ p.2))
        = Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 = 0) := by
      apply Finset.filter_congr; intro p _
      simp only [Fin.le_zero_iff, Fin.zero_le, and_true]
    rw [hfilter] at h0
    have hsum : (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 = 0), m p)
        = ∑ b : Fin (N + 1), m (0, b) := by
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (0 : Fin (N + 1))]
      · simp
      · intro x _ hx; rw [Finset.sum_eq_zero]; intro b _; rw [if_neg (by simp [hx])]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, Fin.sum_univ_castSucc, hcorner, add_zero] at h0
    simp only [eOfm]; exact h0.symm
  · rintro ⟨e, he⟩
    rw [qipFeasible, Finset.mem_finAntidiagonal] at he
    exact ⟨mOfE d e, mOfE_mem d hd he⟩

/-! ## The minimiser-count bridge and the closed form for `θ` -/

/-- **The minimiser counts coincide.** For weakly-increasing `d`, the number of Kostant minimisers
equals the number of QIP minimisers: the value-preserving bijection `m ↔ e` (HL ⟷ feasible). -/
theorem numTop_zero_card_eq_qipNumMinimisers (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (hk : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty) :
    ((kostantPartitions d 0).filter (fun m ↦ codimForm N (extendℤ m) = cCodim d 0 hk)).card
      = ((qipFeasible d).filter (fun e ↦ Gqip d e = qipMin d hne)).card := by
  refine Finset.card_bij'
    (fun m _ ↦ eOfm m) (fun e _ ↦ mOfE d e) ?_ ?_ ?_ ?_
  · -- forward: a Kostant minimiser maps to a QIP minimiser.
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmem, hmin⟩ := hm
    have hHL : IsHL m := minimiser_isHL d hd hk hmem hmin
    obtain ⟨e, he, hme⟩ := mOfE_surj_of_hl d hd hmem hHL
    -- the surjectivity witness is `eOfm m`: `e = eOfm m` since `mOfE d e = m`.
    have heeq : eOfm m = e := by rw [← hme, eOfm_mOfE]
    change eOfm m ∈ (qipFeasible d).filter (fun e ↦ Gqip d e = qipMin d hne)
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [qipFeasible, Finset.mem_finAntidiagonal, heeq]; exact he
    · rw [heeq, ← codimForm_mOfE d hd e, hme, hmin, cCodim_eq_qipMin d hd hk hne]
  · -- inverse: a QIP minimiser maps to a Kostant minimiser.
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hfeas, hmin⟩ := he
    have hfeas' : ∑ i, e i = d 0 := by
      rw [qipFeasible, Finset.mem_finAntidiagonal] at hfeas; exact hfeas
    change mOfE d e ∈ (kostantPartitions d 0).filter
      (fun m ↦ codimForm N (extendℤ m) = cCodim d 0 hk)
    rw [Finset.mem_filter]
    refine ⟨mOfE_mem d hd hfeas', ?_⟩
    rw [codimForm_mOfE d hd e, hmin, cCodim_eq_qipMin d hd hk hne]
  · -- left inverse: `mOfE d (eOfm m) = m` for a Kostant minimiser `m` (HL ⟹ in `mOfE`-image).
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmem, hmin⟩ := hm
    have hHL : IsHL m := minimiser_isHL d hd hk hmem hmin
    obtain ⟨e, he, hme⟩ := mOfE_surj_of_hl d hd hmem hHL
    have heeq : eOfm m = e := by rw [← hme, eOfm_mOfE]
    change mOfE d (eOfm m) = m
    rw [heeq, hme]
  · -- right inverse: `eOfm (mOfE d e) = e` (always).
    intro e _
    change eOfm (mOfE d e) = e
    exact eOfm_mOfE d e

/-- **The paper's `θ` is the closed form (Thm 7.10, `r = 0`, Kostant layer).** For weakly-increasing
`d`, the Kostant-side component count `numTop d 0` equals `θ = C(m, |δ|)` (`cTheta d`). Routes
through the minimiser-count bridge `numTop_zero_card_eq_qipNumMinimisers` and the QIP-layer count
`qipNumMinimisers_eq_cTheta`. The aggregate geometric reading (top components of `Σ⁰`) stays open
per the `Core.CThetaGeometric` roadmap. -/
theorem numTop_zero_eq_cTheta (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (hk : (kostantPartitions d 0).Nonempty) : numTop d 0 hk = cTheta d := by
  have hne : (qipFeasible d).Nonempty :=
    (kostant_nonempty_iff_qipFeasible_nonempty d hd).mp hk
  rw [numTop, numTop_zero_card_eq_qipNumMinimisers d hd hk hne,
    qipNumMinimisers_eq_cTheta d hd hne]

/-! ## Witnesses — `θ = cTheta` computes at the paper's examples

`(2,2,2)` (Ex 4.3/6.2): `θ = numTop d222 0 = 1 = cTheta d222`. `d639` (Ex 6.3): `θ = 4 = cTheta`,
once a Kostant partition is exhibited (the nonemptiness bridge from `qipFeasible`). -/

section Witness

/-- **`(2,2,2)`: the Kostant-side `θ = cTheta = 1`** (Lehalleur–Rimányi Ex 4.3): the paper's
component count for the zero-product locus, now the closed form. -/
theorem numTop_zero_eq_cTheta_d222 :
    numTop d222 0 kostantPartitions_d222_nonempty = cTheta d222 :=
  numTop_zero_eq_cTheta d222 d222_monotone _

/-- **`(2,2,2)`: `numTop d222 0 = 1`**, matching `cTheta d222 = 1` via `numTop_zero_eq_cTheta`. -/
theorem numTop_zero_d222_eq_one :
    numTop d222 0 kostantPartitions_d222_nonempty = 1 := by
  rw [numTop_zero_eq_cTheta_d222, cTheta_d222]

/-- The QIP feasible set for `d639` is nonempty (`e = (8,0,…,0)`, `∑ = d 0 = 8`). -/
theorem qipFeasible_d639_nonempty : (qipFeasible d639).Nonempty :=
  ⟨![8, 0, 0, 0, 0, 0, 0, 0], by decide +kernel⟩

/-- The Kostant partitions of `d639` with corner `0` are nonempty (via the QIP feasible set). -/
theorem kostantPartitions_d639_nonempty : (kostantPartitions d639 0).Nonempty :=
  (kostant_nonempty_iff_qipFeasible_nonempty d639 d639_monotone).mpr qipFeasible_d639_nonempty

/-- **Ex 6.3 `d639`: the Kostant-side `θ = cTheta = 4`** (the paper's `θ` for the rearrangement),
now the closed form. -/
theorem numTop_zero_eq_cTheta_d639 :
    numTop d639 0 kostantPartitions_d639_nonempty = cTheta d639 :=
  numTop_zero_eq_cTheta d639 d639_monotone _

/-- **Ex 6.3 `d639`: `numTop d639 0 = 4`**, matching `cTheta d639 = 4`. -/
theorem numTop_zero_d639_eq_four :
    numTop d639 0 kostantPartitions_d639_nonempty = 4 := by
  rw [numTop_zero_eq_cTheta_d639, cTheta_d639]

end Witness

end DLNFibre.Core
