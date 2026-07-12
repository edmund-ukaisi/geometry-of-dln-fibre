import DLNFibre.DLN.RLCT.Validate.MvalMultSum
import DLNFibre.DLN.RLCT.Validate.MinAdmPermInvariance
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverPath
import DLNFibre.DLN.RLCT.Validate.CascadeAchiever
import DLNFibre.Core.CThetaQIPConverse
import DLNFibre.Core.CThetaPermInvariance
import DLNFibre.Core.CThetaThetaBridge
import DLNFibre.Core.CCodimCornerMono

/-!
# `DLNFibre.DLN.RLCT.Validate.MinAdmCCodim` — the central codimension identity `minAdm = cCodim`

The paper's central tie between the two descriptions of the fibre codimension:

    (minAdm M : ℤ) = cCodim M 0        (all widths `M`, `1 ≤ L`)

- the **QIP** combinatorial minimum `minAdm M = min_{T ∈ Adm M} M(T)` (Aoyagi's admissible-cone
  minimisation, `RouteMLayerSplit`), and
- the **geometric** `Ext`/orbit fibre codimension `cCodim M 0 = min_{m Kostant} codimForm m`
  (Lehalleur–Rimányi, `Core.CTheta`).

**Route (route i).** For weakly-increasing `M` the substitution `e_c := ρ_c − ρ_{c+1}` (`ρ =
expSurvivor`, the achiever running rank) is a value-preserving bijection between the admissible cone
`Adm M` and the QIP feasible set `qipFeasible M = {e : ∑ e = M₀}`, with `Mval M T = Gqip M (eOfT M T)`.
The value identity is the banked signed ring identity `Mval M T = codimForm (diffRank (cascadeRank M T))`
(`MvalMultSum`) matched against the banked horizontal-lace substitution `codimForm (mOfE M e) = Gqip M e`
(`Core.CThetaQIP`): the two `codimForm` arguments agree on the reads it makes — the families
`1 ≤ i ≤ j ≤ L` (first factor) and `1 ≤ u ≤ v ≤ L` (second); the corner `(0,L)` is never read.
Admissibility/monotonicity makes each mixed difference match the `ℕ`-valued lace array on those
reads (so `diffRank ≥ 0` there is a CONSEQUENCE of the match, not a used hypothesis). Then `min_T Mval = min_e Gqip = qipMin = cCodim` via the
banked QIP equality `cCodim_eq_qipMin` (weakly-increasing). The all-width form follows from `minAdm`'s
own permutation-invariance (`minAdm_comp_sort`, Part 1) and `cCodim`'s (`cCodim_comp_sort`).

This completes the route-i (□)-soundness: with the cited Aoyagi `RLCT = ½·codim`, the DLN RLCT equals
`½·cCodim` — a machine-checked theorem modulo Aoyagi, at **all** widths.

**Home.** DLN-side (not Core): the statement references the DLN objects `minAdm`/`Adm`/`Mval`/
`cascadeRank`/`diffRank`; only its Core dependencies (`cCodim`/`Gqip`/`mOfE`) are network-free.
-/

open scoped BigOperators
open Finset

namespace DLNFibre.DLN.RLCT

open DLNFibre.Core

variable {L : ℕ}

/-! ## Admissibility extraction + the `ρ`-difference exponent vector `eOfT` -/

/-- `admPred M T` from membership `T ∈ Adm M` (`Adm` is the `admPred`-filter of the bounded product). -/
theorem admPred_of_mem {M : Fin (L + 1) → ℕ} {T : Fin L → ℕ} (hT : T ∈ Adm M) : admPred M T := by
  rw [Adm, Finset.mem_filter] at hT; exact hT.2

/-- The **QIP exponent vector** `e_c = ρ_c − ρ_{c+1}` extracted from `T` (`ρ = expSurvivor`, `ρ_0 = M_0`,
`ρ_{k+1} = T_k`). For admissible `T` the `ℕ`-subtraction is honest (`ρ` weakly decreasing). -/
def eOfT (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Fin L → ℕ :=
  fun c ↦ expSurvivor M T c.castSucc - expSurvivor M T c.succ

/-- The `ℤ`-cast of `eOfT` is the honest difference (admissibility ⟹ `ρ` weakly decreasing). -/
theorem eOfT_cast (M : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hT : T ∈ Adm M) (c : Fin L) :
    (eOfT M T c : ℤ)
      = (expSurvivor M T c.castSucc : ℤ) - (expSurvivor M T c.succ : ℤ) := by
  have hle : expSurvivor M T c.succ ≤ expSurvivor M T c.castSucc :=
    expSurvivor_antitone M T (admPred_of_mem hT) (Fin.castSucc_le_succ c)
  simp only [eOfT]
  exact Nat.cast_sub hle

/-- Telescoping over `Fin L`: `∑ c, (g c.castSucc − g c.succ) = g 0 − g (last)`. -/
theorem sum_castSucc_sub_succ (g : Fin (L + 1) → ℤ) :
    ∑ c : Fin L, (g c.castSucc - g c.succ) = g 0 - g (Fin.last L) := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have hsum :
        (∑ c : Fin n, (g (c.castSucc : Fin (n + 1)).castSucc - g (c.succ : Fin (n + 1)).castSucc))
          = g ((0 : Fin (n + 1)).castSucc) - g ((Fin.last n).castSucc) :=
      ih (fun i : Fin (n + 1) ↦ g i.castSucc)
    have hcongr :
        (∑ c : Fin n, (g (c.castSucc : Fin (n + 1)).castSucc - g (c.castSucc : Fin (n + 1)).succ))
          = ∑ c : Fin n, (g (c.castSucc : Fin (n + 1)).castSucc - g (c.succ : Fin (n + 1)).castSucc) :=
      Finset.sum_congr rfl (fun c _ ↦ by rw [Fin.succ_castSucc])
    rw [hcongr, hsum]
    have h0 : ((0 : Fin (n + 1)).castSucc : Fin (n + 1 + 1)) = 0 := by apply Fin.ext; simp
    have hls : ((Fin.last n).succ : Fin (n + 1 + 1)) = Fin.last (n + 1) := rfl
    rw [h0, hls]; ring

/-- **Last-zero.** For admissible `T` (`1 ≤ L`), `ρ_L = expSurvivor M T (last L) = T_{L−1} = 0`
(admissibility clause (iii)). -/
theorem expSurvivor_last_eq_zero (M : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hL : 1 ≤ L)
    (hT : T ∈ Adm M) : expSurvivor M T (Fin.last L) = 0 := by
  obtain ⟨_, _, hlast⟩ := admPred_of_mem hT
  have hidx : (Fin.last L) = (⟨L - 1, by omega⟩ : Fin L).succ := by
    apply Fin.ext; simp only [Fin.val_last, Fin.val_succ]; omega
  rw [hidx, expSurvivor_succ]
  exact hlast ⟨L - 1, by omega⟩ rfl

/-- **Feasibility.** For admissible `T`, `∑ c, eOfT M T c = M 0` (telescope `ρ_0 − ρ_L`, `ρ_L = 0` by
last-zero admissibility). So `eOfT M T ∈ qipFeasible M`. -/
theorem eOfT_feasible (M : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hL : 1 ≤ L) (hT : T ∈ Adm M) :
    ∑ c, eOfT M T c = M 0 := by
  have hcast : ((∑ c, eOfT M T c : ℕ) : ℤ) = (M 0 : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl (fun c _ ↦ eOfT_cast M hT c),
      sum_castSucc_sub_succ (fun i ↦ (expSurvivor M T i : ℤ))]
    rw [show (expSurvivor M T 0 : ℤ) = (M 0 : ℤ) by rw [expSurvivor_zero],
      show (expSurvivor M T (Fin.last L) : ℤ) = 0 by rw [expSurvivor_last_eq_zero M hL hT]; rfl,
      sub_zero]
  exact_mod_cast hcast

theorem eOfT_mem_qipFeasible (M : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hL : 1 ≤ L) (hT : T ∈ Adm M) :
    eOfT M T ∈ qipFeasible M := by
  rw [qipFeasible, Finset.mem_finAntidiagonal]; exact eOfT_feasible M hL hT

/-! ## The value identity `Mval M T = Gqip M (eOfT M T)` -/

/-- `rhoT` at `a ∈ [0, L]` is `expSurvivor` at ANY `Fin (L+1)` index of value `a.toNat` (the clamp is
inert; the free index avoids opaque-proof `rw` friction). -/
theorem rhoT_eq_expSurvivor (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) {a : ℤ} (i : Fin (L + 1))
    (hi : (i : ℕ) = a.toNat) (ha : 0 ≤ a) (haL : a ≤ (L : ℤ)) :
    rhoT M T a = (expSurvivor M T i : ℤ) := by
  unfold rhoT
  congr 2
  apply Fin.ext
  simp only [hi]; omega

/-- `qT` at `a ∈ [0, L]`: `M_a − ρ_a` with the `M` and `ρ` reads at possibly-distinct `Fin (L+1)`
indices, each of value `a.toNat` (lets the `M` read match the lace side, `ρ` the other). -/
theorem qT_eq_sub (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) {a : ℤ} (iM iE : Fin (L + 1))
    (hiM : (iM : ℕ) = a.toNat) (hiE : (iE : ℕ) = a.toNat) (ha : 0 ≤ a) (haL : a ≤ (L : ℤ)) :
    qT M T a = (M iM : ℤ) - (expSurvivor M T iE : ℤ) := by
  unfold qT
  rw [rhoT_eq_expSurvivor M T iE hiE ha haL]
  have hmin : min a.toNat L = iM.val := by rw [hiM]; omega
  simp only [hmin, Fin.eta]

/-- **`codimForm` congruence on the reads.** `codimForm` reads only the first factor `f (i−1) (j−1)`
(with `1 ≤ i ≤ j ≤ L`) and the second factor `f u v` (with `1 ≤ u ≤ v ≤ L`); agreement there suffices. -/
theorem codimForm_congr_reads {f g : ℤ → ℤ → ℤ}
    (h1 : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ (L : ℤ) → f (i - 1) (j - 1) = g (i - 1) (j - 1))
    (h2 : ∀ u v : ℤ, 1 ≤ u → u ≤ v → v ≤ (L : ℤ) → f u v = g u v) :
    codimForm L f = codimForm L g := by
  unfold codimForm
  refine Finset.sum_congr rfl (fun i hi ↦ Finset.sum_congr rfl (fun u hu ↦
    Finset.sum_congr rfl (fun j hj ↦ Finset.sum_congr rfl (fun v hv ↦ ?_))))
  rw [Finset.mem_Icc] at hi hu hj hv
  rw [h1 i j (by omega) (by omega) (by omega), h2 u v (by omega) (by omega) (by omega)]

/-- **First-factor agreement.** For admissible `T`, at the read `(i−1, j−1)` (`1 ≤ i ≤ j ≤ L`), the
mixed difference matches the lace array: `i = 1` gives the top row `ρ_{j-1} − ρ_j = e_{j-1}`, `i ≥ 2`
the vanishing interior. -/
theorem diffRank_first_eq (M : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hT : T ∈ Adm M)
    (i j : ℤ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ (L : ℤ)) :
    diffRank (cascadeRank M T) (i - 1) (j - 1) = extendℤ (mOfE M (eOfT M T)) (i - 1) (j - 1) := by
  rw [extendℤ_mOfE_first hi hij hj]
  by_cases hi1 : i = 1
  · subst hi1
    rw [if_pos rfl, show ((1 : ℤ) - 1) = 0 from by ring,
      diffRank_cascadeRank_top_row' M T (j - 1) (by omega) (by omega), eOfT_cast M hT,
      rhoT_eq_expSurvivor M T (a := j - 1) (⟨(j - 1).toNat, by omega⟩ : Fin L).castSucc
        (by simp) (by omega) (by omega),
      rhoT_eq_expSurvivor M T (a := (j - 1) + 1) (⟨(j - 1).toNat, by omega⟩ : Fin L).succ
        (by simp only [Fin.val_succ]; omega) (by omega) (by omega)]
  · rw [if_neg hi1, diffRank_cascadeRank_interior M T (i - 1) (j - 1) (by omega) (by omega)
      (by omega) (by omega)]

/-- **Second-factor agreement.** For weakly-increasing `M` and admissible `T`, at the read `(u, v)`
(`1 ≤ u ≤ v ≤ L`), the mixed difference matches the lace array: `v = L` gives the right column
`q_u − q_{u-1} = e_{u-1} + (M_u − M_{u-1})`, `v < L` the vanishing interior. -/
theorem diffRank_second_eq (M : Fin (L + 1) → ℕ) (hmono : Monotone M) {T : Fin L → ℕ}
    (hT : T ∈ Adm M) (u v : ℤ) (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ (L : ℤ)) :
    diffRank (cascadeRank M T) u v = extendℤ (mOfE M (eOfT M T)) u v := by
  rw [extendℤ_mOfE_second hmono hu huv hv]
  by_cases hvL : v = (L : ℤ)
  · subst hvL
    rw [if_pos rfl, diffRank_cascadeRank_right_col' M T u hu huv, eOfT_cast M hT,
      qT_eq_sub M T (a := u) (⟨u.toNat, by omega⟩ : Fin (L + 1))
        (⟨(u - 1).toNat, by omega⟩ : Fin L).succ (by simp) (by simp only [Fin.val_succ]; omega)
        (by omega) (by omega),
      qT_eq_sub M T (a := u - 1) (⟨(u - 1).toNat, by omega⟩ : Fin (L + 1))
        (⟨(u - 1).toNat, by omega⟩ : Fin L).castSucc (by simp) (by simp) (by omega) (by omega)]
    ring
  · rw [if_neg hvL, diffRank_cascadeRank_interior M T u v (by omega) (by omega) (by omega)
      (by omega)]

/-- **The value identity.** For weakly-increasing `M` and admissible `T`, `Mval M T = Gqip M (eOfT M T)`:
the banked ring identity `Mval = codimForm (diffRank (cascadeRank))` matched against the banked
`codimForm (mOfE) = Gqip`, via read-agreement. -/
theorem Mval_eq_Gqip (M : Fin (L + 1) → ℕ) (hmono : Monotone M)
    {T : Fin L → ℕ} (hT : T ∈ Adm M) :
    Mval M T = Gqip M (eOfT M T) := by
  rw [Mval_eq_codimForm_diffRank_cascadeRank,
    codimForm_congr_reads (diffRank_first_eq M hT) (diffRank_second_eq M hmono hT),
    codimForm_mOfE M hmono]

/-! ## The reverse map `tOfE` (feasible `e` ↦ admissible `T`) -/

/-- The **reverse map** `T_c = M_0 − ∑_{j ≤ c} e_j` (`ρ_{c+1}`; the running-rank staircase of `e`). For
weakly-increasing `M` and feasible `e`, this lands in `Adm M` and inverts `eOfT`. -/
def tOfE (M : Fin (L + 1) → ℕ) (e : Fin L → ℕ) : Fin L → ℕ :=
  fun c ↦ M 0 - ∑ j ∈ Finset.Iic c, e j

/-- Prefix sums of a feasible `e` are `≤ M 0` (the full sum). -/
theorem sum_Iic_le (M : Fin (L + 1) → ℕ) {e : Fin L → ℕ} (hfeas : ∑ j, e j = M 0) (d : Fin L) :
    ∑ j ∈ Finset.Iic d, e j ≤ M 0 := by
  calc ∑ j ∈ Finset.Iic d, e j ≤ ∑ j, e j := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = M 0 := hfeas

/-- **Reverse lands in `Adm`.** For weakly-increasing `M` and feasible `e` (`∑ e = M₀`),
`tOfE M e ∈ Adm M`. Uses `tOfE ≤ M₀ ≤ admBound` (monotone), prefix-sum monotonicity, and the top
prefix `= M₀`. -/
theorem tOfE_mem (M : Fin (L + 1) → ℕ) (hmono : Monotone M) {e : Fin L → ℕ}
    (hfeas : ∑ j, e j = M 0) : tOfE M e ∈ Adm M := by
  have hle := sum_Iic_le M hfeas
  have hM0adm : ∀ c : Fin L, M 0 ≤ admBound M c := by
    intro c
    rw [admBound]
    split_ifs with hc0
    · exact le_min le_rfl (hmono (Fin.zero_le _))
    · exact hmono (Fin.zero_le _)
  rw [Adm, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun c ↦ ?_, fun c ↦ ?_, fun i j hij ↦ ?_, fun c hc ↦ ?_⟩
  · rw [Finset.mem_range]
    have h1 : tOfE M e c ≤ M 0 := Nat.sub_le _ _
    have h2 := hM0adm c
    omega
  · exact le_trans (Nat.sub_le _ _) (hM0adm c)
  · show M 0 - ∑ k ∈ Finset.Iic j, e k ≤ M 0 - ∑ k ∈ Finset.Iic i, e k
    have hsub : ∑ k ∈ Finset.Iic i, e k ≤ ∑ k ∈ Finset.Iic j, e k :=
      Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hij)
    omega
  · show M 0 - ∑ k ∈ Finset.Iic c, e k = 0
    have htop : Finset.Iic c = Finset.univ := by
      apply Finset.ext; intro x
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true, Fin.le_def]
      have := x.isLt; omega
    rw [htop, hfeas]; omega

/-- **Round-trip.** For feasible `e`, `eOfT M (tOfE M e) = e` (the reverse inverts the forward). -/
theorem eOfT_tOfE (M : Fin (L + 1) → ℕ) {e : Fin L → ℕ} (hfeas : ∑ j, e j = M 0) :
    eOfT M (tOfE M e) = e := by
  funext c
  have hle := sum_Iic_le M hfeas
  have hsucc : expSurvivor M (tOfE M e) c.succ = M 0 - ∑ j ∈ Finset.Iic c, e j := by
    rw [expSurvivor_succ]; rfl
  rw [eOfT]
  rcases Nat.eq_zero_or_pos c.val with hc0 | hcpos
  · have hcast : (c.castSucc : Fin (L + 1)) = 0 := by
      apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_zero]; exact hc0
    have hsing : Finset.Iic c = {c} := by
      apply Finset.ext; intro x
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def]
      exact ⟨fun h ↦ Fin.ext (by omega), fun h ↦ by rw [h]⟩
    rw [hcast, expSurvivor_zero, hsucc, hsing, Finset.sum_singleton]
    have hb : e c ≤ M 0 := by rw [← Finset.sum_singleton (f := e) c, ← hsing]; exact hle c
    omega
  · have hpred : (c.castSucc : Fin (L + 1)) = (⟨c.val - 1, by omega⟩ : Fin L).succ := by
      apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_succ]; omega
    rw [hpred, expSurvivor_succ, hsucc]
    show (M 0 - ∑ j ∈ Finset.Iic (⟨c.val - 1, by omega⟩ : Fin L), e j)
        - (M 0 - ∑ j ∈ Finset.Iic c, e j) = e c
    have hsplit : ∑ j ∈ Finset.Iic c, e j
        = (∑ j ∈ Finset.Iic (⟨c.val - 1, by omega⟩ : Fin L), e j) + e c := by
      have hIio : Finset.Iic (⟨c.val - 1, by omega⟩ : Fin L) = Finset.Iio c := by
        apply Finset.ext; intro x
        simp only [Finset.mem_Iic, Finset.mem_Iio, Fin.le_def, Fin.lt_def]; omega
      rw [show Finset.Iic c = insert c (Finset.Iio c) from (Finset.Iio_insert c).symm,
        Finset.sum_insert (by simp), hIio, Nat.add_comm]
    have h1 := hle c
    have h2 := hle (⟨c.val - 1, by omega⟩ : Fin L)
    omega

/-! ## The `inf'` equality and the monotone bridge -/

/-- **The optimisation transport.** For weakly-increasing `M` (`1 ≤ L`), the QIP minimum over the
admissible cone equals the QIP minimum over the feasible set:
`(Adm M).inf' Mval = (qipFeasible M).inf' Gqip`. Antisymmetry, each direction using one of the two
mutually-inverse maps `eOfT` / `tOfE` and the value identity. -/
theorem inf'_Adm_Mval_eq_inf'_qipFeasible_Gqip (M : Fin (L + 1) → ℕ) (hmono : Monotone M)
    (hL : 1 ≤ L) (hne : (qipFeasible M).Nonempty) :
    (Adm M).inf' (Adm_nonempty M) (Mval M) = (qipFeasible M).inf' hne (Gqip M) := by
  apply le_antisymm
  · refine Finset.le_inf' hne _ (fun e he ↦ ?_)
    have hfeas : ∑ j, e j = M 0 := by
      rw [qipFeasible, Finset.mem_finAntidiagonal] at he; exact he
    have hT : tOfE M e ∈ Adm M := tOfE_mem M hmono hfeas
    calc (Adm M).inf' (Adm_nonempty M) (Mval M)
          ≤ Mval M (tOfE M e) := Finset.inf'_le (Mval M) hT
      _ = Gqip M (eOfT M (tOfE M e)) := Mval_eq_Gqip M hmono hT
      _ = Gqip M e := by rw [eOfT_tOfE M hfeas]
  · refine Finset.le_inf' (Adm_nonempty M) _ (fun T hT ↦ ?_)
    calc (qipFeasible M).inf' hne (Gqip M)
          ≤ Gqip M (eOfT M T) := Finset.inf'_le (Gqip M) (eOfT_mem_qipFeasible M hL hT)
      _ = Mval M T := (Mval_eq_Gqip M hmono hT).symm

/-- **The monotone bridge (A-monotone).** For weakly-increasing `M` (`1 ≤ L`),
`(minAdm M : ℤ) = cCodim M 0`. -/
theorem minAdm_eq_cCodim_of_monotone (M : Fin (L + 1) → ℕ) (hmono : Monotone M) (hL : 1 ≤ L)
    (h : (kostantPartitions M 0).Nonempty) :
    (minAdm M : ℤ) = cCodim M 0 h := by
  have hne : (qipFeasible M).Nonempty :=
    (kostant_nonempty_iff_qipFeasible_nonempty M hmono).mp h
  have hcast : (minAdm M : ℤ) = (Adm M).inf' (Adm_nonempty M) (Mval M) := by
    rw [← Mval_tStar_eq, Mval_tStar_eq_inf']
  rw [hcast, cCodim_eq_qipMin M hmono h hne, qipMin,
    inf'_Adm_Mval_eq_inf'_qipFeasible_Gqip M hmono hL hne]

/-! ## The all-width identity -/

/-- **The central codimension identity `minAdm = cCodim` (all widths).** For every `M : Fin (L+1) → ℕ`
with `1 ≤ L`, the QIP combinatorial minimum equals the geometric `Ext`/orbit fibre codimension:
`(minAdm M : ℤ) = cCodim M 0`. Combines the monotone bridge with the permutation-invariance of both
sides (`minAdm_comp_sort`, `cCodim_comp_sort`) applied to the monotone rearrangement `M ∘ sort M`. -/
theorem minAdm_eq_cCodim (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (h : (kostantPartitions M 0).Nonempty) :
    (minAdm M : ℤ) = cCodim M 0 h := by
  have hsorted_mono : Monotone (M ∘ _root_.Tuple.sort M) := _root_.Tuple.monotone_sort M
  have hr : ∀ k, (0 : ℕ) ≤ M k := fun _ ↦ Nat.zero_le _
  have hsorted_ne : (kostantPartitions (M ∘ _root_.Tuple.sort M) 0).Nonempty :=
    kostantPartitions_nonempty_of_le hL (fun _ ↦ Nat.zero_le _)
  have hcs : cCodim (M ∘ _root_.Tuple.sort M) 0 hsorted_ne = cCodim M 0 h :=
    cCodim_comp_sort M 0 hr hsorted_ne h
  have hms : (minAdm (M ∘ _root_.Tuple.sort M) : ℤ) = (minAdm M : ℤ) := by
    rw [minAdm_comp_sort]
  rw [← hms, ← hcs, minAdm_eq_cCodim_of_monotone (M ∘ _root_.Tuple.sort M) hsorted_mono hL hsorted_ne]

/-! ## Non-vacuity witness — `(2,2,2)` -/

/-- **Witness `(2,2,2)`: the central identity holds on the anchor vector.**
`(minAdm ![2,2,2] : ℤ) = cCodim ![2,2,2] 0`. -/
theorem minAdm_eq_cCodim_d222 :
    (minAdm (Core.d222) : ℤ) = cCodim Core.d222 0 Core.kostantPartitions_d222_nonempty :=
  minAdm_eq_cCodim Core.d222 (by norm_num) _

/-- **Value cross-check `(2,2,2)`: `minAdm ![2,2,2] = 3`.** Through the identity and the banked
Kostant-side value `cCodim ![2,2,2] 0 = 3` (Lehalleur–Rimányi Ex 4.3), `minAdm ![2,2,2] = 3` — the
paper's `C = 3`. This theorem derives the value via the identity; the decorrelated cross-check is
the independent `minAdm Core.d222 = 3 := by decide` over the Adm/Mval cone (`RouteMLayerSplit`):
the two machineries (Kostant partitions vs the admissible cone) independently agree on `C = 3`. -/
theorem minAdm_d222_eq_three : minAdm Core.d222 = 3 := by
  have h := minAdm_eq_cCodim_d222
  rw [Core.cCodim_d222_zero] at h
  exact_mod_cast h

end DLNFibre.DLN.RLCT
