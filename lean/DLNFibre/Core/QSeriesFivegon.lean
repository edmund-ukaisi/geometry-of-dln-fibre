import DLNFibre.Core.QSeriesPeel
import DLNFibre.Core.QSeriesExtraction
import DLNFibre.Core.CThetaQIPConverse
import DLNFibre.Core.CCodimZeroMono

/-!
# `DLNFibre.Core.QSeriesFivegon` — Thm 5.6 (the "5gon"), M3b

The 5gon identity (= RWY 2018, reproved zero-cited): over `ℤ⟦X⟧`,

`Pmult d = ∑_{m ∈ kostantAll d} X^{(codimForm (extendℤ m)).toNat} · Pm m`,

the sum over **all** Kostant partitions of `d` (any corner). Proved by the PEEL induction on the
number of vertices `N`, with the last-column transfer collapsing via `transferRHS_eq` (M3a, iterated
`durfee`). This file: the `kostantAll` object + the generating sum `fivegonSum` + its membership and
non-negativity foundation. The peeling induction (the bijection + `codimForm`/`Pm` split) follows.
-/

namespace DLNFibre.Core

open PowerSeries Finset

variable {N : ℕ}

/-- **All Kostant partitions of `d`** (any corner): like `kostantPartitions d r` but without the
corner constraint `m (0, last) = r`. -/
def kostantAll (d : Fin (N + 1) → ℕ) : Finset (Fin (N + 1) × Fin (N + 1) → ℕ) :=
  (Fintype.piFinset (fun p : Fin (N + 1) × Fin (N + 1) ↦
      if p.1 ≤ p.2 then Finset.range (d p.1 + 1) else Finset.range 1)).filter
    (fun m ↦ ∀ k, kostantAt d m k)

/-- Membership in `kostantAll`, unfolded (bounded `m_{ij} ≤ d_i`, supported on `i ≤ j`, Kostant at
every vertex). -/
theorem mem_kostantAll {d : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ} :
    m ∈ kostantAll d ↔
      (∀ p : Fin (N + 1) × Fin (N + 1), m p ≤ d p.1)
        ∧ (∀ p : Fin (N + 1) × Fin (N + 1), ¬ p.1 ≤ p.2 → m p = 0)
        ∧ (∀ k, kostantAt d m k) := by
  unfold kostantAll
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hpi, hk⟩
    refine ⟨fun p ↦ ?_, fun p hp ↦ ?_, hk⟩
    · have := hpi p; split_ifs at this with h
      · simpa [Nat.lt_succ_iff] using this
      · simp only [Finset.mem_range, Nat.lt_one_iff] at this; omega
    · have := hpi p; rw [if_neg hp] at this
      simpa [Nat.lt_one_iff] using this
  · rintro ⟨hb, hs, hk⟩
    refine ⟨fun p ↦ ?_, hk⟩
    split_ifs with h
    · simp only [Finset.mem_range, Nat.lt_succ_iff]; exact hb p
    · simp only [Finset.mem_range, Nat.lt_one_iff]; exact hs p h

/-- `kostantAll` is the disjoint union of the corner-graded `kostantPartitions d r` — the corner
`m (0, last)` is determined by `m`, so each `m ∈ kostantAll` lies in exactly one `kostantPartitions`. -/
theorem kostantPartitions_subset_kostantAll {d : Fin (N + 1) → ℕ} {r : ℕ} :
    kostantPartitions d r ⊆ kostantAll d := by
  intro m hm
  rw [mem_kostantPartitions] at hm
  rw [mem_kostantAll]
  exact ⟨hm.1, hm.2.1, hm.2.2.1⟩

/-- The **Thm 5.6 generating function**: `∑_{m ∈ kostantAll d} X^{codimForm} · Pm m`. -/
noncomputable def fivegonSum (d : Fin (N + 1) → ℕ) : ℤ⟦X⟧ :=
  ∑ m ∈ kostantAll d, (X : ℤ⟦X⟧) ^ (codimForm N (extendℤ m)).toNat * Pm N m

/-- `fivegonSum` has non-negative coefficients (a sum of `X^c · Pm m`, each non-negative — M1). -/
theorem nonnegCoeffs_fivegonSum (d : Fin (N + 1) → ℕ) : NonnegCoeffs (fivegonSum d) := by
  intro n
  rw [fivegonSum, map_sum]
  refine Finset.sum_nonneg fun m _ ↦ ?_
  have : NonnegCoeffs ((X : ℤ⟦X⟧) ^ (codimForm N (extendℤ m)).toNat * Pm N m) := by
    refine NonnegCoeffs.mul (fun j ↦ ?_) (nonnegCoeffs_Pm m)
    rw [coeff_X_pow]; split_ifs <;> norm_num
  exact this n

/-- On `Fin 1` (a single vertex), the only Kostant partition is `m (0,0) = d 0`. -/
theorem kostantAll_zero_eq (d : Fin 1 → ℕ) :
    kostantAll d = {fun _ ↦ d 0} := by
  have fin01 : ∀ i : Fin (0 + 1), i = 0 := fun i ↦ by omega
  have prod01 : ∀ b : Fin (0 + 1) × Fin (0 + 1), b = (0, 0) := fun b ↦
    Prod.ext (fin01 b.1) (fin01 b.2)
  have hsum : ∀ (f : Fin (0 + 1) × Fin (0 + 1) → ℕ),
      ∑ p ∈ Finset.univ.filter (fun p : Fin (0 + 1) × Fin (0 + 1) ↦
        p.1 ≤ (0 : Fin (0 + 1)) ∧ (0 : Fin (0 + 1)) ≤ p.2), f p = f (0, 0) := by
    intro f
    rw [Finset.sum_eq_single (0, 0)]
    · intro b _ hb; exact absurd (prod01 b) hb
    · intro hmem
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _, le_refl _⟩) hmem
  ext m
  rw [Finset.mem_singleton, mem_kostantAll]
  constructor
  · rintro ⟨-, -, hk⟩
    have hk0 := hk 0
    rw [kostantAt, hsum] at hk0
    funext p
    rw [prod01 p]
    exact hk0.symm
  · rintro rfl
    refine ⟨fun p ↦ ?_, fun p hp ↦ ?_, fun k ↦ ?_⟩
    · change d 0 ≤ d p.1; rw [fin01 p.1]
    · exact absurd (le_of_eq ((fin01 p.1).trans (fin01 p.2).symm)) hp
    · rw [kostantAt, fin01 k, hsum]

/-- **Thm 5.6 base case** (`N = 0`): `fivegonSum d = Pmult d` — the single partition contributes
`X^0 · P (d 0) = P (d 0) = Pmult d`. -/
theorem fivegon_base (d : Fin 1 → ℕ) : fivegonSum d = Pmult d := by
  rw [fivegonSum, kostantAll_zero_eq, Finset.sum_singleton]
  have hcf : codimForm 0 (extendℤ (fun _ : Fin 1 × Fin 1 ↦ d 0)) = 0 := by
    rw [codimForm, show Finset.Icc (1 : ℤ) ((0 : ℕ) : ℤ) = ∅ from by decide, Finset.sum_empty]
  rw [hcf, Int.toNat_zero, pow_zero, one_mul, Pm, Pmult, Fin.prod_univ_one,
    show upperPairs 0 = {(0, 0)} from by decide, Finset.prod_singleton]

/-! ## The peeling step (`N+1`): merge the last vertex's column

`peelPart m` drops the last vertex `Fin.last (N+1)` by merging its column into column `N`
(`m'_{i,N} = m_{i,N} + m_{i,N+1}`); columns `j < N` are untouched. This is the `m'` of the
bijection `kostantAll d ↔ Σ_{m'} (last-column data)`. -/

/-- `extendℤ` is additive: `extendℤ (m₁ + m₂) = extendℤ m₁ + extendℤ m₂`. -/
theorem extendℤ_add (m₁ m₂ : Fin (N + 1) × Fin (N + 1) → ℕ) :
    extendℤ (m₁ + m₂) = extendℤ m₁ + extendℤ m₂ := by
  funext a b
  simp only [extendℤ, Pi.add_apply]
  split_ifs with h
  · push_cast; ring
  · ring

/-- The forward peel map: `m' = peelPart m` on `Fin (N+1)` merges `m`'s columns `N` and `N+1`. -/
def peelPart (m : Fin (N + 2) × Fin (N + 2) → ℕ) : Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ p.2.lastCases
    (m (p.1.castSucc, (Fin.last N).castSucc) + m (p.1.castSucc, Fin.last (N + 1)))
    (fun J₀ ↦ m (p.1.castSucc, J₀.castSucc.castSucc))

/-- `peelPart` value at the merged last column. -/
@[simp] theorem peelPart_last (m : Fin (N + 2) × Fin (N + 2) → ℕ) (I : Fin (N + 1)) :
    peelPart m (I, Fin.last N)
      = m (I.castSucc, (Fin.last N).castSucc) + m (I.castSucc, Fin.last (N + 1)) := by
  simp [peelPart]

/-- `peelPart` value at an interior column `j = castSucc J₀`. -/
@[simp] theorem peelPart_castSucc (m : Fin (N + 2) × Fin (N + 2) → ℕ) (I : Fin (N + 1))
    (J₀ : Fin N) :
    peelPart m (I, J₀.castSucc) = m (I.castSucc, J₀.castSucc.castSucc) := by
  simp [peelPart]

/-- **Additive form of `peelPart`**: a shifted entry plus a correction at the merged last column.
`peelPart m (i,j) = m(i⁺, j⁺) + [j = last] · m(i⁺, last)`. The clean handle for the `kostantAt` merge. -/
theorem peelPart_eq (m : Fin (N + 2) × Fin (N + 2) → ℕ) (i j : Fin (N + 1)) :
    peelPart m (i, j)
      = m (i.castSucc, j.castSucc)
        + (if j = Fin.last N then m (i.castSucc, Fin.last (N + 1)) else 0) := by
  induction j using Fin.lastCases with
  | last => rw [peelPart_last, if_pos rfl]
  | cast j₀ => rw [peelPart_castSucc, if_neg (Fin.castSucc_ne_last j₀), add_zero]

/-- The cover set at vertex `k`: interval-index pairs `q` with `q.1 ≤ k ≤ q.2`. -/
private def coverF (N : ℕ) (k : Fin (N + 1)) : Finset (Fin (N + 1) × Fin (N + 1)) :=
  Finset.univ.filter (fun q ↦ q.1 ≤ k ∧ k ≤ q.2)

/-- **The cover-sum reindex** (the `kostantAt`-merge crux): summing `peelPart m` over the cover of
`k` in `Fin (N+1)` equals summing `m` over the cover of `k.castSucc` in `Fin (N+2)`. Proof via the
additive form `peelPart_eq`: the shifted entries reindex by `castSucc` (the non-last columns), and the
`[j = last]` corrections supply the last column. -/
theorem peelPart_cover_sum (m : Fin (N + 2) × Fin (N + 2) → ℕ) (k : Fin (N + 1)) :
    ∑ q ∈ coverF N k, peelPart m q
      = ∑ p ∈ coverF (N + 1) k.castSucc, m p := by
  -- LHS: expand peelPart via its additive form, split the sum
  have hL : ∑ q ∈ coverF N k, peelPart m q
      = (∑ q ∈ coverF N k, m (q.1.castSucc, q.2.castSucc))
        + ∑ q ∈ coverF N k, (if q.2 = Fin.last N then m (q.1.castSucc, Fin.last (N + 1)) else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ ↦ peelPart_eq m q.1 q.2
  -- RHS: split the cover of k.castSucc by whether the second index is the last vertex
  have hR : ∑ p ∈ coverF (N + 1) k.castSucc, m p
      = (∑ p ∈ (coverF (N + 1) k.castSucc).filter (fun p ↦ p.2 ≠ Fin.last (N + 1)), m p)
        + ∑ p ∈ (coverF (N + 1) k.castSucc).filter (fun p ↦ ¬ p.2 ≠ Fin.last (N + 1)), m p :=
    (Finset.sum_filter_add_sum_filter_not (coverF (N + 1) k.castSucc)
      (fun p ↦ p.2 ≠ Fin.last (N + 1)) m).symm
  rw [hL, hR]
  congr 1
  · -- non-last part: bijection `q ↦ (q.1.castSucc, q.2.castSucc)`
    refine Finset.sum_bij (fun q _ ↦ (q.1.castSucc, q.2.castSucc)) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [coverF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      refine ⟨⟨?_, ?_⟩, Fin.castSucc_ne_last _⟩
      · exact Fin.castSucc_le_castSucc_iff.mpr hq.1
      · exact Fin.castSucc_le_castSucc_iff.mpr hq.2
    · intro q₁ _ q₂ _ h
      simp only [Prod.mk.injEq, Fin.castSucc_inj] at h
      exact Prod.ext h.1 h.2
    · intro p hp
      simp only [coverF, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨⟨ha, hb⟩, hlast⟩ := hp
      refine ⟨(p.1.castPred (Fin.ne_last_of_lt (lt_of_le_of_lt ha (Fin.castSucc_lt_last k))),
        p.2.castPred hlast), ?_, ?_⟩
      · simp only [coverF, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred]; exact ha
        · rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred]; exact hb
      · simp [Fin.castSucc_castPred]
    · intro q _; rfl
  · -- last part: `(i, last N) ↦ (i.castSucc, last (N+1))`
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun q _ ↦ (q.1.castSucc, Fin.last (N + 1))) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [coverF, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨⟨hq1, _⟩, _⟩ := hq
      simp only [coverF, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      exact ⟨⟨Fin.castSucc_le_castSucc_iff.mpr hq1, Fin.le_last _⟩, trivial⟩
    · intro q₁ hq₁ q₂ hq₂ h
      simp only [coverF, Finset.mem_filter, Finset.mem_univ, true_and] at hq₁ hq₂
      simp only [Prod.mk.injEq, Fin.castSucc_inj, and_true] at h
      exact Prod.ext h (hq₁.2.trans hq₂.2.symm)
    · intro p hp
      simp only [coverF, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hp
      obtain ⟨⟨hp1, _⟩, hp3⟩ := hp
      have hne : p.1 ≠ Fin.last (N + 1) :=
        Fin.ne_last_of_lt (lt_of_le_of_lt hp1 (Fin.castSucc_lt_last k))
      refine ⟨(p.1.castPred hne, Fin.last N), ?_, ?_⟩
      · simp only [coverF, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨?_, Fin.le_last _⟩, trivial⟩
        rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred]; exact hp1
      · exact Prod.ext (Fin.castSucc_castPred p.1 hne) hp3.symm
    · intro q _; rfl

/-- The "lower" part of `m` (columns `≤ N`, raw — NOT merged), as a `Fin (N+1)` array. -/
def peelLower (m : Fin (N + 2) × Fin (N + 2) → ℕ) : Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ m (p.1.castSucc, p.2.castSucc)

/-- The last-column correction at the merged column `N` (carries `m`'s column-`N+1` value). -/
def peelCorr (m : Fin (N + 2) × Fin (N + 2) → ℕ) : Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ if p.2 = Fin.last N then m (p.1.castSucc, Fin.last (N + 1)) else 0

/-- **`peelPart` splits as lower + correction** (`peelPart_eq` repackaged as an array identity). -/
theorem peelPart_eq_add (m : Fin (N + 2) × Fin (N + 2) → ℕ) :
    peelPart m = peelLower m + peelCorr m := by
  funext p
  obtain ⟨i, j⟩ := p
  rw [Pi.add_apply, peelPart_eq, peelLower, peelCorr]

/-- `extendℤ (peelCorr m)` vanishes off column `N` (it lives only at the merged column). -/
theorem extendℤ_peelCorr_off (m : Fin (N + 2) × Fin (N + 2) → ℕ) (a b : ℤ) (hb : b ≠ (N : ℤ)) :
    extendℤ (peelCorr m) a b = 0 := by
  unfold extendℤ
  split_ifs with h
  · obtain ⟨ha, hab, hbN⟩ := h
    unfold peelCorr
    split_ifs with h2
    · exfalso
      have hval : b.toNat = N := by have := congrArg Fin.val h2; simpa [Fin.val_last] using this
      omega
    · rfl
  · rfl

/-- The `peelCorr`-first cross-terms vanish: `codimBil N (extendℤ (peelCorr m)) A = 0` for any `A`
(the first factor reads column `j-1 ≤ N-1 < N`, where `extendℤ (peelCorr m)` is `0`). -/
theorem codimBil_peelCorr_left (m : Fin (N + 2) × Fin (N + 2) → ℕ) (A : ℤ → ℤ → ℤ) :
    codimBil N (extendℤ (peelCorr m)) A = 0 := by
  unfold codimBil
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun u _ ↦
    Finset.sum_eq_zero fun j hj ↦ Finset.sum_eq_zero fun v _ ↦ ?_
  rw [Finset.mem_Icc] at hj
  rw [extendℤ_peelCorr_off m (i - 1) (j - 1) (by omega), zero_mul]

/-- **Peel-side codimForm** (`codimForm_add` + the two `R`-first vanishings): the `codimForm` of the
merged partition is `codimForm A + codimBil A R`. -/
theorem codimForm_peel_lhs (m : Fin (N + 2) × Fin (N + 2) → ℕ) :
    codimForm N (extendℤ (peelPart m))
      = codimForm N (extendℤ (peelLower m))
        + codimBil N (extendℤ (peelLower m)) (extendℤ (peelCorr m)) := by
  rw [peelPart_eq_add, extendℤ_add, codimForm_add, codimBil_peelCorr_left,
    ← codimBil_self (extendℤ (peelCorr m)), codimBil_peelCorr_left]
  ring

/-- The "true last column" of `m` at the last vertex `N+1`, as a `Fin (N+2)` array. -/
def peelLast (m : Fin (N + 2) × Fin (N + 2) → ℕ) : Fin (N + 2) × Fin (N + 2) → ℕ :=
  fun p ↦ if p.2 = Fin.last (N + 1) then m (p.1, Fin.last (N + 1)) else 0

/-- **Big-side on-box identity**: on the box `0 ≤ α ≤ β ≤ N+1`, `extendℤ m = extendℤ (peelLower m)
+ extendℤ (peelLast m)` — columns `≤ N` come from `peelLower` (`castSucc`), column `N+1` from
`peelLast`. Hence the `(N+1)`-codimForm of `extendℤ m` rewrites to that of the split (`congr_onbox`). -/
theorem codimForm_peel_rhs (m : Fin (N + 2) × Fin (N + 2) → ℕ) :
    codimForm (N + 1) (extendℤ m)
      = codimForm (N + 1) (extendℤ (peelLower m) + extendℤ (peelLast m)) := by
  apply codimForm_congr_onbox
  intro α β hα hαβ hβ
  simp only [Pi.add_apply, extendℤ, peelLower, peelLast]
  rw [dif_pos ⟨hα, hαβ, hβ⟩]
  by_cases hbN : β ≤ (N : ℤ)
  · rw [dif_pos ⟨hα, hαβ, hbN⟩, dif_pos ⟨hα, hαβ, hβ⟩]
    split_ifs with hif
    · exfalso
      have hv := Fin.val_eq_of_eq hif; rw [Fin.val_last] at hv
      change β.toNat = N + 1 at hv; omega
    · rw [Nat.cast_zero, add_zero]
      congr 1
  · rw [dif_neg (by rintro ⟨_, _, h⟩; omega), dif_pos ⟨hα, hαβ, hβ⟩]
    split_ifs with hif
    · rw [zero_add]
      congr 1
      congr 1
      rw [hif]
    · exfalso; apply hif
      apply Fin.ext; rw [Fin.val_last]; change β.toNat = N + 1; omega

/-- The peel preserves support: if `m` is supported on `i ≤ j` then so is `peelPart m`. -/
theorem peelPart_support {m : Fin (N + 2) × Fin (N + 2) → ℕ}
    (hs : ∀ p : Fin (N + 2) × Fin (N + 2), ¬ p.1 ≤ p.2 → m p = 0)
    (p : Fin (N + 1) × Fin (N + 1)) (hp : ¬ p.1 ≤ p.2) : peelPart m p = 0 := by
  obtain ⟨I, J⟩ := p
  induction J using Fin.lastCases with
  | last => exact absurd (Fin.le_last I) hp
  | cast J₀ =>
    rw [peelPart_castSucc]
    apply hs
    simp only [Fin.castSucc_le_castSucc_iff] at hp ⊢
    exact hp

/-- **The peel maps `kostantAll d` into `kostantAll d'`** (`d' = d ∘ castSucc`). The `kostantAt`
constraint transfers by the cover-reindex `peelPart_cover_sum`; the bound and support follow. -/
theorem peelPart_mem {d : Fin (N + 2) → ℕ} {m : Fin (N + 2) × Fin (N + 2) → ℕ}
    (hm : m ∈ kostantAll d) : peelPart m ∈ kostantAll (d ∘ Fin.castSucc) := by
  rw [mem_kostantAll] at hm ⊢
  obtain ⟨_, hs, hk⟩ := hm
  have hk' : ∀ k, kostantAt (d ∘ Fin.castSucc) (peelPart m) k := by
    intro k
    have hkk := hk k.castSucc
    rw [kostantAt] at hkk
    rw [kostantAt]
    change d k.castSucc = ∑ q ∈ coverF N k, peelPart m q
    rw [peelPart_cover_sum]
    exact hkk
  refine ⟨fun p ↦ ?_, peelPart_support hs, hk'⟩
  by_cases hp : p.1 ≤ p.2
  · have hkp := hk' p.1
    rw [kostantAt] at hkp
    change peelPart m p ≤ d (Fin.castSucc p.1)
    rw [show d (Fin.castSucc p.1) = (d ∘ Fin.castSucc) p.1 from rfl, hkp]
    refine Finset.single_le_sum (f := peelPart m) (fun i _ ↦ Nat.zero_le _) ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_refl _, hp⟩
  · rw [peelPart_support hs p hp]; exact Nat.zero_le _

/-- **Fiberwise decomposition of `fivegonSum`** (the SUCC case `d : Fin (N+2) → ℕ`): reorganize the
sum over `kostantAll d` into its `peelPart`-fibres over `kostantAll d'`. Independent of the weight
identity — just `Finset.sum_fiberwise_of_maps_to` with `peelPart_mem`. -/
theorem fivegonSum_fiberwise (d : Fin (N + 2) → ℕ) :
    fivegonSum d
      = ∑ m' ∈ kostantAll (d ∘ Fin.castSucc),
          ∑ m ∈ (kostantAll d).filter (fun m ↦ peelPart m = m'),
            (X : ℤ⟦X⟧) ^ (codimForm (N + 1) (extendℤ m)).toNat * Pm (N + 1) m := by
  rw [fivegonSum]
  exact (Finset.sum_fiberwise_of_maps_to (fun m hm ↦ peelPart_mem hm) _).symm

/-! ## The codimForm split (thread-07 piece 2 / thread-08 A·R·L route)

`codimForm (N+1) (extendℤ m) = codimForm N (extendℤ (peelPart m)) + Δ`, with
`Δ = codimBil (N+1) A L − codimBil N A R` (`A = extendℤ (peelLower m)` the common lower part,
`R = extendℤ (peelCorr m)` the peeled last column at slot `N`, `L = extendℤ (peelLast m)` the true
last column at slot `N+1`). Built by expanding both sides with `codimForm_add` against `A` and killing
the first-slot cross-terms (`R`/`L` read out of range). -/

/-- `extendℤ` (level `K`) vanishes for column `b > K`. Here at level `N` for `peelLower m`. -/
theorem extendℤ_peelLower_col (m : Fin (N + 2) × Fin (N + 2) → ℕ) (a b : ℤ) (hb : (N : ℤ) < b) :
    extendℤ (peelLower m) a b = 0 := by
  unfold extendℤ; rw [dif_neg]; rintro ⟨_, _, h⟩; omega

/-- `extendℤ (peelLast m)` (level `N+1`) vanishes off the last column `N+1`. -/
theorem extendℤ_peelLast_off (m : Fin (N + 2) × Fin (N + 2) → ℕ) (a b : ℤ)
    (hb : b ≠ ((N : ℤ) + 1)) : extendℤ (peelLast m) a b = 0 := by
  unfold extendℤ
  split_ifs with h
  · obtain ⟨ha, hab, hbN⟩ := h
    unfold peelLast
    split_ifs with h2
    · exfalso
      have hval : b.toNat = N + 1 := by
        have := congrArg Fin.val h2; simpa [Fin.val_last] using this
      omega
    · rfl
  · rfl

/-- The `L`-first cross-terms vanish: `codimBil (N+1) (extendℤ (peelLast m)) A = 0` (the first factor
reads column `j-1 ≤ N < N+1`, where `extendℤ (peelLast m)` is `0`). -/
theorem codimBil_peelLast_left (m : Fin (N + 2) × Fin (N + 2) → ℕ) (A : ℤ → ℤ → ℤ) :
    codimBil (N + 1) (extendℤ (peelLast m)) A = 0 := by
  unfold codimBil
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun u _ ↦
    Finset.sum_eq_zero fun j hj ↦ Finset.sum_eq_zero fun v _ ↦ ?_
  rw [Finset.mem_Icc] at hj
  rw [extendℤ_peelLast_off m (i - 1) (j - 1) (by omega), zero_mul]

/-- Drop the top `N+1` of an integer `Icc`-range sum whose summand vanishes there. -/
private lemma sum_Icc_peel_top (a : ℤ) (g : ℤ → ℤ) (h : g ((N : ℤ) + 1) = 0) :
    ∑ x ∈ Finset.Icc a ((N : ℤ) + 1), g x = ∑ x ∈ Finset.Icc a (N : ℤ), g x := by
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega)) ?_).symm
  intro x hx hx'
  rw [Finset.mem_Icc] at hx
  rw [Finset.mem_Icc, not_and] at hx'
  have hxN : x = (N : ℤ) + 1 := by have := hx' hx.1; omega
  rw [hxN, h]

/-- **Step D — level change for `A = extendℤ (peelLower m)`**: `codimForm (N+1) A = codimForm N A`.
`A` vanishes off columns `≤ N`, so every term of the `(N+1)`-form involving the new index `N+1` reads
a zero factor (innermost) or sits over an empty inner range — they all drop. -/
theorem codimForm_peelLower_level (m : Fin (N + 2) × Fin (N + 2) → ℕ) :
    codimForm (N + 1) (extendℤ (peelLower m)) = codimForm N (extendℤ (peelLower m)) := by
  unfold codimForm
  simp only [Nat.cast_add, Nat.cast_one]
  set F := extendℤ (peelLower m) with hF
  have hv : ∀ i u j : ℤ,
      ∑ v ∈ Finset.Icc j ((N : ℤ) + 1), F (i - 1) (j - 1) * F u v
        = ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F u v := by
    intro i u j
    refine sum_Icc_peel_top j (fun v ↦ F (i - 1) (j - 1) * F u v) ?_
    show F (i - 1) (j - 1) * F u ((N : ℤ) + 1) = 0
    rw [hF, extendℤ_peelLower_col m u ((N : ℤ) + 1) (by omega), mul_zero]
  have hj : ∀ i u : ℤ,
      ∑ j ∈ Finset.Icc u ((N : ℤ) + 1), ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F u v
        = ∑ j ∈ Finset.Icc u (N : ℤ), ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F u v := by
    intro i u
    refine sum_Icc_peel_top u
      (fun j ↦ ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F u v) ?_
    show ∑ v ∈ Finset.Icc ((N : ℤ) + 1) (N : ℤ), F (i - 1) (((N : ℤ) + 1) - 1) * F u v = 0
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
  have hu : ∀ i : ℤ,
      ∑ u ∈ Finset.Icc i ((N : ℤ) + 1), ∑ j ∈ Finset.Icc u (N : ℤ),
          ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F u v
        = ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
            ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F u v := by
    intro i
    refine sum_Icc_peel_top i
      (fun u ↦ ∑ j ∈ Finset.Icc u (N : ℤ), ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F u v) ?_
    show ∑ j ∈ Finset.Icc ((N : ℤ) + 1) (N : ℤ),
        ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F ((N : ℤ) + 1) v = 0
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
  calc ∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
          ∑ j ∈ Finset.Icc u ((N : ℤ) + 1), ∑ v ∈ Finset.Icc j ((N : ℤ) + 1),
            F (i - 1) (j - 1) * F u v
      = ∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
          ∑ j ∈ Finset.Icc u ((N : ℤ) + 1), ∑ v ∈ Finset.Icc j (N : ℤ),
            F (i - 1) (j - 1) * F u v := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun u _ ↦
          Finset.sum_congr rfl fun j _ ↦ hv i u j
    _ = ∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
          ∑ j ∈ Finset.Icc u (N : ℤ), ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F u v := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun u _ ↦ hj i u
    _ = ∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i (N : ℤ),
          ∑ j ∈ Finset.Icc u (N : ℤ), ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F u v := by
        refine Finset.sum_congr rfl fun i _ ↦ hu i
    _ = ∑ i ∈ Finset.Icc (1 : ℤ) (N : ℤ), ∑ u ∈ Finset.Icc i (N : ℤ),
          ∑ j ∈ Finset.Icc u (N : ℤ), ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F u v := by
        refine sum_Icc_peel_top 1
          (fun i ↦ ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
            ∑ v ∈ Finset.Icc j (N : ℤ), F (i - 1) (j - 1) * F u v) ?_
        show ∑ u ∈ Finset.Icc ((N : ℤ) + 1) (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
            ∑ v ∈ Finset.Icc j (N : ℤ), F (((N : ℤ) + 1) - 1) (j - 1) * F u v = 0
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]

/-- **Big-side codimForm** (`codimForm_add` + the two `L`-first vanishings + Step D level-change):
`codimForm (N+1) (extendℤ m) = codimForm N A + codimBil (N+1) A L` (`A = extendℤ (peelLower m)`,
`L = extendℤ (peelLast m)`). -/
theorem codimForm_big (m : Fin (N + 2) × Fin (N + 2) → ℕ) :
    codimForm (N + 1) (extendℤ m)
      = codimForm N (extendℤ (peelLower m))
        + codimBil (N + 1) (extendℤ (peelLower m)) (extendℤ (peelLast m)) := by
  rw [codimForm_peel_rhs, codimForm_add, codimBil_peelLast_left,
    ← codimBil_self (extendℤ (peelLast m)), codimBil_peelLast_left, codimForm_peelLower_level]
  ring

/-- **The codimForm split** (thread-07 piece 2): `codimForm (N+1) (extendℤ m) =
codimForm N (extendℤ (peelPart m)) + Δ` with `Δ = codimBil (N+1) A L − codimBil N A R` the
last-two-columns pairing (`A = extendℤ (peelLower m)`, `R = extendℤ (peelCorr m)`,
`L = extendℤ (peelLast m)`). -/
theorem codimForm_split (m : Fin (N + 2) × Fin (N + 2) → ℕ) :
    codimForm (N + 1) (extendℤ m)
      = codimForm N (extendℤ (peelPart m))
        + (codimBil (N + 1) (extendℤ (peelLower m)) (extendℤ (peelLast m))
           - codimBil N (extendℤ (peelLower m)) (extendℤ (peelCorr m))) := by
  rw [codimForm_big, codimForm_peel_lhs]; ring

/-- The last column is carried verbatim: `extendℤ (peelLast m) u (N+1) = extendℤ m u (N+1)`. -/
theorem extendℤ_peelLast_at (m : Fin (N + 2) × Fin (N + 2) → ℕ) (u : ℤ) :
    extendℤ (peelLast m) u ((N : ℤ) + 1) = extendℤ m u ((N : ℤ) + 1) := by
  unfold extendℤ
  split_ifs with h
  · congr 1
    rw [peelLast]
    have hY : (⟨((N : ℤ) + 1).toNat, by omega⟩ : Fin (N + 2)) = Fin.last (N + 1) := by
      apply Fin.ext; rw [Fin.val_last]; show ((N : ℤ) + 1).toNat = N + 1; omega
    split_ifs with hc
    · congr 1
    · exact absurd hY hc
  · rfl

/-- The lower part agrees with `m` on columns `≤ N`: `extendℤ (peelLower m) a b = extendℤ m a b`. -/
theorem extendℤ_peelLower_at (m : Fin (N + 2) × Fin (N + 2) → ℕ) (a b : ℤ) (hb : b ≤ (N : ℤ)) :
    extendℤ (peelLower m) a b = extendℤ m a b := by
  unfold extendℤ
  by_cases hbox : 0 ≤ a ∧ a ≤ b ∧ b ≤ (N : ℤ)
  · rw [dif_pos hbox, dif_pos ⟨hbox.1, hbox.2.1, by omega⟩]; rfl
  · rw [dif_neg hbox, dif_neg (fun h ↦ hbox ⟨h.1, h.2.1, hb⟩)]

/-- The peeled correction at column `N` carries the last column: `extendℤ (peelCorr m) u N =
extendℤ m u (N+1)` for `0 ≤ u ≤ N`. -/
theorem extendℤ_peelCorr_at (m : Fin (N + 2) × Fin (N + 2) → ℕ) (u : ℤ) (hu : 0 ≤ u)
    (huN : u ≤ (N : ℤ)) : extendℤ (peelCorr m) u (N : ℤ) = extendℤ m u ((N : ℤ) + 1) := by
  unfold extendℤ
  rw [dif_pos ⟨hu, huN, le_refl _⟩, dif_pos ⟨hu, by omega, by omega⟩]
  congr 1
  rw [peelCorr]
  split_ifs with hc
  · congr 1
  · exfalso; apply hc; apply Fin.ext; rw [Fin.val_last]; show (N : ℤ).toNat = N; omega

/-- Small-side `codimBil` collapse: the `v`-sum picks `v = N` (where `peelCorr` lives), the eval
helpers rewrite to `m`'s entries. -/
theorem codimBil_peelCorr_collapse (m : Fin (N + 2) × Fin (N + 2) → ℕ) :
    codimBil N (extendℤ (peelLower m)) (extendℤ (peelCorr m))
      = ∑ i ∈ Finset.Icc (1 : ℤ) (N : ℤ), ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
          extendℤ m (i - 1) (j - 1) * extendℤ m u ((N : ℤ) + 1) := by
  unfold codimBil
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun u hu ↦
    Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_Icc] at hi hu hj
  rw [← Finset.mul_sum, Finset.sum_eq_single_of_mem (N : ℤ) (by rw [Finset.mem_Icc]; omega)
    (fun v _ hvN ↦ extendℤ_peelCorr_off m u v hvN)]
  rw [extendℤ_peelLower_at m (i - 1) (j - 1) (by omega), extendℤ_peelCorr_at m u (by omega) (by omega)]

/-- Big-side `codimBil` collapse: the `v`-sum picks `v = N+1` (where `peelLast` lives). -/
theorem codimBil_peelLast_collapse (m : Fin (N + 2) × Fin (N + 2) → ℕ) :
    codimBil (N + 1) (extendℤ (peelLower m)) (extendℤ (peelLast m))
      = ∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
          ∑ j ∈ Finset.Icc u ((N : ℤ) + 1),
          extendℤ m (i - 1) (j - 1) * extendℤ m u ((N : ℤ) + 1) := by
  unfold codimBil
  simp only [Nat.cast_add, Nat.cast_one]
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun u hu ↦
    Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_Icc] at hi hu hj
  rw [← Finset.mul_sum, Finset.sum_eq_single_of_mem ((N : ℤ) + 1) (by rw [Finset.mem_Icc]; omega)
    (fun v _ hvN ↦ extendℤ_peelLast_off m u v hvN)]
  rw [extendℤ_peelLower_at m (i - 1) (j - 1) (by omega), extendℤ_peelLast_at m u]

/-- **Step E — the explicit, manifestly-nonneg Δ**: the codimBil difference is the bilinear pairing
of `m`'s last two columns over `i ≤ u` (with `a = i-1`, the second-from-last column `N` against the
last column `N+1`). -/
theorem codimBil_diff_eq_delta (m : Fin (N + 2) × Fin (N + 2) → ℕ) :
    codimBil (N + 1) (extendℤ (peelLower m)) (extendℤ (peelLast m))
      - codimBil N (extendℤ (peelLower m)) (extendℤ (peelCorr m))
    = ∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
        extendℤ m (i - 1) (N : ℤ) * extendℤ m u ((N : ℤ) + 1) := by
  rw [codimBil_peelLast_collapse, codimBil_peelCorr_collapse]
  -- peel the inner `j` of the big sum at the top `N+1`
  have hLHS : (∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
                 ∑ j ∈ Finset.Icc u ((N : ℤ) + 1), extendℤ m (i - 1) (j - 1) * extendℤ m u ((N : ℤ) + 1))
      = ∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
          (extendℤ m (i - 1) (N : ℤ) * extendℤ m u ((N : ℤ) + 1)
           + ∑ j ∈ Finset.Icc u (N : ℤ), extendℤ m (i - 1) (j - 1) * extendℤ m u ((N : ℤ) + 1)) := by
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun u hu ↦ ?_
    rw [Finset.mem_Icc] at hu
    rw [show Finset.Icc u ((N : ℤ) + 1) = insert ((N : ℤ) + 1) (Finset.Icc u (N : ℤ)) from by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega,
        Finset.sum_insert (by simp [Finset.mem_Icc]),
        show ((N : ℤ) + 1) - 1 = (N : ℤ) from by ring]
  rw [hLHS]
  simp only [Finset.sum_add_distrib]
  -- the residual triple-sum (`j ≤ N`) drops its `i, u = N+1` slices (empty inner range) → small sum
  have hP1 : (∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
                ∑ j ∈ Finset.Icc u (N : ℤ), extendℤ m (i - 1) (j - 1) * extendℤ m u ((N : ℤ) + 1))
      = ∑ i ∈ Finset.Icc (1 : ℤ) (N : ℤ), ∑ u ∈ Finset.Icc i (N : ℤ),
          ∑ j ∈ Finset.Icc u (N : ℤ), extendℤ m (i - 1) (j - 1) * extendℤ m u ((N : ℤ) + 1) := by
    rw [sum_Icc_peel_top 1 (fun i ↦ ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
          ∑ j ∈ Finset.Icc u (N : ℤ), extendℤ m (i - 1) (j - 1) * extendℤ m u ((N : ℤ) + 1))
        (by show (∑ u ∈ Finset.Icc ((N : ℤ) + 1) ((N : ℤ) + 1), ∑ j ∈ Finset.Icc u (N : ℤ),
              extendℤ m (((N : ℤ) + 1) - 1) (j - 1) * extendℤ m u ((N : ℤ) + 1)) = 0
            rw [Finset.Icc_self, Finset.sum_singleton, Finset.Icc_eq_empty (by omega),
              Finset.sum_empty])]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [sum_Icc_peel_top i (fun u ↦ ∑ j ∈ Finset.Icc u (N : ℤ),
          extendℤ m (i - 1) (j - 1) * extendℤ m u ((N : ℤ) + 1))
        (by show (∑ j ∈ Finset.Icc ((N : ℤ) + 1) (N : ℤ),
              extendℤ m (i - 1) (j - 1) * extendℤ m ((N : ℤ) + 1) ((N : ℤ) + 1)) = 0
            rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty])]
  rw [hP1, add_sub_cancel_right]

/-- **The explicit codimForm split** (`codimForm_split` + Step E): `codimForm (N+1) (extendℤ m) =
codimForm N (extendℤ (peelPart m)) + Δ` with `Δ` the manifest last-two-columns pairing. -/
theorem codimForm_split_explicit (m : Fin (N + 2) × Fin (N + 2) → ℕ) :
    codimForm (N + 1) (extendℤ m)
      = codimForm N (extendℤ (peelPart m))
        + ∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
            extendℤ m (i - 1) (N : ℤ) * extendℤ m u ((N : ℤ) + 1) := by
  rw [codimForm_split, codimBil_diff_eq_delta]

/-- `Δ ≥ 0` — a sum of products of non-negative `extendℤ` entries (needed for the `toNat` exponent
split in the per-fibre collapse). -/
theorem delta_nonneg (m : Fin (N + 2) × Fin (N + 2) → ℕ) :
    0 ≤ ∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
          extendℤ m (i - 1) (N : ℤ) * extendℤ m u ((N : ℤ) + 1) :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (extendℤ_nonneg m _ _) (extendℤ_nonneg m _ _)

/-! ## The last-column bijection (thread-07 piece 1)

The fibre `{m : peelPart m = m'}` is parametrised by `m`'s last column `x = lastCol m`. The inverse
`rebuild m' x` keeps columns `≤ N-1` from `m'`, splits the merged column `N` as `(m'_{·,N} − x, x)`,
and places the corner. -/

/-- Forward map: `m`'s last column (vertex `N+1`). -/
def lastCol (m : Fin (N + 2) × Fin (N + 2) → ℕ) : Fin (N + 2) → ℕ :=
  fun I ↦ m (I, Fin.last (N + 1))

/-- Per-row upper bound for an admissible last column: `m'_{I',N}` for rows `I' ≤ N`, `dlast` for the
corner row `N+1`. -/
def boundX (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (dlast : ℕ) : Fin (N + 2) → ℕ :=
  fun I ↦ Fin.lastCases dlast (fun I' ↦ m' (I', Fin.last N)) I

/-- The admissible last columns for a fixed `m'` and last-vertex dimension `dlast`. -/
def admissibleXs (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (dlast : ℕ) : Finset (Fin (N + 2) → ℕ) :=
  (Fintype.piFinset (fun I ↦ Finset.range (boundX m' dlast I + 1))).filter (fun x ↦ ∑ I, x I = dlast)

/-- Inverse map: rebuild `m` from `m'` and a last column `x`. Columns `≤ N-1` come from `m'`; the
merged column `N` splits as `m_{I,N} = m'_{I',N} − x_I`, the last column `N+1` is `x`. -/
def rebuild (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (x : Fin (N + 2) → ℕ) :
    Fin (N + 2) × Fin (N + 2) → ℕ :=
  fun p ↦ Fin.lastCases
    (x p.1)
    (fun J' ↦ Fin.lastCases
      (Fin.lastCases 0 (fun I' ↦ m' (I', Fin.last N) - x p.1) p.1)
      (fun J'' ↦ Fin.lastCases 0 (fun I' ↦ m' (I', J''.castSucc)) p.1)
      J')
    p.2

/-- Right inverse: `lastCol (rebuild m' x) = x`. -/
theorem lastCol_rebuild (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (x : Fin (N + 2) → ℕ) :
    lastCol (rebuild m' x) = x := by
  funext I; simp only [lastCol, rebuild, Fin.lastCases_last]

/-- `peelPart` recovers `m'` from `rebuild m' x` (given the per-row bound, so the `ℕ` split is exact). -/
theorem peelPart_rebuild (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (x : Fin (N + 2) → ℕ)
    (hx : ∀ I' : Fin (N + 1), x I'.castSucc ≤ m' (I', Fin.last N)) :
    peelPart (rebuild m' x) = m' := by
  funext p
  obtain ⟨I', J'⟩ := p
  induction J' using Fin.lastCases with
  | last =>
    rw [peelPart_last]
    simp only [rebuild, Fin.lastCases_castSucc, Fin.lastCases_last]
    exact Nat.sub_add_cancel (hx I')
  | cast J'' =>
    rw [peelPart_castSucc]
    simp only [rebuild, Fin.lastCases_castSucc]

/-- Left inverse: `rebuild (peelPart m) (lastCol m) = m` for a support-respecting `m`. -/
theorem rebuild_lastCol (m : Fin (N + 2) × Fin (N + 2) → ℕ)
    (hs : ∀ p : Fin (N + 2) × Fin (N + 2), ¬ p.1 ≤ p.2 → m p = 0) :
    rebuild (peelPart m) (lastCol m) = m := by
  funext p
  obtain ⟨I, J⟩ := p
  induction J using Fin.lastCases with
  | last => simp only [rebuild, Fin.lastCases_last, lastCol]
  | cast J' =>
    simp only [rebuild, Fin.lastCases_castSucc]
    induction J' using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last]
      induction I using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        exact (hs _ (by simp only [Fin.le_def, Fin.val_last, Fin.coe_castSucc]; omega)).symm
      | cast I' =>
        simp only [Fin.lastCases_castSucc]
        rw [peelPart_last, lastCol]
        omega
    | cast J'' =>
      simp only [Fin.lastCases_castSucc]
      induction I using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        refine (hs _ ?_).symm
        have := J''.isLt
        simp only [Fin.le_def, Fin.val_last, Fin.coe_castSucc]; omega
      | cast I' =>
        simp only [Fin.lastCases_castSucc]
        rw [peelPart_castSucc]

/-- Forward map lands in `admissibleXs`: `lastCol m ∈ admissibleXs (peelPart m) (d_last)`. -/
theorem lastCol_mem_admissibleXs {d : Fin (N + 2) → ℕ} {m : Fin (N + 2) × Fin (N + 2) → ℕ}
    (hm : m ∈ kostantAll d) :
    lastCol m ∈ admissibleXs (peelPart m) (d (Fin.last (N + 1))) := by
  rw [mem_kostantAll] at hm
  obtain ⟨hb, _, hk⟩ := hm
  rw [admissibleXs, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun I ↦ ?_, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    induction I using Fin.lastCases with
    | last =>
      simp only [lastCol, boundX, Fin.lastCases_last]
      exact hb _
    | cast I' =>
      simp only [lastCol, boundX, Fin.lastCases_castSucc, peelPart_last]
      exact Nat.le_add_left _ _
  · have hklast := hk (Fin.last (N + 1))
    unfold kostantAt at hklast
    have hfilter : (Finset.univ.filter
        (fun p : Fin (N + 2) × Fin (N + 2) ↦ p.1 ≤ Fin.last (N + 1) ∧ Fin.last (N + 1) ≤ p.2))
        = Finset.univ.filter (fun p ↦ p.2 = Fin.last (N + 1)) :=
      Finset.filter_congr (fun p _ ↦ by simp only [Fin.le_last, true_and, Fin.last_le_iff])
    rw [hklast, hfilter, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun I _ ↦ ?_
    rw [Finset.sum_ite_eq' Finset.univ (Fin.last (N + 1)) (fun J ↦ m (I, J))]
    simp only [Finset.mem_univ, if_true, lastCol]

end DLNFibre.Core
