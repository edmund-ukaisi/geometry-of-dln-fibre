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

/-- **Backward membership (the crux)**: `rebuild m' x ∈ kostantAll d` for `m' ∈ kostantAll (d∘castSucc)`
and `x ∈ admissibleXs m' (d_last)`. The Kostant equations at old vertices reduce through
`peelPart_rebuild` + `peelPart_cover_sum`; at the new vertex through `∑ x = d_last`. -/
theorem rebuild_mem_kostantAll {d : Fin (N + 2) → ℕ} {m' : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hm' : m' ∈ kostantAll (d ∘ Fin.castSucc)) {x : Fin (N + 2) → ℕ}
    (hx : x ∈ admissibleXs m' (d (Fin.last (N + 1)))) :
    rebuild m' x ∈ kostantAll d := by
  rw [admissibleXs, Finset.mem_filter, Fintype.mem_piFinset] at hx
  obtain ⟨hxb, hxsum⟩ := hx
  rw [mem_kostantAll] at hm' ⊢
  obtain ⟨hm'b, hm's, hm'k⟩ := hm'
  have hxbound : ∀ I' : Fin (N + 1), x I'.castSucc ≤ m' (I', Fin.last N) := by
    intro I'; have := hxb I'.castSucc
    rwa [Finset.mem_range, Nat.lt_succ_iff, boundX, Fin.lastCases_castSucc] at this
  have hxle : ∀ I : Fin (N + 2), x I ≤ boundX m' (d (Fin.last (N + 1))) I := by
    intro I; have := hxb I; rwa [Finset.mem_range, Nat.lt_succ_iff] at this
  refine ⟨fun p ↦ ?_, fun p hp ↦ ?_, fun k ↦ ?_⟩
  · -- bound
    obtain ⟨I, J⟩ := p
    induction J using Fin.lastCases with
    | last =>
      simp only [rebuild, Fin.lastCases_last]
      refine (hxle I).trans ?_
      induction I using Fin.lastCases with
      | last => simp [boundX]
      | cast I' => simp only [boundX, Fin.lastCases_castSucc]; exact hm'b (I', Fin.last N)
    | cast J' =>
      simp only [rebuild, Fin.lastCases_castSucc]
      induction J' using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        induction I using Fin.lastCases with
        | last => simp only [Fin.lastCases_last]; exact Nat.zero_le _
        | cast I' =>
          simp only [Fin.lastCases_castSucc]
          exact (Nat.sub_le _ _).trans (hm'b (I', Fin.last N))
      | cast J'' =>
        simp only [Fin.lastCases_castSucc]
        induction I using Fin.lastCases with
        | last => simp only [Fin.lastCases_last]; exact Nat.zero_le _
        | cast I' => simp only [Fin.lastCases_castSucc]; exact hm'b (I', J''.castSucc)
  · -- support
    obtain ⟨I, J⟩ := p
    induction J using Fin.lastCases with
    | last => exact absurd (Fin.le_last I) hp
    | cast J' =>
      simp only [rebuild, Fin.lastCases_castSucc]
      induction J' using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        induction I using Fin.lastCases with
        | last => simp only [Fin.lastCases_last]
        | cast I' =>
          exfalso; apply hp
          simp only [Fin.le_def, Fin.coe_castSucc, Fin.val_last] at hp ⊢
          omega
      | cast J'' =>
        simp only [Fin.lastCases_castSucc]
        induction I using Fin.lastCases with
        | last => simp only [Fin.lastCases_last]
        | cast I' =>
          simp only [Fin.lastCases_castSucc]
          apply hm's
          simp only [Fin.le_def, Fin.coe_castSucc] at hp ⊢
          exact hp
  · -- kostant
    induction k using Fin.lastCases with
    | last =>
      unfold kostantAt
      have hfilter : (Finset.univ.filter
          (fun p : Fin (N + 2) × Fin (N + 2) ↦ p.1 ≤ Fin.last (N + 1) ∧ Fin.last (N + 1) ≤ p.2))
          = Finset.univ.filter (fun p ↦ p.2 = Fin.last (N + 1)) :=
        Finset.filter_congr (fun p _ ↦ by simp only [Fin.le_last, true_and, Fin.last_le_iff])
      rw [hfilter, Finset.sum_filter, Fintype.sum_prod_type]
      rw [← hxsum]
      refine Finset.sum_congr rfl fun I _ ↦ ?_
      rw [Finset.sum_ite_eq' Finset.univ (Fin.last (N + 1)) (fun J ↦ rebuild m' x (I, J))]
      simp only [Finset.mem_univ, if_true, rebuild, Fin.lastCases_last]
    | cast k' =>
      have hck := peelPart_cover_sum (rebuild m' x) k'
      rw [peelPart_rebuild m' x hxbound] at hck
      have hm'kk := hm'k k'
      unfold kostantAt at hm'kk ⊢
      rw [show d k'.castSucc = (d ∘ Fin.castSucc) k' from rfl, hm'kk]
      exact hck

/-- **The last-column bijection as a sum reindex** (thread-07 piece 1): the fibre sum over
`{m : peelPart m = m'}` reindexes to a sum over admissible last columns `x`. -/
theorem fibre_sum_reindex {M : Type*} [AddCommMonoid M] (d : Fin (N + 2) → ℕ)
    (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (hm' : m' ∈ kostantAll (d ∘ Fin.castSucc))
    (F : (Fin (N + 2) × Fin (N + 2) → ℕ) → M) :
    ∑ m ∈ (kostantAll d).filter (fun m ↦ peelPart m = m'), F m
      = ∑ x ∈ admissibleXs m' (d (Fin.last (N + 1))), F (rebuild m' x) := by
  refine Finset.sum_bij' (fun m _ ↦ lastCol m) (fun x _ ↦ rebuild m' x) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter] at hm
    exact hm.2 ▸ lastCol_mem_admissibleXs hm.1
  · intro x hx
    rw [Finset.mem_filter]
    have hxbound : ∀ I' : Fin (N + 1), x I'.castSucc ≤ m' (I', Fin.last N) := by
      rw [admissibleXs, Finset.mem_filter, Fintype.mem_piFinset] at hx
      intro I'; have := hx.1 I'.castSucc
      rwa [Finset.mem_range, Nat.lt_succ_iff, boundX, Fin.lastCases_castSucc] at this
    exact ⟨rebuild_mem_kostantAll hm' hx, peelPart_rebuild m' x hxbound⟩
  · intro m hm
    rw [Finset.mem_filter] at hm
    exact hm.2 ▸ rebuild_lastCol m (mem_kostantAll.mp hm.1).2.1
  · intro x _; exact lastCol_rebuild m' x
  · intro m hm
    rw [Finset.mem_filter] at hm
    have he : rebuild m' (lastCol m) = m := hm.2 ▸ rebuild_lastCol m (mem_kostantAll.mp hm.1).2.1
    rw [he]

/-- The codimForm exponent of `rebuild m' x`, split as `m'`'s codim plus the `Δ` pairing of its
last two columns. -/
theorem codimForm_rebuild (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (x : Fin (N + 2) → ℕ)
    (hxbound : ∀ I' : Fin (N + 1), x I'.castSucc ≤ m' (I', Fin.last N)) :
    codimForm (N + 1) (extendℤ (rebuild m' x))
      = codimForm N (extendℤ m')
        + ∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
            extendℤ (rebuild m' x) (i - 1) (N : ℤ) * extendℤ (rebuild m' x) u ((N : ℤ) + 1) := by
  rw [codimForm_split_explicit, peelPart_rebuild m' x hxbound]

/-- `Pmult` peels its last factor: `Pmult d = Pmult (d ∘ castSucc) · P (d_last)` (the outer
induction's multiplicative step). -/
theorem Pmult_succ {N : ℕ} (d : Fin (N + 2) → ℕ) :
    Pmult d = Pmult (d ∘ Fin.castSucc) * P (d (Fin.last (N + 1))) := by
  rw [Pmult, Pmult, Fin.prod_univ_castSucc]; rfl

/-- List bridge (piece 4): `(b.map P).prod = ∏_i P(b_i)` for `b = List.ofFn (m'(·, last N))` — the
column-`N` factors, the `transferRHS_eq` RHS reconciled with a `Finset.prod`. -/
theorem listOfFn_col_prod (m' : Fin (N + 1) × Fin (N + 1) → ℕ) :
    ((List.ofFn (fun i : Fin (N + 1) ↦ m' (i, Fin.last N))).map P).prod
      = ∏ i : Fin (N + 1), P (m' (i, Fin.last N)) := by
  rw [List.map_ofFn, List.prod_ofFn]; rfl

/-- The product over the **top column** `j = last K` of `upperPairs K` reindexes to a product over
all rows. (Reused for column `N` of `m'` and column `N+1` of `rebuild`.) -/
theorem prod_lastCol {K : ℕ} (f : Fin (K + 1) × Fin (K + 1) → ℕ) :
    ∏ p ∈ (upperPairs K).filter (fun p ↦ p.2 = Fin.last K), P (f p)
      = ∏ I : Fin (K + 1), P (f (I, Fin.last K)) := by
  refine Finset.prod_bij' (fun p _ ↦ p.1) (fun I _ ↦ (I, Fin.last K)) ?_ ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_univ _
  · intro I _
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.le_last I⟩, rfl⟩
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact Prod.ext rfl hp.2.symm
  · intro I _; rfl
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact congrArg (fun q ↦ P (f q)) (Prod.ext rfl hp.2)

/-- The "lower part" of `Pm`: the columns `< N` factors (`p.2 ≠ last N`). Common to `Pm N m'` and
`Pm (N+1) (rebuild m' x)`. -/
noncomputable def lowerPm (m' : Fin (N + 1) × Fin (N + 1) → ℕ) : ℤ⟦X⟧ :=
  ∏ p ∈ (upperPairs N).filter (fun p ↦ ¬ p.2 = Fin.last N), P (m' p)

/-- **S3(a)**: `Pm N m' = (∏_I P(m'_{I,N})) · lowerPm m'`. -/
theorem Pm_eq_colN_mul_lower (m' : Fin (N + 1) × Fin (N + 1) → ℕ) :
    Pm N m' = (∏ I : Fin (N + 1), P (m' (I, Fin.last N))) * lowerPm m' := by
  rw [Pm, ← Finset.prod_filter_mul_prod_filter_not (upperPairs N) (fun p ↦ p.2 = Fin.last N),
    prod_lastCol]
  rfl

/-- `rebuild` on a `(castSucc, castSucc)` index (columns `≤ N`): `m'_{I',J'}` minus the split-off `x`
at the merged column `N`. -/
theorem rebuild_castSucc (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (x : Fin (N + 2) → ℕ)
    (I' J' : Fin (N + 1)) :
    rebuild m' x (I'.castSucc, J'.castSucc)
      = m' (I', J') - (if J' = Fin.last N then x I'.castSucc else 0) := by
  induction J' using Fin.lastCases with
  | last => simp only [rebuild, Fin.lastCases_castSucc, Fin.lastCases_last, if_pos]
  | cast J'' =>
    simp only [rebuild, Fin.lastCases_castSucc, if_neg (Fin.castSucc_ne_last J''), Nat.sub_zero]

/-- Reindex the columns `< N+1` of `upperPairs (N+1)` to `upperPairs N` via `castSucc`. -/
theorem prod_lower_reindex (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (x : Fin (N + 2) → ℕ) :
    ∏ p ∈ (upperPairs (N + 1)).filter (fun p ↦ ¬ p.2 = Fin.last (N + 1)), P (rebuild m' x p)
      = ∏ q ∈ upperPairs N, P (rebuild m' x (q.1.castSucc, q.2.castSucc)) := by
  symm
  refine Finset.prod_bij' (fun q _ ↦ (q.1.castSucc, q.2.castSucc))
    (fun p hp ↦ (p.1.castPred (by
        have h := Finset.mem_filter.mp hp
        have hle := (Finset.mem_filter.mp h.1).2
        exact fun he ↦ h.2 (le_antisymm (Fin.le_last p.2) (he ▸ hle))),
      p.2.castPred (Finset.mem_filter.mp hp).2)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [upperPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact ⟨Fin.castSucc_le_castSucc_iff.mpr hq, Fin.castSucc_ne_last q.2⟩
  · intro p hp
    simp only [upperPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [Fin.le_def, Fin.coe_castPred, Fin.coe_castPred, ← Fin.le_def]
    exact hp.1
  · intro q _; simp only [Fin.castPred_castSucc]
  · intro p hp; simp only [Fin.castSucc_castPred]
  · intro q _; rfl

/-- `rebuild` on the last column: `rebuild m' x (I, last (N+1)) = x I`. -/
theorem rebuild_last (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (x : Fin (N + 2) → ℕ) (I : Fin (N + 2)) :
    rebuild m' x (I, Fin.last (N + 1)) = x I := by
  simp only [rebuild, Fin.lastCases_last]

/-- **S3(b)**: `Pm (N+1) (rebuild m' x)` factors as last-column × merged-column × lower part. -/
theorem Pm_rebuild_factor (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (x : Fin (N + 2) → ℕ) :
    Pm (N + 1) (rebuild m' x)
      = (∏ I : Fin (N + 2), P (x I))
        * ((∏ I' : Fin (N + 1), P (m' (I', Fin.last N) - x I'.castSucc)) * lowerPm m') := by
  rw [Pm,
    ← Finset.prod_filter_mul_prod_filter_not (upperPairs (N + 1)) (fun p ↦ p.2 = Fin.last (N + 1))]
  congr 1
  · rw [prod_lastCol]
    exact Finset.prod_congr rfl fun I _ ↦ congrArg P (rebuild_last m' x I)
  · rw [prod_lower_reindex,
      Finset.prod_congr rfl (fun q _ ↦ congrArg P (rebuild_castSucc m' x q.1 q.2)),
      ← Finset.prod_filter_mul_prod_filter_not (upperPairs N) (fun q ↦ q.2 = Fin.last N)]
    congr 1
    · rw [prod_lastCol]
      refine Finset.prod_congr rfl fun I _ ↦ ?_
      simp only [if_true]
    · rw [lowerPm]
      refine Finset.prod_congr rfl fun q hq ↦ ?_
      rw [Finset.mem_filter] at hq
      simp only [if_neg hq.2, Nat.sub_zero]

/-- The `toNat` exponent split for the per-fibre collapse: `X^{(A+Δ).toNat} = X^{A.toNat}·X^{Δ.toNat}`
when `A, Δ ≥ 0`. -/
theorem X_pow_toNat_add (A Δ : ℤ) (hA : 0 ≤ A) (hΔ : 0 ≤ Δ) :
    (X : ℤ⟦X⟧) ^ (A + Δ).toNat = X ^ A.toNat * X ^ Δ.toNat := by
  rw [Int.toNat_add hA hΔ, pow_add]

/-- `extendℤ (rebuild m' x)` at the last column `N+1`, evaluated to `x` of the row. -/
theorem extendℤ_rebuild_colNp1 (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (x : Fin (N + 2) → ℕ) (u : ℤ)
    (hu0 : 0 ≤ u) (huN : u ≤ (N : ℤ) + 1) :
    extendℤ (rebuild m' x) u ((N : ℤ) + 1) = (x ⟨u.toNat, by omega⟩ : ℤ) := by
  unfold extendℤ
  rw [dif_pos ⟨hu0, by omega, le_refl _⟩]
  norm_cast
  convert rebuild_last m' x ⟨u.toNat, by omega⟩ using 2

/-- `extendℤ (rebuild m' x)` at the merged column `N`, evaluated to `m'_{·,N} − x`. -/
theorem extendℤ_rebuild_colN (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (x : Fin (N + 2) → ℕ) (a : ℤ)
    (ha0 : 0 ≤ a) (haN : a ≤ (N : ℤ)) :
    extendℤ (rebuild m' x) a (N : ℤ)
      = ((m' (⟨a.toNat, by omega⟩, Fin.last N)
          - x (⟨a.toNat, by omega⟩ : Fin (N + 1)).castSucc : ℕ) : ℤ) := by
  unfold extendℤ
  rw [dif_pos ⟨ha0, by omega, by omega⟩]
  norm_cast
  have h := rebuild_castSucc m' x ⟨a.toNat, by omega⟩ (Fin.last N)
  rw [if_pos rfl] at h
  convert h using 2

/-- The per-fibre inner sum over admissible last columns: `X^{Δ}·(last col P-factors)·(merged col
P-factors)`. The per-fibre collapse reduces to this; `(Q)` shows it equals `transferRHS`. -/
noncomputable def innerSum (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (dlast : ℕ) : ℤ⟦X⟧ :=
  ∑ x ∈ admissibleXs m' dlast,
    X ^ (∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
          extendℤ (rebuild m' x) (i - 1) (N : ℤ) * extendℤ (rebuild m' x) u ((N : ℤ) + 1)).toNat
      * (∏ I : Fin (N + 2), P (x I))
      * (∏ I' : Fin (N + 1), P (m' (I', Fin.last N) - x I'.castSucc))

/-- **(P) — the per-fibre reduction**: the fibre weight-sum reduces to `X^{codim(m')}·lowerPm·innerSum`
(the last-column bijection + the `toNat` exponent split + the `Pm` factorization). -/
theorem perfibre_reduces (d : Fin (N + 2) → ℕ) (m' : Fin (N + 1) × Fin (N + 1) → ℕ)
    (hm' : m' ∈ kostantAll (d ∘ Fin.castSucc)) :
    ∑ m ∈ (kostantAll d).filter (fun m ↦ peelPart m = m'),
        X ^ (codimForm (N + 1) (extendℤ m)).toNat * Pm (N + 1) m
      = X ^ (codimForm N (extendℤ m')).toNat * lowerPm m' * innerSum m' (d (Fin.last (N + 1))) := by
  rw [fibre_sum_reindex d m' hm', innerSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hxbound : ∀ I' : Fin (N + 1), x I'.castSucc ≤ m' (I', Fin.last N) := by
    rw [admissibleXs, Finset.mem_filter, Fintype.mem_piFinset] at hx
    intro I'; have := hx.1 I'.castSucc
    rwa [Finset.mem_range, Nat.lt_succ_iff, boundX, Fin.lastCases_castSucc] at this
  rw [codimForm_rebuild m' x hxbound,
    X_pow_toNat_add _ _ (codimForm_extendℤ_nonneg _) (delta_nonneg _), Pm_rebuild_factor]
  ring

/-! ## (Q) — the q-series inner-sum induction

The `innerSum` over admissible last columns equals `transferRHS` of the column-`N` data. We work
through a length-indexed flat reformulation `adm b d` (Codex route): admissible `(n+1)`-tuples summing
to `d` with `x_{i.castSucc} ≤ b_i`. The constrained-vector peel reorganizes `∑_{x ∈ adm b d}` into
`∑_{x₀} ∑_{y ∈ adm (tail b) (d−x₀)}` via a sigma `Finset.sum_bij'`. The exponent (a `Fin`-indexed
ℕ-pairing `flatDelta`) peels as `(b₀−x₀)(d−x₀) + flatDelta (tail b) y`, and each block closes with
`durfee` — yielding `qSum b d = transferRHS (List.ofFn b) d`. -/

/-- Flat admissible tuples: `(n+1)`-tuples summing to `d` with `x_{i.castSucc} ≤ b_i` on the first
`n` coordinates (the corner coordinate `n` is free, bounded by `d` via the sum). -/
def adm {n : ℕ} (b : Fin n → ℕ) (d : ℕ) : Finset (Fin (n + 1) → ℕ) :=
  (Finset.Nat.antidiagonalTuple (n + 1) d).filter (fun x ↦ ∀ i : Fin n, x i.castSucc ≤ b i)

/-- Membership in `adm`, unfolded. -/
theorem mem_adm {n : ℕ} {b : Fin n → ℕ} {d : ℕ} {x : Fin (n + 1) → ℕ} :
    x ∈ adm b d ↔ (∑ i, x i = d) ∧ (∀ i : Fin n, x i.castSucc ≤ b i) := by
  rw [adm, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]

/-- The admissible last columns are exactly `adm` of the column-`N` data. The only non-trivial point
is the corner bound `x_{last} ≤ dlast`, which follows from `∑ x = dlast`. -/
theorem admissibleXs_eq_adm (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (dlast : ℕ) :
    admissibleXs m' dlast = adm (fun i : Fin (N + 1) ↦ m' (i, Fin.last N)) dlast := by
  ext x
  rw [admissibleXs, Finset.mem_filter, Fintype.mem_piFinset, mem_adm]
  constructor
  · rintro ⟨hb, hsum⟩
    refine ⟨hsum, fun i ↦ ?_⟩
    have := hb i.castSucc
    rwa [Finset.mem_range, Nat.lt_succ_iff, boundX, Fin.lastCases_castSucc] at this
  · rintro ⟨hsum, hb⟩
    refine ⟨fun I ↦ ?_, hsum⟩
    rw [Finset.mem_range, Nat.lt_succ_iff]
    induction I using Fin.lastCases with
    | last =>
      rw [boundX, Fin.lastCases_last, ← hsum]
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)
    | cast I' => rw [boundX, Fin.lastCases_castSucc]; exact hb I'

/-- **The constrained-vector peel** (the (Q) crux): a sum over `adm b d` (with `b : Fin (n+1) → ℕ`)
reorganizes into `∑_{x₀ ≤ min (b 0) d} ∑_{y ∈ adm (tail b) (d−x₀)} F (cons x₀ y)`. Proof via a sigma
`Finset.sum_bij'` (`x ↦ ⟨x 0, tail x⟩`, inverse `⟨x₀, y⟩ ↦ cons x₀ y`). The `∑ = d` filter couples
head and tail; the head bound `x₀ ≤ min (b 0) d` comes from `x₀ ≤ b₀` and `x₀ ≤ ∑ x = d`. -/
theorem adm_peel_sum {M : Type*} [AddCommMonoid M] {n : ℕ} (b : Fin (n + 1) → ℕ) (d : ℕ)
    (F : (Fin (n + 2) → ℕ) → M) :
    ∑ x ∈ adm b d, F x
      = ∑ x0 ∈ Finset.range (min (b 0) d + 1),
          ∑ y ∈ adm (Fin.tail b) (d - x0), F (Fin.cons x0 y) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun x _ ↦ (⟨x 0, Fin.tail x⟩ : Σ _ : ℕ, Fin (n + 1) → ℕ))
    (fun p _ ↦ Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · -- maps_to: x ∈ adm b d → ⟨x 0, tail x⟩ ∈ sigma
    intro x hx
    rw [mem_adm] at hx
    obtain ⟨hsum, hb⟩ := hx
    have hx0d : x 0 ≤ d := by
      rw [← hsum]; exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ 0)
    have hx0b : x 0 ≤ b 0 := by have := hb 0; rwa [Fin.castSucc_zero] at this
    rw [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff, mem_adm]
    refine ⟨le_min hx0b hx0d, ?_, fun i ↦ ?_⟩
    · -- ∑ tail x = d - x 0
      rw [Fin.sum_univ_succ] at hsum
      simp only [Fin.tail]; omega
    · -- tail x bound: (tail x) (i.castSucc) = x (i.castSucc.succ) ≤ b i.succ = (tail b) i
      simp only [Fin.tail]
      have := hb i.succ
      rwa [Fin.castSucc_succ] at this
  · -- inv maps_to: ⟨x0, y⟩ ∈ sigma → cons x0 y ∈ adm b d
    intro p hp
    rw [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff, mem_adm] at hp
    obtain ⟨hx0, hysum, hyb⟩ := hp
    simp only
    rw [mem_adm]
    refine ⟨?_, fun i ↦ ?_⟩
    · rw [Fin.sum_cons]; omega
    · induction i using Fin.cases with
      | zero => rw [Fin.castSucc_zero, Fin.cons_zero]; omega
      | succ i' =>
        rw [Fin.castSucc_succ, Fin.cons_succ]
        have := hyb i'; simpa [Fin.tail] using this
  · -- left inverse: cons (x 0) (tail x) = x
    intro x _; exact Fin.cons_self_tail x
  · -- right inverse: ⟨(cons x0 y) 0, tail (cons x0 y)⟩ = ⟨x0, y⟩
    intro p _
    obtain ⟨x0, y⟩ := p
    simp only [Fin.cons_zero, Fin.tail_cons]
  · -- term: F x = F (cons (x 0) (tail x))
    intro x _; exact congrArg F (Fin.cons_self_tail x).symm

/-- The peelable ℤ exponent of the flat q-sum: recursively, the first block `(b₀−x₀)·(∑_{i>0} xᵢ)`
plus the tail's exponent. A pure-ℤ recursion (no `ℕ`-subtraction), peeling under `Fin.cons`. -/
def flatDelta : (n : ℕ) → (Fin n → ℕ) → (Fin (n + 1) → ℕ) → ℤ
  | 0, _, _ => 0
  | (n + 1), b, x =>
      ((b 0 : ℤ) - x 0) * (∑ i : Fin (n + 1), (x i.succ : ℤ))
        + flatDelta n (Fin.tail b) (Fin.tail x)

/-- `flatDelta` peels its first block (definitional unfold of the `succ` branch). -/
theorem flatDelta_succ {n : ℕ} (b : Fin (n + 1) → ℕ) (x : Fin (n + 2) → ℕ) :
    flatDelta (n + 1) b x
      = ((b 0 : ℤ) - x 0) * (∑ i : Fin (n + 1), (x i.succ : ℤ))
        + flatDelta n (Fin.tail b) (Fin.tail x) := rfl

/-- `flatDelta` is `≥ 0` on admissible tuples (each block factor `bᵢ − xᵢ ≥ 0`, the tail-sum `≥ 0`). -/
theorem flatDelta_nonneg {n : ℕ} (b : Fin n → ℕ) {x : Fin (n + 1) → ℕ}
    (hx : ∀ i : Fin n, x i.castSucc ≤ b i) : 0 ≤ flatDelta n b x := by
  induction n with
  | zero => rw [flatDelta]
  | succ n ih =>
    rw [flatDelta_succ]
    refine add_nonneg (mul_nonneg ?_ ?_) (ih (Fin.tail b) ?_)
    · have := hx 0; rw [Fin.castSucc_zero] at this; push_cast; omega
    · exact Finset.sum_nonneg fun i _ ↦ Int.natCast_nonneg _
    · intro i; have := hx i.succ; simpa [Fin.tail, Fin.castSucc_succ] using this

/-- **The general flat q-sum**: over admissible tuples `adm b d`, weight `X^{flatDelta}·∏ P(xᵢ)·∏ P(bᵢ−x_{i.castSucc})`. -/
noncomputable def qSum {n : ℕ} (b : Fin n → ℕ) (d : ℕ) : ℤ⟦X⟧ :=
  ∑ x ∈ adm b d,
    X ^ (flatDelta n b x).toNat
      * (∏ I : Fin (n + 1), P (x I))
      * (∏ i : Fin n, P (b i - x i.castSucc))

/-- `adm` at `n = 0` is the single tuple `![d]` (no constraints; the sole `Fin 1`-tuple summing to `d`). -/
theorem adm_zero (b : Fin 0 → ℕ) (d : ℕ) : adm b d = {![d]} := by
  rw [adm, Finset.filter_true_of_mem (fun x _ i ↦ i.elim0), Finset.Nat.antidiagonalTuple_one]

/-- **`flatDelta` as an explicit double sum** over the row/column pairs `a.castSucc < u`. The bridge
between the recursive exponent and the `innerSum` codimForm pairing. -/
theorem flatDelta_eq_finsum {n : ℕ} (b : Fin n → ℕ) (x : Fin (n + 1) → ℕ) :
    flatDelta n b x
      = ∑ a : Fin n, ∑ u : Fin (n + 1),
          (if a.castSucc < u then ((b a : ℤ) - x a.castSucc) * x u else 0) := by
  induction n with
  | zero => rw [flatDelta]; simp
  | succ n ih =>
    -- split the RHS outer sum over `a : Fin (n+2)` at `a = 0`
    rw [Fin.sum_univ_succ (f := fun a : Fin (n + 1) ↦ ∑ u : Fin (n + 2),
        if a.castSucc < u then ((b a : ℤ) - x a.castSucc) * x u else 0)]
    rw [flatDelta_succ, ih (Fin.tail b) (Fin.tail x)]
    congr 1
    · -- a = 0 row: RHS sum picks u = u'.succ; pull `(b0-x0)` out, match the block tail-sum
      rw [Finset.mul_sum, Fin.castSucc_zero,
        Fin.sum_univ_succ (f := fun u : Fin (n + 2) ↦
          if (0 : Fin (n + 2)) < u then ((b 0 : ℤ) - x 0) * x u else 0),
        if_neg (lt_irrefl _), zero_add]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [if_pos (Fin.succ_pos u)]
    · -- a = a'.succ rows reindex to the tail finsum (shift u = u'.succ)
      refine Finset.sum_congr rfl fun a' _ ↦ ?_
      rw [Fin.sum_univ_succ (f := fun u : Fin (n + 2) ↦
          if a'.succ.castSucc < u then ((b a'.succ : ℤ) - x a'.succ.castSucc) * x u else 0),
        if_neg (not_lt.mpr (Fin.zero_le _)), zero_add]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      have hcond : (a'.succ.castSucc < u.succ) ↔ (a'.castSucc < u) := by
        rw [← Fin.succ_castSucc, Fin.succ_lt_succ_iff]
      by_cases h : a'.castSucc < u
      · rw [if_pos (hcond.mpr h), if_pos h, Fin.tail, Fin.tail, Fin.tail, Fin.succ_castSucc]
      · rw [if_neg (fun hc ↦ h (hcond.mp hc)), if_neg h]

/-- **The exponent bridge**: the `innerSum` codimForm exponent (an `Icc`-indexed ℤ pairing of
`rebuild`'s last two columns) equals `flatDelta (N+1) (col) x` of the column-`N` data. The two
`extendℤ_rebuild` eval lemmas turn the `extendℤ` entries into `colₐ − xₐ` and `x_u`; the `Icc`-to-`Fin`
reindex (`i ↦ ⟨(i−1).toNat⟩`, inner via `Finset.sum_filter`) matches `flatDelta_eq_finsum`. -/
theorem innerSum_exp_eq_flatDelta (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (x : Fin (N + 2) → ℕ)
    (hxbound : ∀ I' : Fin (N + 1), x I'.castSucc ≤ m' (I', Fin.last N)) :
    (∑ i ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), ∑ u ∈ Finset.Icc i ((N : ℤ) + 1),
        extendℤ (rebuild m' x) (i - 1) (N : ℤ) * extendℤ (rebuild m' x) u ((N : ℤ) + 1))
      = flatDelta (N + 1) (fun i : Fin (N + 1) ↦ m' (i, Fin.last N)) x := by
  rw [flatDelta_eq_finsum]
  -- outer reindex Icc 1 (N+1) → Fin (N+1) univ, i ↦ ⟨(i-1).toNat⟩, a ↦ a+1
  refine Finset.sum_bij' (fun i hi ↦ (⟨(i - 1).toNat, by rw [Finset.mem_Icc] at hi; omega⟩ : Fin (N + 1)))
    (fun a _ ↦ (a : ℤ) + 1) ?_ ?_ ?_ ?_ ?_
  · intro i _; exact Finset.mem_univ _
  · intro a _; simp only; rw [Finset.mem_Icc]; have := a.isLt; omega
  · intro i hi; simp only [Fin.val_mk]; rw [Finset.mem_Icc] at hi; omega
  · intro a _; simp only; apply Fin.ext; simp only [Fin.val_mk]; have := a.isLt; omega
  · -- term: inner Icc sum at i = guarded Fin sum at a = ⟨(i-1).toNat⟩
    intro i hi
    rw [Finset.mem_Icc] at hi
    simp only
    set a : Fin (N + 1) := ⟨(i - 1).toNat, by omega⟩ with ha
    -- rewrite the LHS first factor via the colN eval lemma (independent of u)
    have haeq : (⟨(i - 1).toNat, by omega⟩ : Fin (N + 1)) = a := by rw [ha]
    -- the truncated ℕ-subtraction = the ℤ-subtraction, since `x a.castSucc ≤ m' (a, last N)`
    have hcolN : extendℤ (rebuild m' x) (i - 1) (N : ℤ)
        = ((m' (a, Fin.last N) : ℤ) - x a.castSucc) := by
      rw [extendℤ_rebuild_colN m' x (i - 1) (by omega) (by omega), haeq, Nat.cast_sub (hxbound a)]
    -- convert the guarded Fin sum to a filtered sum
    rw [← Finset.sum_filter]
    -- inner reindex Icc i (N+1) → (univ).filter (a.castSucc < ·), u ↦ ⟨u.toNat⟩, ufin ↦ ufin
    refine Finset.sum_bij' (fun u hu ↦ (⟨u.toNat, by rw [Finset.mem_Icc] at hu; omega⟩ : Fin (N + 2)))
      (fun ufin _ ↦ (ufin : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro u hu; simp only; rw [Finset.mem_Icc] at hu
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Fin.lt_def, Fin.coe_castSucc, ha]; simp only [Fin.val_mk]; omega
    · intro ufin hufin; simp only; rw [Finset.mem_filter] at hufin
      rw [Finset.mem_Icc]
      have hlt := hufin.2; rw [Fin.lt_def, Fin.coe_castSucc, ha] at hlt
      simp only [Fin.val_mk] at hlt
      have := ufin.isLt; constructor <;> omega
    · intro u hu; simp only [Fin.val_mk]; rw [Finset.mem_Icc] at hu; omega
    · intro ufin _; simp only; apply Fin.ext; simp only [Fin.val_mk, Int.toNat_natCast]
    · intro u hu; simp only; rw [Finset.mem_Icc] at hu
      rw [hcolN, extendℤ_rebuild_colNp1 m' x u (by omega) (by omega)]

/-- **(Q), general form**: `qSum b d = transferRHS (List.ofFn b) d` — the flat q-sum equals the
last-column transfer. Induction on `n`: base `qSum [] d = P d`; step peels the first block via
`adm_peel_sum`, the `flatDelta`/P-factor split, one `durfee`, and the IH. -/
theorem qSum_eq_transferRHS : ∀ {n : ℕ} (b : Fin n → ℕ) (d : ℕ),
    qSum b d = transferRHS (List.ofFn b) d
  | 0, b, d => by
      rw [qSum, adm_zero, Finset.sum_singleton, List.ofFn_zero, transferRHS]
      rw [flatDelta, Int.toNat_zero, pow_zero, one_mul,
        Fin.prod_univ_one, Finset.prod_of_isEmpty, mul_one]
      rfl
  | (n + 1), b, d => by
      rw [qSum, adm_peel_sum b d]
      have hofn : List.ofFn b = b 0 :: List.ofFn (Fin.tail b) := by
        rw [← List.ofFn_cons, Fin.cons_self_tail]
      rw [hofn, transferRHS]
      refine Finset.sum_congr rfl fun x0 hx0 ↦ ?_
      rw [Finset.mem_range, Nat.lt_succ_iff, le_min_iff] at hx0
      obtain ⟨hx0b, hx0d⟩ := hx0
      -- IH on the tail transfer, then both sides are `∑_{y ∈ adm (tail b) (d - x0)}`
      rw [← qSum_eq_transferRHS (Fin.tail b) (d - x0), qSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y hy ↦ ?_
      rw [mem_adm] at hy
      obtain ⟨hysum, hyb⟩ := hy
      -- ∑ i, (cons x0 y) i.succ = ∑ y = d - x0
      have hyterm : (∑ i : Fin (n + 1), ((Fin.cons x0 y : Fin (n + 2) → ℕ) i.succ : ℤ))
          = ((d - x0 : ℕ) : ℤ) := by
        simp only [Fin.cons_succ]; rw [← Nat.cast_sum, hysum]
      -- flatDelta split
      have hytailb : ∀ i : Fin n, y i.castSucc ≤ Fin.tail b i := fun i ↦ by
        have := hyb i; simpa [Fin.tail] using this
      have hΔ : (flatDelta (n + 1) b (Fin.cons x0 y)).toNat
          = (b 0 - x0) * (d - x0) + (flatDelta n (Fin.tail b) y).toNat := by
        rw [flatDelta_succ,
          show (Fin.cons x0 y : Fin (n + 2) → ℕ) 0 = x0 from Fin.cons_zero _ _, hyterm,
          Fin.tail_cons]
        have hblk : ((b 0 : ℤ) - x0) * ((d - x0 : ℕ) : ℤ) = (((b 0 - x0) * (d - x0) : ℕ) : ℤ) := by
          rw [show ((b 0 : ℤ) - x0) = ((b 0 - x0 : ℕ) : ℤ) from by push_cast; omega, ← Nat.cast_mul]
        rw [hblk, Int.toNat_add (Int.natCast_nonneg _) (flatDelta_nonneg _ hytailb),
          Int.toNat_natCast]
      -- last-column P-factors: ∏ (cons x0 y) = P x0 · ∏ y
      have hcol : (∏ I : Fin (n + 2), P ((Fin.cons x0 y : Fin (n + 2) → ℕ) I))
          = P x0 * ∏ I : Fin (n + 1), P (y I) := by
        rw [Fin.prod_univ_succ, Fin.cons_zero]
        refine congrArg _ (Finset.prod_congr rfl fun i _ ↦ congrArg P (Fin.cons_succ _ _ _))
      -- merged-column P-factors: ∏ (b i − (cons x0 y) i.castSucc) = P (b 0 − x0) · ∏ (tail b − y)
      have hmerge : (∏ i : Fin (n + 1), P (b i - (Fin.cons x0 y : Fin (n + 2) → ℕ) i.castSucc))
          = P (b 0 - x0) * ∏ i : Fin n, P (Fin.tail b i - y i.castSucc) := by
        rw [Fin.prod_univ_succ,
          show (Fin.cons x0 y : Fin (n + 2) → ℕ) (Fin.castSucc 0) = x0 from by
              rw [Fin.castSucc_zero]; exact Fin.cons_zero _ _]
        refine congrArg _ (Finset.prod_congr rfl fun i _ ↦ ?_)
        rw [Fin.tail, show (Fin.cons x0 y : Fin (n + 2) → ℕ) i.succ.castSucc
              = y i.castSucc from by rw [← Fin.succ_castSucc]; exact Fin.cons_succ _ _ _]
      rw [hΔ, hcol, hmerge, pow_add]
      ring

/-- `innerSum` is the flat q-sum `qSum` of the column-`N` data: same index set (`admissibleXs_eq_adm`),
same P-factors (`col i = m'(i,N)`), same exponent (`innerSum_exp_eq_flatDelta`, using the per-`x` bound). -/
theorem innerSum_eq_qSum (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (dlast : ℕ) :
    innerSum m' dlast = qSum (fun i : Fin (N + 1) ↦ m' (i, Fin.last N)) dlast := by
  rw [innerSum, qSum, admissibleXs_eq_adm]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [mem_adm] at hx
  obtain ⟨_, hxb⟩ := hx
  rw [innerSum_exp_eq_flatDelta m' x hxb]

/-- **(Q)**: the per-fibre `innerSum` equals the last-column transfer `transferRHS` of the column-`N`
data — `innerSum = qSum` (`innerSum_eq_qSum`) then the q-series induction (`qSum_eq_transferRHS`). -/
theorem innerSum_eq_transferRHS (m' : Fin (N + 1) × Fin (N + 1) → ℕ) (dlast : ℕ) :
    innerSum m' dlast
      = transferRHS (List.ofFn (fun i : Fin (N + 1) ↦ m' (i, Fin.last N))) dlast := by
  rw [innerSum_eq_qSum, qSum_eq_transferRHS]

end DLNFibre.Core
