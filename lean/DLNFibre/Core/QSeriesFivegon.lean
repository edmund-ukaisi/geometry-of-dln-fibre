import DLNFibre.Core.QSeriesPeel
import DLNFibre.Core.QSeriesExtraction

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
    show d k.castSucc = ∑ q ∈ coverF N k, peelPart m q
    rw [peelPart_cover_sum]
    exact hkk
  refine ⟨fun p ↦ ?_, peelPart_support hs, hk'⟩
  by_cases hp : p.1 ≤ p.2
  · have hkp := hk' p.1
    rw [kostantAt] at hkp
    show peelPart m p ≤ d (Fin.castSucc p.1)
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

end DLNFibre.Core
