import DLNFibre.Core.OrbitLinearCodim
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Nat

/-!
# `DLNFibre.Core.CTheta` — the combinatorial codimension `C` and component count `θ`

The paper's invariants `(C, θ)` of the rank-`r` product locus (Lehalleur–Rimányi 2024 §§5–7), here
defined **purely combinatorially** as the minimum and the minimiser-count of the committed Cor 3.5
quadratic form over the Kostant partitions of the dimension vector `d` with corner multiplicity
`m_{0N} = r`:

$$
C \;=\; \min_{\underline m}\ \sum_{1\le i\le u\le j\le v\le N} m_{i-1,j-1}\,m_{uv},
\qquad
\theta \;=\; \#\{\text{minimisers}\},
$$

where `m` ranges over `kostantPartitions d r`. Layer 1 of the `c-theta` expedition.

**Name = content (the load-bearing caveat).** `cCodim` and `numTop` are the **combinatorial** `C`
and `θ`: the minimum and minimiser-count of the *form* `codimForm`, over the Kostant partitions.
The form `codimForm N m` is **literally** the right-hand side of the committed headline
`Core.OrbitLinearCodim.orbitLinearCodim_eq_multSum` (and `finrank_deformationExt1_self_eq_multSum`)
(`codimForm_multiplicityArray` is `rfl` against it). That headline reads the form as the *expected*
(tangent / `Ext¹`) codimension `orbitLinearCodim M = dim Ext¹(M,M)` of the orbit of
`M = ⊕ M_{(a,b)}^{m_{ab}}`. Its identification with the **geometric** codimension of the orbit
closure `Ō_M` is now **PROVED** in `Core.CThetaGeometric` (`codimForm` = geometric
`codimRepCanonical (orbitRankLocus (⊕L))`, via the discharged Voigt lemma
`Core.VoigtDischarge.codimRep_orbitRankLocus_eq_orbitLinearCodim`, `[IsAlgClosed k] [CharZero k]`) —
no longer deferred. What is **NOT** asserted here, and stays open per the `Core.CThetaGeometric`
roadmap, is the **aggregate** reading: that `cCodim`/`numTop` are the geometric codimension / top
component count of the *whole* rank-`r` locus `Σ^r` (the union of orbit closures), which needs a
geometric definition of `Σ^r` and its orbit stratification. The combinatorial `cCodim`/`numTop`
here are min / minimiser-count of a ℤ-quadratic form over a finite set, nothing more; the proved
geometric reading is per-orbit (`Core.CThetaGeometric.cCodim_eq_inf_geomCodim`: `cCodim` = min over
partitions of the genuine geometric orbit-closure codimension). Later layers reformulate `cCodim` as
the QIP (Thm 6.1) and the explicit closest-lattice-point formula (Thm 7.10).

**Encoding.** A Kostant partition is encoded as a function `m : Fin (N+1) × Fin (N+1) → ℕ`
(the multiplicity `m_{ij}` of the interval module `M_{ij}`), required to vanish off `i ≤ j`. The
candidate universe is finite because `m_{ij} ≤ d_i` (the interval `[i,j]` covers vertex `i`), so
each entry lies in `Finset.range (d i + 1)`; `Fintype.piFinset` builds the bounded product and a
`Finset.filter` cuts out the Kostant constraint `d_k = ∑_{i ≤ k ≤ j} m_{ij}` and the corner
`m_{0,last} = r`. The form is evaluated on the ℤ-extension `extendℤ m` (`0` off the `Fin` box), so
`codimForm` reuses the *exact* index machinery of the committed headline.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Finset

variable {N : ℕ}

/-! ## The quadratic form (Cor 3.5), as a functional of the multiplicity array

`codimForm N m` is the committed Cor 3.5 right-hand side with the array abstracted out: the same
four nested `Finset.Icc` sums over `1 ≤ i ≤ u ≤ j ≤ v ≤ N`, same product `m (i-1) (j-1) * m u v`.
`codimForm_multiplicityArray` checks it is *literally* that headline form. -/

/-- The Cor 3.5 quadratic form on a ℤ-array `m`:
`∑_{1 ≤ i ≤ u ≤ j ≤ v ≤ N} m (i-1) (j-1) · m u v`. Abstracts the committed headline RHS
(`orbitLinearCodim_eq_multSum`) over the array, so it *is* that form (see
`codimForm_multiplicityArray`). -/
def codimForm (N : ℕ) (m : ℤ → ℤ → ℤ) : ℤ :=
  ∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
    ∑ v ∈ Finset.Icc j (N : ℤ),
      m (i - 1) (j - 1) * m u v

/-- **Cross-check: `codimForm` is literally the committed Cor 3.5 form.** On the multiplicity array
of any list `L`, `codimForm N (multiplicityArray L)` equals the headline right-hand side of
`orbitLinearCodim_eq_multSum` — `rfl`, since `codimForm` is that expression with the array
abstracted. -/
theorem codimForm_multiplicityArray (L : List (Fin (N + 1) × Fin (N + 1))) :
    codimForm N (multiplicityArray L)
      = ∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
          ∑ v ∈ Finset.Icc j (N : ℤ),
          multiplicityArray L (i - 1) (j - 1) * multiplicityArray L u v := rfl

/-! ## Kostant partitions of `d` with corner `r`

A partition `m : Fin (N+1) × Fin (N+1) → ℕ` is **Kostant for `d`** when it vanishes off `i ≤ j` and
`d k = ∑_{i ≤ k ≤ j} m (i,j)` for every vertex `k`; the corner is `m (0, last N)`. -/

/-- The ℤ-extension of a `Fin`-indexed partition `m`: `m` on the box `0 ≤ a ≤ b ≤ N`, else `0`.
Lets the `ℤ`-indexed `codimForm` consume a finite partition. -/
def extendℤ (m : Fin (N + 1) × Fin (N + 1) → ℕ) : ℤ → ℤ → ℤ :=
  fun a b ↦ if h : 0 ≤ a ∧ a ≤ b ∧ b ≤ (N : ℤ) then
    (m (⟨a.toNat, by omega⟩, ⟨b.toNat, by omega⟩) : ℤ) else 0

/-- The Kostant constraint at vertex `k`: `d k = ∑_{i ≤ k ≤ j} m (i,j)`, the sum of the
multiplicities of all interval modules `M_{ij}` whose support contains `k`. -/
def kostantAt (d : Fin (N + 1) → ℕ) (m : Fin (N + 1) × Fin (N + 1) → ℕ) (k : Fin (N + 1)) : Prop :=
  d k = ∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2), m p

instance (d : Fin (N + 1) → ℕ) (m : Fin (N + 1) × Fin (N + 1) → ℕ) (k : Fin (N + 1)) :
    Decidable (kostantAt d m k) := by unfold kostantAt; infer_instance

/-- The **Kostant partitions** of `d` with corner multiplicity `m_{0,last} = r`: functions
`m : Fin (N+1)² → ℕ` vanishing off `i ≤ j`, satisfying `d k = ∑_{i ≤ k ≤ j} m_{ij}` at every vertex
`k`, with `m (0, last N) = r`. A `Finset` cut from the bounded product whose `p`-carrier is
`Finset.range (d p.1 + 1)` on the triangle `p.1 ≤ p.2` (so `m_{ij} ≤ d_i`, since `i ∈ [i,j]`) and
`Finset.range 1 = {0}` off it (forcing `m_{ij} = 0` for `i > j`). The off-triangle clamp keeps the
candidate product small — only the upper-triangular entries vary — so the witness `decide` is cheap;
the support `m_{ij} = 0` for `i > j` then comes for free from carrier membership. -/
def kostantPartitions (d : Fin (N + 1) → ℕ) (r : ℕ) :
    Finset (Fin (N + 1) × Fin (N + 1) → ℕ) :=
  (Fintype.piFinset (fun p : Fin (N + 1) × Fin (N + 1) ↦
      if p.1 ≤ p.2 then Finset.range (d p.1 + 1) else Finset.range 1)).filter
    (fun m ↦ (∀ k, kostantAt d m k) ∧ m (0, Fin.last N) = r)

/-- Membership in `kostantPartitions`, unfolded: a partition is bounded `m_{ij} ≤ d_i`, supported on
`i ≤ j`, Kostant at every vertex, with corner `r`. The bound + support are carried by the product;
the `iff` exposes them in the same shape for downstream use. -/
theorem mem_kostantPartitions {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} :
    m ∈ kostantPartitions d r ↔
      (∀ p : Fin (N + 1) × Fin (N + 1), m p ≤ d p.1)
        ∧ (∀ p : Fin (N + 1) × Fin (N + 1), ¬ p.1 ≤ p.2 → m p = 0)
        ∧ (∀ k, kostantAt d m k)
        ∧ m (0, Fin.last N) = r := by
  unfold kostantPartitions
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hpi, hk, hc⟩
    refine ⟨fun p ↦ ?_, fun p hp ↦ ?_, hk, hc⟩
    · have := hpi p; split_ifs at this with h
      · simpa [Nat.lt_succ_iff] using this
      · simp only [Finset.mem_range, Nat.lt_one_iff] at this; omega
    · have := hpi p; rw [if_neg hp] at this
      simpa [Nat.lt_one_iff] using this
  · rintro ⟨hb, hs, hk, hc⟩
    refine ⟨fun p ↦ ?_, hk, hc⟩
    split_ifs with h
    · simp only [Finset.mem_range, Nat.lt_succ_iff]; exact hb p
    · simp only [Finset.mem_range, Nat.lt_one_iff]; exact hs p h

/-! ## `C` and `θ`

`cCodim d r` is the minimum of `codimForm` over the (nonempty) Kostant partitions of `d` with corner
`r`; `numTop d r` counts the minimisers. The nonemptiness is supplied as a hypothesis to `cCodim`
(via `Finset.min'`); `numTop` is unconditional (a `card`). -/

/-- The **combinatorial codimension** `C`: the minimum of `codimForm` over the Kostant partitions of
`d` with corner `r`. Requires the partition set nonempty (`h`). This is the minimum of the genuine
**geometric** orbit-closure codimensions (`Core.CThetaGeometric.cCodim_eq_inf_geomCodim`, proved);
it is NOT (yet) the geometric codimension of the *whole* rank-`r` locus `Σ^r` — that aggregate
reading awaits a geometric `Σ^r` (see `Core.CThetaGeometric` roadmap). -/
noncomputable def cCodim (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) : ℤ :=
  (kostantPartitions d r).inf' h (fun m ↦ codimForm N (extendℤ m))

/-- The **combinatorial component count** `θ`: the number of Kostant partitions of `d` with corner
`r` whose `codimForm` attains the minimum `cCodim d r h`. -/
noncomputable def numTop (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) : ℕ :=
  ((kostantPartitions d r).filter (fun m ↦ codimForm N (extendℤ m) = cCodim d r h)).card

/-! ## The rank-shift `cCodim d r = cCodim (d−r) 0` (Lehalleur–Rimányi Lemma 4.5)

The paper's rank-`r` → rank-`0` reduction: subtracting `r` copies of the all-covering interval
module `M_{0N}` (the projective-injective object, Thm 3.7) carries the rank-`r` orbit problem to the
zero-product one without changing `(C, θ)`. Combinatorially: the corner multiplicity `m_{0N}` is the
**only** entry `codimForm` never reads (every `m (u,v)` has `u ≥ 1 ≠ 0`; every `m (i-1,j-1)` has
`j-1 < N`), and `M_{0N}` covers every vertex, so the map `m ↦ Function.update m (0,last) 0` is a
`codimForm`-preserving bijection `kostantPartitions d r ≃ kostantPartitions (d−r) 0` (with
`d−r := fun k ↦ d k − r`, valid when `r ≤ d k` everywhere). Hence `cCodim` and `numTop` transport.

`codimForm`-blindness to the corner is `codimForm_update_corner`; the bijection is
`kostantEquivShift`; the conclusions are `cCodim_rankShift` / `numTop_rankShift`. **Proved**
(elementary `Finset` combinatorics; the per-orbit geometric reading of these combinatorial values
is now also proved, `Core.CThetaGeometric`). -/

/-- `extendℤ` is blind to a corner `update` (at `(0, last N)`) when the first index is `≥ 1`
(so `⟨a.toNat,_⟩ ≠ 0`): the updated and original arrays agree there. -/
theorem extendℤ_update_corner_of_fst_pos (m : Fin (N + 1) × Fin (N + 1) → ℕ) (c : ℕ)
    {a b : ℤ} (ha : 1 ≤ a) :
    extendℤ (Function.update m (0, Fin.last N) c) a b = extendℤ m a b := by
  unfold extendℤ
  split_ifs with h
  · rw [Function.update_apply, if_neg]
    rintro hpair
    have : (⟨a.toNat, by omega⟩ : Fin (N + 1)) = 0 := (Prod.mk.injEq .. ▸ hpair).1
    rw [Fin.ext_iff] at this; simp only [Fin.val_zero] at this; omega
  · rfl

/-- `extendℤ` is blind to a corner `update` (at `(0, last N)`) when the second index is `< N`
(so `⟨b.toNat,_⟩ ≠ Fin.last N`): the updated and original arrays agree there. -/
theorem extendℤ_update_corner_of_snd_lt (m : Fin (N + 1) × Fin (N + 1) → ℕ) (c : ℕ)
    {a b : ℤ} (hb : b < (N : ℤ)) :
    extendℤ (Function.update m (0, Fin.last N) c) a b = extendℤ m a b := by
  unfold extendℤ
  split_ifs with h
  · rw [Function.update_apply, if_neg]
    rintro hpair
    have : (⟨b.toNat, by omega⟩ : Fin (N + 1)) = Fin.last N := (Prod.mk.injEq .. ▸ hpair).2
    rw [Fin.ext_iff, Fin.val_last] at this; simp only at this; omega
  · rfl

/-- **`codimForm` is blind to the corner entry.** Updating `m` at `(0, last N)` to any `c` leaves
`codimForm N (extendℤ m)` unchanged: the form sums `m (i-1) (j-1) · m (u,v)` over
`1 ≤ i ≤ u ≤ j ≤ v ≤ N`, where the first factor has second index `j-1 < N` and the second factor has
first index `u ≥ 1`, so neither ever reads `(0, N)`. -/
theorem codimForm_update_corner (m : Fin (N + 1) × Fin (N + 1) → ℕ) (c : ℕ) :
    codimForm N (extendℤ (Function.update m (0, Fin.last N) c)) = codimForm N (extendℤ m) := by
  unfold codimForm
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun u hu ↦
    Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun v hv ↦ ?_
  rw [Finset.mem_Icc] at hi hu hj hv
  rw [extendℤ_update_corner_of_snd_lt m c (by omega),
      extendℤ_update_corner_of_fst_pos m c (by omega)]

/-! ### The corner-dropping bijection -/

/-- Drop the corner: set `m (0, last N)` to `0`. The map realising the rank-`r` → rank-`0` shift. -/
def dropCorner (m : Fin (N + 1) × Fin (N + 1) → ℕ) : Fin (N + 1) × Fin (N + 1) → ℕ :=
  Function.update m (0, Fin.last N) 0

/-- The shifted dimension vector `d − r`: `(d − r) k = d k − r` (ℕ truncated subtraction; honest
when `r ≤ d k`). -/
def dminus (d : Fin (N + 1) → ℕ) (r : ℕ) : Fin (N + 1) → ℕ := fun k ↦ d k - r

/-- The corner `(0, last N)` lies in the Kostant filter at every vertex `k` (the all-covering
interval `[0, N]` contains `k`). -/
theorem corner_mem_filter (k : Fin (N + 1)) :
    ((0 : Fin (N + 1)), Fin.last N) ∈
      Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, Fin.val_zero,
    Fin.val_last]
  exact ⟨Nat.zero_le _, Nat.le_of_lt_succ k.isLt⟩

/-- **Kostant filter sum after dropping the corner.** At every vertex `k`, the filtered sum of
`dropCorner m` is the filtered sum of `m` minus the corner value `m (0, last N)`. -/
theorem sum_filter_dropCorner (m : Fin (N + 1) × Fin (N + 1) → ℕ) (k : Fin (N + 1)) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2),
        dropCorner m p
      = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2), m p)
        - m (0, Fin.last N) := by
  set S := Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2) with hS
  have hc : ((0 : Fin (N + 1)), Fin.last N) ∈ S := corner_mem_filter k
  -- split the corner off both sums
  rw [← Finset.add_sum_erase S m hc, ← Finset.add_sum_erase S (dropCorner m) hc]
  -- `dropCorner m` is `0` at the corner and `= m` on the erased set
  have hcorner : dropCorner m (0, Fin.last N) = 0 := Function.update_self _ _ _
  have herase : ∀ p ∈ S.erase (0, Fin.last N), dropCorner m p = m p := by
    intro p hp
    exact Function.update_of_ne (Finset.ne_of_mem_erase hp) _ _
  rw [hcorner, Finset.sum_congr rfl herase, zero_add, Nat.add_sub_cancel_left]

/-- **The bound is a consequence of the Kostant constraint.** A partition supported on `i ≤ j` and
Kostant for `e` satisfies `m p ≤ e p.1` automatically: for `p.1 ≤ p.2` the entry `m p` is one
summand of the filtered sum `e p.1`; off the triangle `m p = 0`. -/
theorem bound_of_kostant {e : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hsupp : ∀ p, ¬ p.1 ≤ p.2 → m p = 0) (hk : ∀ k, kostantAt e m k)
    (p : Fin (N + 1) × Fin (N + 1)) :
    m p ≤ e p.1 := by
  by_cases hp : p.1 ≤ p.2
  · rw [hk p.1]
    refine Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_rfl, hp⟩
  · rw [hsupp p hp]; exact Nat.zero_le _

/-- **Dropping the corner lands in the shifted partitions.** If `m` is Kostant for `d` with corner
`r`, then `dropCorner m` is Kostant for `d − r` with corner `0`. (No `r ≤ d k` hypothesis: a Kostant
partition has corner `m_{0N} = r ≤ d k` at every vertex automatically, so `d k − r` is honest.) -/
theorem dropCorner_mem {d : Fin (N + 1) → ℕ} {r : ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hm : m ∈ kostantPartitions d r) :
    dropCorner m ∈ kostantPartitions (dminus d r) 0 := by
  rw [mem_kostantPartitions] at hm ⊢
  obtain ⟨-, hsupp, hk, hcorner⟩ := hm
  -- support of dropCorner: off the triangle it is m (= 0); at the corner it is 0
  have hsupp' : ∀ p, ¬ p.1 ≤ p.2 → dropCorner m p = 0 := by
    intro p hp
    by_cases hpc : p = (0, Fin.last N)
    · rw [hpc]; exact Function.update_self _ _ _
    · rw [dropCorner, Function.update_of_ne hpc]; exact hsupp p hp
  -- Kostant for d - r: filtered sum drops by m corner = r
  have hk' : ∀ k, kostantAt (dminus d r) (dropCorner m) k := by
    intro k
    rw [kostantAt, sum_filter_dropCorner, ← hk k, hcorner]; rfl
  exact ⟨bound_of_kostant hsupp' hk', hsupp', hk', Function.update_self _ _ _⟩

/-- **Restoring the corner inverts the drop.** If `m'` is Kostant for `d − r` with corner `0` (and
`r ≤ d k` everywhere), then `Function.update m' (0, last) r` is Kostant for `d` with corner `r`, and
dropping its corner returns `m'`. -/
theorem addCorner_mem {d : Fin (N + 1) → ℕ} {r : ℕ} {m' : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hr : ∀ k, r ≤ d k) (hm' : m' ∈ kostantPartitions (dminus d r) 0) :
    Function.update m' (0, Fin.last N) r ∈ kostantPartitions d r := by
  rw [mem_kostantPartitions] at hm' ⊢
  obtain ⟨-, hsupp, hk, hcorner⟩ := hm'
  set m := Function.update m' (0, Fin.last N) r with hmdef
  have hsupp' : ∀ p, ¬ p.1 ≤ p.2 → m p = 0 := by
    intro p hp
    have hpc : p ≠ (0, Fin.last N) := by
      rintro rfl; exact hp (by simp [Fin.le_def])
    rw [hmdef, Function.update_of_ne hpc]; exact hsupp p hp
  have hmc : m (0, Fin.last N) = r := Function.update_self _ _ _
  -- `dropCorner m = m'` since `m` is `m'` with the corner re-set, and `m'` has corner 0
  have hdrop : dropCorner m = m' := by
    funext q
    by_cases hqc : q = (0, Fin.last N)
    · subst hqc
      rw [dropCorner, Function.update_self, hcorner]
    · rw [dropCorner, Function.update_of_ne hqc, hmdef, Function.update_of_ne hqc]
  -- Kostant for d: the corner sum rises by r; m' was Kostant for d - r with corner 0
  have hk' : ∀ k, kostantAt d m k := by
    intro k
    -- ∑ filterₖ m' = ∑ filterₖ m − r   (drop the corner), and  d k − r = ∑ filterₖ m'
    have hdc : (∑ p ∈ Finset.univ.filter
          (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2), m' p)
        = (∑ p ∈ Finset.univ.filter
          (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2), m p) - r := by
      have := sum_filter_dropCorner m k
      rw [hdrop, hmc] at this; exact this
    have hk2 : d k - r = ∑ p ∈ Finset.univ.filter
        (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2), m' p := hk k
    -- corner ∈ filterₖ contributes `m corner = r`, so `r ≤ ∑ filterₖ m`
    have hge : r ≤ ∑ p ∈ Finset.univ.filter
        (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2), m p := by
      rw [← hmc]
      exact Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) (corner_mem_filter k)
    have hrk := hr k
    rw [kostantAt]; omega
  exact ⟨bound_of_kostant hsupp' hk', hsupp', hk', hmc⟩

/-- **The corner-dropping bijection (set form).** `kostantPartitions (d − r) 0` is the image of
`kostantPartitions d r` under `dropCorner` (for `r ≤ d k` everywhere) — the paper's rank-`r` →
rank-`0` reduction realised as a `Finset` bijection. -/
theorem kostantPartitions_dminus_eq_image {d : Fin (N + 1) → ℕ} {r : ℕ} (hr : ∀ k, r ≤ d k) :
    kostantPartitions (dminus d r) 0 = (kostantPartitions d r).image dropCorner := by
  ext m'
  rw [Finset.mem_image]
  constructor
  · intro hm'
    refine ⟨Function.update m' (0, Fin.last N) r, addCorner_mem hr hm', ?_⟩
    -- dropCorner (addCorner m') = m', since m' has corner 0
    have hcorner : m' (0, Fin.last N) = 0 := (mem_kostantPartitions.mp hm').2.2.2
    funext q
    by_cases hqc : q = (0, Fin.last N)
    · subst hqc
      rw [dropCorner, Function.update_self]; exact hcorner.symm
    · rw [dropCorner, Function.update_of_ne hqc, Function.update_of_ne hqc]
  · rintro ⟨m, hm, rfl⟩
    exact dropCorner_mem hm

/-- `dropCorner` is injective on `kostantPartitions d r`: its corner is fixed at `r`, so the corner
can be restored, recovering `m`. -/
theorem dropCorner_injOn {d : Fin (N + 1) → ℕ} {r : ℕ} :
    Set.InjOn dropCorner (kostantPartitions d r : Set (Fin (N + 1) × Fin (N + 1) → ℕ)) := by
  intro m₁ hm₁ m₂ hm₂ heq
  have hc₁ : m₁ (0, Fin.last N) = r := (mem_kostantPartitions.mp hm₁).2.2.2
  have hc₂ : m₂ (0, Fin.last N) = r := (mem_kostantPartitions.mp hm₂).2.2.2
  funext q
  by_cases hqc : q = (0, Fin.last N)
  · rw [hqc, hc₁, hc₂]
  · have := congrFun heq q
    rwa [dropCorner, Function.update_of_ne hqc, dropCorner, Function.update_of_ne hqc] at this

/-! ### The rank-shift conclusions -/

/-- **Rank-shift for `C` (Lehalleur–Rimányi Lemma 4.5).** The combinatorial codimension is unchanged
under the rank-`r` → rank-`0` reduction: `cCodim (d − r) 0 = cCodim d r` (for `r ≤ d k` everywhere).
`codimForm` is blind to the corner (`codimForm_update_corner`) and `dropCorner` is a bijection
`kostantPartitions d r ≃ kostantPartitions (d − r) 0`, so the minimum transports. -/
theorem cCodim_rankShift {d : Fin (N + 1) → ℕ} {r : ℕ} (hr : ∀ k, r ≤ d k)
    (h₀ : (kostantPartitions (dminus d r) 0).Nonempty)
    (hr' : (kostantPartitions d r).Nonempty) :
    cCodim (dminus d r) 0 h₀ = cCodim d r hr' := by
  have himg : ((kostantPartitions d r).image dropCorner).Nonempty := by
    rw [← kostantPartitions_dminus_eq_image hr]; exact h₀
  have h1 : ((kostantPartitions d r).image dropCorner).inf' himg (fun m ↦ codimForm N (extendℤ m))
      = (kostantPartitions d r).inf' himg.of_image
          ((fun m ↦ codimForm N (extendℤ m)) ∘ dropCorner) :=
    Finset.inf'_image himg _
  have h2 : (kostantPartitions d r).inf' himg.of_image
        ((fun m ↦ codimForm N (extendℤ m)) ∘ dropCorner)
      = (kostantPartitions d r).inf' hr' (fun m ↦ codimForm N (extendℤ m)) :=
    Finset.inf'_congr himg.of_image rfl (fun m _ ↦ codimForm_update_corner m 0)
  simpa only [cCodim, kostantPartitions_dminus_eq_image hr] using h1.trans h2

/-- **Rank-shift for `θ` (Lehalleur–Rimányi Lemma 4.5).** The combinatorial component count is
unchanged: `numTop (d − r) 0 = numTop d r` (for `r ≤ d k` everywhere). The minimiser set bijects
under the corner-dropping bijection, which preserves `codimForm` and (by `cCodim_rankShift`) the
minimum. -/
theorem numTop_rankShift {d : Fin (N + 1) → ℕ} {r : ℕ} (hr : ∀ k, r ≤ d k)
    (h₀ : (kostantPartitions (dminus d r) 0).Nonempty)
    (hr' : (kostantPartitions d r).Nonempty) :
    numTop (dminus d r) 0 h₀ = numTop d r hr' := by
  unfold numTop
  rw [cCodim_rankShift hr h₀ hr', kostantPartitions_dminus_eq_image hr, Finset.filter_image]
  -- the inner predicate `codimForm (dropCorner a) = …` equals `codimForm a = …` (corner-blind)
  have hfilter : ((kostantPartitions d r).filter
        (fun a ↦ codimForm N (extendℤ (dropCorner a)) = cCodim d r hr'))
      = (kostantPartitions d r).filter (fun m ↦ codimForm N (extendℤ m) = cCodim d r hr') :=
    Finset.filter_congr (fun m _ ↦ by
      rw [show dropCorner m = Function.update m (0, Fin.last N) 0 from rfl,
        codimForm_update_corner m 0])
  rw [hfilter]
  exact Finset.card_image_of_injOn (dropCorner_injOn.mono (fun m hm ↦ (Finset.mem_filter.mp hm).1))

/-! ## Non-vacuity witness — `(2,2,2)`, `r = 0` (Lehalleur–Rimányi Ex 4.3)

`N = 2`, `d = (2,2,2)`, corner `r = 0` (the zero-product / `Σ^0` case). There are exactly six
Kostant partitions; their `codimForm` values are `{4,3,5,4,5,8}`, so `C = 3` (the unique minimiser
is the `(1,1)`-orbit `m₀₀=m₀₁=m₁₂=m₂₂=1`) and `θ = 1`. `mMin` is the minimiser; the `Nonempty`
witness uses it, and `cCodim`/`numTop` evaluate by axiom-clean kernel `decide` over the product. -/

section Witness

/-- The `(2,2,2)` dimension vector. -/
abbrev d222 : Fin 3 → ℕ := ![2, 2, 2]

/-- The unique minimiser of `codimForm` among the Kostant partitions of `(2,2,2)` with `r = 0`: the
`(1,1)`-orbit `m₀₀ = m₀₁ = m₁₂ = m₂₂ = 1` (Ex 4.3), `codimForm = 3`. -/
def mMin : Fin 3 × Fin 3 → ℕ := fun p ↦
  if p = (0, 0) then 1 else if p = (0, 1) then 1
  else if p = (1, 2) then 1 else if p = (2, 2) then 1 else 0

/-- `mMin` is a Kostant partition of `(2,2,2)` with corner `r = 0`; in particular the set is
nonempty. -/
theorem mMin_mem : mMin ∈ kostantPartitions d222 0 := by
  rw [mem_kostantPartitions]; refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The Kostant partitions of `(2,2,2)` with corner `r = 0` form a nonempty set (`mMin` is one). -/
theorem kostantPartitions_d222_nonempty : (kostantPartitions d222 0).Nonempty :=
  ⟨mMin, mMin_mem⟩

/-- **`(2,2,2)`, `r = 0`: `C = 3`.** The minimum of the Cor 3.5 form over the six Kostant partitions
is `3`, attained at the `(1,1)`-orbit `mMin` (Lehalleur–Rimányi Ex 4.3). Axiom-clean kernel `decide`
over the bounded product. -/
theorem cCodim_d222_zero : cCodim d222 0 kostantPartitions_d222_nonempty = 3 := by
  decide +kernel

/-- **`(2,2,2)`, `r = 0`: `θ = 1`.** The minimum codimension `3` is attained at a unique Kostant
partition (`mMin`): the combinatorial `θ = 1` (one minimiser). The aggregate geometric reading "the
rank-`0` locus `Σ^0` has one top-dimensional component" is still OPEN — the component-count half
needs a geometric `Σ^0` and its orbit stratification (the `Core.CThetaGeometric` roadmap); the
per-orbit codimension reading there is proved. -/
theorem numTop_d222_zero : numTop d222 0 kostantPartitions_d222_nonempty = 1 := by
  decide +kernel

/-! ### Rank-shift witness — `(2,2,2)`, `r = 1` reduces to `(1,1,1)`, `r = 0`

`dminus ![2,2,2] 1 = ![1,1,1]` (pointwise `2 − 1`), and `1 ≤ 2` at every vertex, so the rank-shift
applies: `cCodim ![2,2,2] 1 = cCodim ![1,1,1] 0` and likewise for `numTop`. Both sides have
`C = 1, θ = 2`. -/

/-- A Kostant partition of `(2,2,2)` with corner `r = 1`: `m₀₁ = m₀₂ = m₂₂ = 1`. -/
def mShift : Fin 3 × Fin 3 → ℕ := fun p ↦
  if p = (0, 1) then 1 else if p = (0, 2) then 1 else if p = (2, 2) then 1 else 0

theorem mShift_mem : mShift ∈ kostantPartitions d222 1 := by
  rw [mem_kostantPartitions]; refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem kostantPartitions_d222_one_nonempty : (kostantPartitions d222 1).Nonempty :=
  ⟨mShift, mShift_mem⟩

/-- `1 ≤ d k` at every vertex of `(2,2,2)` — the rank-shift hypothesis. -/
theorem d222_one_le : ∀ k, (1 : ℕ) ≤ d222 k := by decide

theorem kostantPartitions_d222_dminus_nonempty :
    (kostantPartitions (dminus d222 1) 0).Nonempty := by
  rw [kostantPartitions_dminus_eq_image d222_one_le]
  exact kostantPartitions_d222_one_nonempty.image dropCorner

/-- **Rank-shift witness.** `(2,2,2)` at rank `1` reduces to `(1,1,1) = dminus ![2,2,2] 1` at rank
`0`: `cCodim (dminus ![2,2,2] 1) 0 = cCodim ![2,2,2] 1` (`= 1`), via `cCodim_rankShift`. -/
theorem cCodim_d222_one_rankShift :
    cCodim (dminus d222 1) 0 kostantPartitions_d222_dminus_nonempty
      = cCodim d222 1 kostantPartitions_d222_one_nonempty :=
  cCodim_rankShift d222_one_le _ _

/-- **`(2,2,2)`, `r = 1`: `C = 1`.** Concrete value of the rank-`1` codimension (matches the
`(1,1,1)`, `r = 0` value via `cCodim_d222_one_rankShift`). -/
theorem cCodim_d222_one : cCodim d222 1 kostantPartitions_d222_one_nonempty = 1 := by
  decide +kernel

/-- **`(2,2,2)`, `r = 1`: `θ = 2`.** Two top minimisers (matches `(1,1,1)`, `r = 0`). -/
theorem numTop_d222_one : numTop d222 1 kostantPartitions_d222_one_nonempty = 2 := by
  decide +kernel

end Witness

end DLNFibre.Core
