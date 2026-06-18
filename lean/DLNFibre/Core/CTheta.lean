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
`M = ⊕ M_{(a,b)}^{m_{ab}}`. Its identification with the **geometric** codimension of the rank-`r`
locus `Σ^r` (the orbit closure) rides on the DEFERRED Voigt hypothesis `hVoigt`
(`Core.OrbitCodim`); **the combinatorial `cCodim`/`numTop` here do NOT assert that geometric
identity** — they are min / minimiser-count of a ℤ-quadratic form over a finite set, nothing more.
Later layers reformulate `cCodim` as the QIP (Thm 6.1) and the explicit closest-lattice-point
formula (Thm 7.10).

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
`d` with corner `r`. Requires the partition set nonempty (`h`). NOT the geometric codimension of
`Σ^r` — that identification rests on the deferred `hVoigt` (see module docstring). -/
noncomputable def cCodim (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) : ℤ :=
  (kostantPartitions d r).inf' h (fun m ↦ codimForm N (extendℤ m))

/-- The **combinatorial component count** `θ`: the number of Kostant partitions of `d` with corner
`r` whose `codimForm` attains the minimum `cCodim d r h`. -/
noncomputable def numTop (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) : ℕ :=
  ((kostantPartitions d r).filter (fun m ↦ codimForm N (extendℤ m) = cCodim d r h)).card

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
partition (`mMin`): the combinatorial `θ = 1` (one minimiser). The geometric reading "the rank-`0`
locus has one top-dimensional component" rests on the deferred `hVoigt` (see module docstring). -/
theorem numTop_d222_zero : numTop d222 0 kostantPartitions_d222_nonempty = 1 := by
  decide +kernel

end Witness

end DLNFibre.Core
