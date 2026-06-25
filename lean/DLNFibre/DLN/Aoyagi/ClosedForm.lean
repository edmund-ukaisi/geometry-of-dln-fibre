import DLNFibre.Core.CThetaArbitrary
import DLNFibre.Core.FibreCodimFinal

/-!
# `DLNFibre.DLN.Aoyagi.ClosedForm` — Aoyagi's displayed closed formula

This file gives a source-shaped Lean surface for Aoyagi's formula in Theorem 2 of
`paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/`.

The formula is intentionally written with Aoyagi's variables:

* shifted widths `M^(s) = H^(s) - r`;
* active-set size `ell + 1`;
* ceiling integer `M`;
* residue `a = Σ M^(S_k) - (M - 1) ell`;
* the pair sum `Σ_{i<j} M^(S_i) M^(S_j)`;
* the rank shift `(-r^2 + r(H^(1)+H^(L+1)))/2`.

The existing formalisation computes the same integer codimension through `Core.cValue`.
The stubs below are the intended bridge: first the paper-shaped rational expression equals
`cValue / 2`, then the fibre codimension equals twice Aoyagi's `lambda` formula.

**Definition-by-definition recovery (fidelity, gap CLOSED).** The first surface (`ell`, `ceilingM`,
`residueA`, `lambda`) selects the active-set size with the Lehalleur–Rimányi threshold `ell = qipM`,
which is value-equivalent to but pointwise distinct from Aoyagi's own Definition 3 — e.g. at sorted
shifted widths `(1,1,2)`, `qipM = 2` while Aoyagi's `ℓ = 1` (both give the same λ). The
**`paper`-prefixed** surface below closes that gap: `paperEll` realises Aoyagi's *own* Definition 3
(`paperEll := max{l : qipA M l ≥ 1}`, the last index where the active threshold is *strict*),
**certified** as its unique solution by `isAoyagiEll_paperEll` / `paperEll_unique`, and
**`paperLambda_eq_lambda`** proves it gives the *identical* λ (turning the ~3000-input value check
into a theorem, via the zero-run step-invariance of `coreFormula`). `ell = qipM` is retained as the
computationally-convenient equal-valued handle. The corrected Definition-3 inactive condition fixes
the source misprint `∑ M^{(S_k)} ≤ (ℓ−1)M^{(s)}` to the consistent `≤ ℓ M^{(s)}` (matching her own
Theorem 1 case rule); `IsAoyagiEll` is Definition 3 read through its binding cases under sortedness
(active `qipA ℓ ≥ 1`, inactive `qipA (ℓ+1) ≤ 0`).
-/

namespace DLNFibre.DLN

open Finset
open Matrix DLNFibre.Core

namespace Aoyagi

variable {N : ℕ}

/-- The clamped index used to make the paper's `0..ell` sums total in Lean. -/
def clampedFin (N i : ℕ) : Fin (N + 1) :=
  ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩

/-- Aoyagi's shifted widths `M^(s) = H^(s) - r`, sorted into active-first order. -/
noncomputable def shiftedSorted (d : Fin (N + 1) → ℕ) (r : ℕ) : Fin (N + 1) → ℕ :=
  dminus d r ∘ _root_.Tuple.sort (dminus d r)

/-- The active-set size `ell` (Aoyagi's `Card(𝓜) − 1`), realised by the LR threshold `qipM` on the
sorted shifted widths. Surrogate: `ell = qipM` yields Aoyagi's λ value but need not equal her
`Card(𝓜) − 1` pointwise (see the module docstring). -/
noncomputable def ell (d : Fin (N + 1) → ℕ) (r : ℕ) : ℕ :=
  qipM (shiftedSorted d r)

/-- The paper's active shifted widths `M^(S_i)`, indexed as `i = 0, ..., ell`. -/
noncomputable def activeWidth (d : Fin (N + 1) → ℕ) (r i : ℕ) : ℤ :=
  shiftedSorted d r (clampedFin N i)

/-- The paper's `Σ_{k=1}^{ell+1} M^(S_k)`, written with zero-based active indices. -/
noncomputable def activeSum (d : Fin (N + 1) → ℕ) (r : ℕ) : ℤ :=
  qipS (shiftedSorted d r)

/-- Aoyagi's ceiling integer `M`, determined by `M - 1 < activeSum / ell ≤ M`. -/
noncomputable def ceilingM (d : Fin (N + 1) → ℕ) (r : ℕ) : ℤ :=
  (activeSum d r + (ell d r : ℤ) - 1) / (ell d r : ℤ)

/-- Aoyagi's residue `a = Σ M^(S_k) - (M - 1) ell`. -/
noncomputable def residueA (d : Fin (N + 1) → ℕ) (r : ℕ) : ℤ :=
  activeSum d r - (ceilingM d r - 1) * (ell d r : ℤ)

/-- The pair sum `Σ_{1 ≤ i < j ≤ ell+1} M^(S_i) M^(S_j)`, zero-based in Lean. -/
noncomputable def activePairSum (d : Fin (N + 1) → ℕ) (r : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (ell d r + 1),
    ∑ j ∈ Finset.Icc (i + 1) (ell d r), activeWidth d r i * activeWidth d r j

/-- The zero-rank part of Aoyagi's displayed `lambda` formula, evaluated on the LR engine's prefix
data (`ell = qipM` surrogate; equals Aoyagi's zero-rank λ *in value* — see the module note). -/
noncomputable def lambdaCore (d : Fin (N + 1) → ℕ) (r : ℕ) : ℚ :=
    ((residueA d r : ℚ) * ((ell d r : ℚ) - (residueA d r : ℚ))) / (4 * (ell d r : ℚ))
  - (((ell d r : ℚ) * ((ell d r : ℚ) - 1)) / 4)
      * (((activeSum d r : ℚ) / (ell d r : ℚ)) ^ 2)
  + (1 / 2 : ℚ) * (activePairSum d r : ℚ)

/-- The rank contribution `(-r^2 + r(H^(1)+H^(L+1)))/2` in Aoyagi's formula. -/
noncomputable def lambdaShift (d : Fin (N + 1) → ℕ) (r : ℕ) : ℚ :=
  (-((r : ℚ) ^ 2) + (r : ℚ) * ((d 0 : ℚ) + (d (Fin.last N) : ℚ))) / 2

/-- Aoyagi's full displayed `lambda` formula for an architecture and target rank, on the LR engine's
prefix data (`= Aoyagi's λ in value`; the intermediate `ell` is a surrogate — see module note). -/
noncomputable def lambda (d : Fin (N + 1) → ℕ) (r : ℕ) : ℚ :=
  lambdaShift d r + lambdaCore d r

/-- The corresponding integer codimension formula, i.e. `2 * lambda` in codimension units. -/
noncomputable def codimFormula (d : Fin (N + 1) → ℕ) (r : ℕ) : ℤ :=
  cValue (shiftedSorted d r) + ((r * (d 0 + d (Fin.last N) - r) : ℕ) : ℤ)

/-- The architecture-and-target-matrix version: the target matrix enters only through its rank. -/
noncomputable def codimOfTarget [Field k] (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) : ℤ :=
  codimFormula d B.rank

/-- The architecture-and-target-matrix version of Aoyagi's `lambda`. -/
noncomputable def lambdaOfTarget [Field k] (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) : ℚ :=
  lambda d B.rank

/-! ## Bridge statements to be discharged -/

/-- Aoyagi's ceiling convention agrees with the nearest-integer residue used by `Core.cValue`. -/
theorem residueA_mul_sub_eq_qipDelta_abs_mul_sub
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hN : 1 ≤ N) :
    residueA d r * ((ell d r : ℤ) - residueA d r)
      =
    |qipDelta (shiftedSorted d r)| *
      ((ell d r : ℤ) - |qipDelta (shiftedSorted d r)|) := by
  set M := shiftedSorted d r with hM
  -- `ell d r = qipM M`; fold the goal onto `M`.
  change residueA d r * ((qipM M : ℤ) - residueA d r)
    = |qipDelta M| * ((qipM M : ℤ) - |qipDelta M|)
  -- `ℓ = qipM M`, `S = qipS M`, residue `ρ = S % ℓ`, quotient `q = S / ℓ`.
  have hℓ1 : 1 ≤ qipM M := qipM_ge_one M hN
  set ℓ : ℤ := (qipM M : ℤ) with hℓ
  set S : ℤ := qipS M with hS
  have hℓ1' : 1 ≤ ℓ := by rw [hℓ]; exact_mod_cast hℓ1
  have hℓpos : 0 < ℓ := by omega
  -- The arithmetic residue `ρ := S % ℓ` (`0 ≤ ρ < ℓ`).
  have hρ0 : 0 ≤ S % ℓ := Int.emod_nonneg S (by omega)
  have hρlt : S % ℓ < ℓ := Int.emod_lt_of_pos S hℓpos
  have hdm : ℓ * (S / ℓ) + S % ℓ = S := Int.mul_ediv_add_emod S ℓ
  -- (a) `residueA ∈ {ρ, ℓ}`: `residueA = ρ` when `ρ > 0`, `= ℓ` when `ρ = 0`.
  have hresval : residueA d r = S % ℓ ∨ (residueA d r = ℓ ∧ S % ℓ = 0) := by
    have hreseq : residueA d r = S - (((S + ℓ - 1) / ℓ) - 1) * ℓ := rfl
    -- `ceilingM = ⌈S/ℓ⌉`: pin `(S+ℓ−1)/ℓ` by exhibiting its quotient/residue (cases on `S%ℓ`).
    rcases eq_or_lt_of_le hρ0 with hρeq | hρpos
    · -- `S % ℓ = 0`: `(S+ℓ−1)/ℓ = S/ℓ` (residue `ℓ−1`), residueA = `ℓ`.
      right
      have hdiv : (S + ℓ - 1) / ℓ = S / ℓ :=
        (Int.ediv_emod_unique hℓpos (r := ℓ - 1) (q := S / ℓ)).mpr
          ⟨by linarith [hdm], by omega, by omega⟩ |>.1
      rw [hreseq, hdiv]; refine ⟨?_, hρeq.symm⟩
      have : ℓ * (S / ℓ) = S := by linarith [hdm]
      nlinarith [this]
    · -- `S % ℓ ≥ 1`: `(S+ℓ−1)/ℓ = S/ℓ + 1` (residue `ρ−1`), residueA = `S % ℓ`.
      left
      have hdiv : (S + ℓ - 1) / ℓ = S / ℓ + 1 :=
        (Int.ediv_emod_unique hℓpos (r := S % ℓ - 1) (q := S / ℓ + 1)).mpr
          ⟨by nlinarith [hdm], by omega, by omega⟩ |>.1
      rw [hreseq, hdiv]
      have : ℓ * (S / ℓ) = S - S % ℓ := by linarith [hdm]
      nlinarith [this]
  -- (b) `|δ| ∈ {ρ, ℓ − ρ}`: `δ ≡ ρ (mod ℓ)` with `−ℓ ≤ 2δ ≤ ℓ−1`, `0 ≤ ρ < ℓ`.
  have habsval : |qipDelta M| = S % ℓ ∨ |qipDelta M| = ℓ - S % ℓ := by
    have hδdef : qipDelta M = S - ℓ * qipRound M := rfl
    have hbounds := two_qipDelta_bounds M hN
    rw [← hℓ] at hbounds
    -- `δ − ρ = ℓ·(S/ℓ − a)` is a multiple of `ℓ`.
    have hdivides : ℓ ∣ (qipDelta M - S % ℓ) := by
      refine ⟨S / ℓ - qipRound M, ?_⟩
      rw [hδdef]; linarith [hdm]
    obtain ⟨c, hc⟩ := hdivides
    -- `−ℓ ≤ 2δ ≤ ℓ−1`, `δ = ρ + ℓc`, `0 ≤ ρ < ℓ` force `c ∈ {0, −1}`.
    have hcle : c ≤ 0 := by nlinarith [hc, hbounds.2, hρ0, hℓ1']
    have hcge : -1 ≤ c := by nlinarith [hc, hbounds.1, hρlt, hℓ1']
    have hc01 : c = 0 ∨ c = -1 := by omega
    rcases hc01 with h0 | h1
    · left; rw [h0] at hc; have : qipDelta M = S % ℓ := by linarith [hc]
      rw [this, abs_of_nonneg hρ0]
    · right; rw [h1] at hc
      have hδneg : qipDelta M = S % ℓ - ℓ := by linarith [hc]
      rw [hδneg, abs_of_nonpos (by omega)]; ring
  -- Both products equal `ρ·(ℓ − ρ)`; `x ↦ x(ℓ−x)` is symmetric under `x ↦ ℓ − x`.
  rcases hresval with hr | ⟨hr, hρ0'⟩
  · rcases habsval with ha | ha
    · rw [hr, ha]
    · rw [hr, ha]; ring
  · rcases habsval with ha | ha
    · rw [hr, ha, hρ0']; ring
    · rw [hr, ha, hρ0']; ring

/-- **Square-of-sum split (range form).** `(∑_{range n} g)² = ∑_{range n} g² + 2·∑_{i<j} g_i g_j`,
the strict-upper-triangle pair sum written with an `if i < j` indicator over `range n × range n`. -/
theorem sq_sum_range_eq_sum_sq_add_two_pair (n : ℕ) (g : ℕ → ℤ) :
    (∑ i ∈ Finset.range n, g i) ^ 2
      = (∑ i ∈ Finset.range n, (g i) ^ 2)
        + 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
            (if i < j then g i * g j else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hpair : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if i < j then g i * g j else 0))
        = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < j then g i * g j else 0))
          + (∑ i ∈ Finset.range n, g i) * g n := by
      rw [Finset.sum_range_succ]
      have hrow : (∑ j ∈ Finset.range (n + 1), (if n < j then g n * g j else 0)) = 0 :=
        Finset.sum_eq_zero (fun j hj ↦ by rw [Finset.mem_range] at hj; rw [if_neg (by omega)])
      rw [hrow, add_zero]
      have hcol : ∀ i ∈ Finset.range n,
          (∑ j ∈ Finset.range (n + 1), (if i < j then g i * g j else 0))
            = (∑ j ∈ Finset.range n, (if i < j then g i * g j else 0)) + g i * g n :=
        fun i hi ↦ by rw [Finset.mem_range] at hi; rw [Finset.sum_range_succ, if_pos hi]
      rw [Finset.sum_congr rfl hcol, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hpair]; ring_nf; nlinarith [ih]

/-- **The pair-sum combinatorial identity.** `2·∑_{i∈range(n)} ∑_{j∈Icc(i+1)(n−1)} g_i g_j =
(∑ g)² − ∑ g²` — the `if i<j` indicator over `range n` collapses to `Icc (i+1) (n−1)`. -/
theorem two_pairSum_Icc_eq (n : ℕ) (g : ℕ → ℤ) :
    2 * (∑ i ∈ Finset.range n, ∑ j ∈ Finset.Icc (i + 1) (n - 1), g i * g j)
      = (∑ i ∈ Finset.range n, g i) ^ 2 - ∑ i ∈ Finset.range n, (g i) ^ 2 := by
  have hconv : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.Icc (i + 1) (n - 1), g i * g j)
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < j then g i * g j else 0) := by
    refine Finset.sum_congr rfl (fun i hi ↦ ?_)
    rw [Finset.mem_range] at hi
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr ?_ (fun j _ ↦ rfl)
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  rw [hconv, sq_sum_range_eq_sum_sq_add_two_pair]; ring

/-- The paper-shaped zero-rank summation formula is the existing `cValue / 2`. -/
theorem two_lambdaCore_eq_cValue
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hN : 1 ≤ N) :
    2 * lambdaCore d r = (cValue (shiftedSorted d r) : ℚ) := by
  set M := shiftedSorted d r with hM
  -- abbreviations matching the `qipS` / `cValue` clamped-index summand
  set ℓ : ℕ := qipM M with hℓ
  have hℓ1 : 1 ≤ ℓ := qipM_ge_one M hN
  have hℓN : ℓ ≤ N := qipM_le M
  set g : ℕ → ℤ := fun i ↦ (M ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ : ℤ) with hg
  -- `S = ∑_{range(ℓ+1)} g`, `Q := ∑_{range(ℓ+1)} g²`.
  set S : ℤ := qipS M with hS
  have hSsum : S = ∑ i ∈ Finset.range (ℓ + 1), g i := rfl
  set Q : ℤ := ∑ i ∈ Finset.range (ℓ + 1), (g i) ^ 2 with hQ
  -- `activeWidth d r i = g i` (same clamped index): `activePairSum = ∑_i∑_{Icc(i+1)ℓ} g_i g_j`.
  have haw : ∀ i, activeWidth d r i = g i := fun i ↦ rfl
  have hpairval : activePairSum d r
      = ∑ i ∈ Finset.range (ℓ + 1), ∑ j ∈ Finset.Icc (i + 1) ℓ, g i * g j := by
    rw [activePairSum]
    refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ by rw [haw, haw]))
  -- combinatorial identity at `n = ℓ+1` (so `n−1 = ℓ`): `2·activePairSum = S² − Q`.
  have hcomb : 2 * activePairSum d r = S ^ 2 - Q := by
    rw [hpairval, hSsum, hQ]
    have := two_pairSum_Icc_eq (ℓ + 1) g
    simpa using this
  -- `cValue`'s prefix sum: `∑_{Icc 1 ℓ}(g_i − g_0)² = Q + g_0² − 2 g_0 S + ℓ g_0²`.
  have hM0 : g 0 = (M 0 : ℤ) := by simp [hg]
  have hprefix : (∑ i ∈ Finset.Icc 1 ℓ, (g i - g 0) ^ 2)
      = Q - (g 0) ^ 2 - 2 * g 0 * (S - g 0) + (ℓ : ℤ) * (g 0) ^ 2 := by
    have hexp : ∀ i, (g i - g 0) ^ 2 = (g i) ^ 2 - 2 * g 0 * g i + (g 0) ^ 2 := fun i ↦ by ring
    rw [Finset.sum_congr rfl (fun i _ ↦ hexp i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    -- `range (ℓ+1) = insert 0 (Icc 1 ℓ)`: peel the `i = 0` term off `Q` and `S`.
    have hsplit : ∀ h : ℕ → ℤ,
        (∑ i ∈ Finset.range (ℓ + 1), h i) = h 0 + ∑ i ∈ Finset.Icc 1 ℓ, h i :=
      fun h ↦ by
        rw [show Finset.range (ℓ + 1) = insert 0 (Finset.Icc 1 ℓ) from ?_,
          Finset.sum_insert (by simp)]
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    have hQsplit : (∑ i ∈ Finset.Icc 1 ℓ, (g i) ^ 2) = Q - (g 0) ^ 2 := by
      rw [hQ, hsplit (fun i ↦ (g i) ^ 2)]; ring
    have hSsplit : (∑ i ∈ Finset.Icc 1 ℓ, g i) = S - g 0 := by
      rw [hSsum, hsplit g]; ring
    rw [hQsplit, hSsplit]; push_cast [show ℓ + 1 - 1 = ℓ from by omega]; ring
  -- The `residueA·(ℓ−residueA) = |δ|·(ℓ−|δ|)` bridge (part 1) and `δ = S − ℓ·a`, `|δ|² = δ²`.
  have hbridge := residueA_mul_sub_eq_qipDelta_abs_mul_sub d r hN
  rw [← hM] at hbridge
  -- `ell d r = qipM M = ℓ`; fold the bridge onto `ℓ`.
  have hell : (ell d r : ℤ) = (ℓ : ℤ) := rfl
  rw [hell] at hbridge
  have hδdef : qipDelta M = S - (ℓ : ℤ) * qipRound M := rfl
  have hδsq : |qipDelta M| ^ 2 = (qipDelta M) ^ 2 := sq_abs _
  -- `M` is monotone (`dminus ∘ Tuple.sort`), so `cValue`'s numerator is even: `2·cValue = num`.
  have hmono : Monotone M := by rw [hM, shiftedSorted]; exact _root_.Tuple.monotone_sort _
  have h2cvRaw : 2 * cValue M
      = (M 0 : ℤ) ^ 2
        - (∑ i ∈ Finset.Icc 1 ℓ,
            ((M ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ : ℤ) - (M 0 : ℤ)) ^ 2)
        + (ℓ : ℤ) * (qipRound M - (M 0 : ℤ)) ^ 2
        + 2 * (qipRound M - (M 0 : ℤ))
            * qipDelta M
        + |qipDelta M| := by
    rw [cValue_eq_Gqip_witness M hmono hN]
    exact (cValueNum_eq_two_Gqip_witness M hmono hN).symm
  -- The prefix sum over `Icc 1 ℓ` is `Q − g_0² − 2 g_0(S − g_0) + ℓ g_0²` (folded `hprefix`).
  have hpref0 : (∑ i ∈ Finset.Icc 1 ℓ,
        ((M ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ : ℤ) - (M 0 : ℤ)) ^ 2)
      = Q - (M 0 : ℤ) ^ 2 - 2 * (M 0 : ℤ) * (S - (M 0 : ℤ)) + (ℓ : ℤ) * (M 0 : ℤ) ^ 2 := by
    rw [← hM0]; exact hprefix
  have h2cv : 2 * cValue M
      = (M 0 : ℤ) ^ 2
        - (Q - (M 0 : ℤ) ^ 2 - 2 * (M 0 : ℤ) * (S - (M 0 : ℤ)) + (ℓ : ℤ) * (M 0 : ℤ) ^ 2)
        + (ℓ : ℤ) * (qipRound M - (M 0 : ℤ)) ^ 2
        + 2 * (qipRound M - (M 0 : ℤ)) * qipDelta M
        + |qipDelta M| := by rw [h2cvRaw, hpref0]
  -- The two integer equations + the residue facts pin `2·cValue` to a `Q,S,g 0,ℓ,a,δ` polynomial.
  have hℓQ : (0 : ℚ) < (ℓ : ℚ) := by exact_mod_cast hℓ1
  have hℓ0 : (ℓ : ℚ) ≠ 0 := ne_of_gt hℓQ
  -- Cast the integer facts to `ℚ`.
  have hcombQ : 2 * (activePairSum d r : ℚ) = (S : ℚ) ^ 2 - (Q : ℚ) := by exact_mod_cast hcomb
  have h2cvQ : 2 * (cValue M : ℚ)
      = (M 0 : ℚ) ^ 2 - ((Q : ℚ) - (M 0 : ℚ) ^ 2 - 2 * (M 0 : ℚ) * ((S : ℚ) - (M 0 : ℚ))
            + (ℓ : ℚ) * (M 0 : ℚ) ^ 2)
        + (ℓ : ℚ) * ((qipRound M : ℚ) - (M 0 : ℚ)) ^ 2
        + 2 * ((qipRound M : ℚ) - (M 0 : ℚ)) * (qipDelta M : ℚ)
        + |(qipDelta M : ℚ)| := by
    have hc : ((2 * cValue M : ℤ) : ℚ)
        = (((M 0 : ℤ) ^ 2
            - (Q - (M 0 : ℤ) ^ 2 - 2 * (M 0 : ℤ) * (S - (M 0 : ℤ)) + (ℓ : ℤ) * (M 0 : ℤ) ^ 2)
            + (ℓ : ℤ) * (qipRound M - (M 0 : ℤ)) ^ 2
            + 2 * (qipRound M - (M 0 : ℤ)) * qipDelta M
            + |qipDelta M| : ℤ) : ℚ) := by exact_mod_cast h2cv
    push_cast at hc
    linarith [hc]
  -- `δ = S − ℓ·a` and `a'(ℓ−a') = |δ|(ℓ−|δ|)` cast to ℚ; `|δ|² = δ²`.
  have hδdefQ : (qipDelta M : ℚ) = (S : ℚ) - (ℓ : ℚ) * (qipRound M : ℚ) := by exact_mod_cast hδdef
  have hbridgeQ : (residueA d r : ℚ) * ((ℓ : ℚ) - (residueA d r : ℚ))
      = |(qipDelta M : ℚ)| * ((ℓ : ℚ) - |(qipDelta M : ℚ)|) := by
    have : ((residueA d r * ((ℓ : ℤ) - residueA d r) : ℤ) : ℚ)
        = ((|qipDelta M| * ((ℓ : ℤ) - |qipDelta M|) : ℤ) : ℚ) := by exact_mod_cast hbridge
    push_cast at this
    linarith [this]
  have hδsqQ : |(qipDelta M : ℚ)| ^ 2 = (qipDelta M : ℚ) ^ 2 := sq_abs _
  -- Reduce `2·lambdaCore = cValue` by clearing the `4ℓ` denominator (cancel `4ℓ ≠ 0`).
  have h4ℓ : (4 : ℚ) * (ℓ : ℚ) ≠ 0 := by positivity
  rw [← mul_right_inj' h4ℓ]
  -- `4ℓ·(2·lambdaCore) = 2·residueA(ℓ−residueA) − 2(ℓ−1)S² + 4ℓ·activePairSum` (cleared).
  have hellQ : (ell d r : ℚ) = (ℓ : ℚ) := rfl
  have hactiveSumQ : (activeSum d r : ℚ) = (S : ℚ) := rfl
  have hlhs : 4 * (ℓ : ℚ) * (2 * lambdaCore d r)
      = 2 * ((residueA d r : ℚ) * ((ℓ : ℚ) - (residueA d r : ℚ)))
        - 2 * ((ℓ : ℚ) - 1) * (S : ℚ) ^ 2
        + 4 * (ℓ : ℚ) * (activePairSum d r : ℚ) := by
    rw [lambdaCore, hellQ, hactiveSumQ]; field_simp
  -- RHS: `4ℓ·cValue = 2ℓ·(2·cValue)`.
  have hrhs : 4 * (ℓ : ℚ) * (cValue M : ℚ) = 2 * (ℓ : ℚ) * (2 * (cValue M : ℚ)) := by ring
  rw [hlhs, hrhs, h2cvQ, hbridgeQ]
  -- `2·activePairSum = S²−Q`: rewrite the `4ℓ·activePairSum` term as `2ℓ·(2·activePairSum)`.
  rw [show 4 * (ℓ : ℚ) * (activePairSum d r : ℚ)
      = 2 * (ℓ : ℚ) * (2 * (activePairSum d r : ℚ)) from by ring, hcombQ]
  -- `|δ|(ℓ−|δ|) = |δ|ℓ − |δ|²`; substitute `|δ|² = δ²`, `δ = S − ℓa`. The linear `|δ|` cancels.
  rw [show |(qipDelta M : ℚ)| * ((ℓ : ℚ) - |(qipDelta M : ℚ)|)
      = |(qipDelta M : ℚ)| * (ℓ : ℚ) - |(qipDelta M : ℚ)| ^ 2 from by ring, hδsqQ, hδdefQ]
  ring

/-- The full Aoyagi formula is the integer codimension formula divided by two. The rank bound
`hr : r ≤ d 0 + d (Fin.last N)` is necessary: it ensures the shift term's `ℕ`-subtraction
`d 0 + d (Fin.last N) − r` does not truncate, so that `(r·(d 0 + d (Fin.last N) − r) : ℕ)` equals
`r·(d 0 + d (Fin.last N)) − r²` over `ℚ`. Without it the identity is false for `r > d 0 + d (last)`
(e.g. `d = ![1,1]`, `r = 3`: LHS `−3`, RHS `0`). In the fibre theorems the bound is supplied by the
Kostant nonemptiness `h` (`corner_le_dim_of_mem`). -/
theorem two_lambda_eq_codimFormula
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hN : 1 ≤ N) (hr : r ≤ d 0 + d (Fin.last N)) :
    2 * lambda d r = (codimFormula d r : ℚ) := by
  rw [lambda, mul_add, two_lambdaCore_eq_cValue d r hN, codimFormula]
  -- `2·lambdaShift = −r² + r(d₀+d_last)`; the shift `(r(d₀+d_last−r):ℕ):ℚ = r(d₀+d_last) − r²`.
  rw [lambdaShift]
  push_cast [Nat.cast_sub hr]
  ring

/-- The existing explicit `C` theorem, restated with the Aoyagi naming surface. -/
theorem cCodim_eq_aoyagi_cValue
    (hN : 1 ≤ N) (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) :
    cCodim d r h = cValue (shiftedSorted d r) := by
  simpa [shiftedSorted] using cCodim_eq_cValue_comp_sort hN d r h

/-- The existing closed form for `C + shift`, restated as Aoyagi's codimension formula. -/
theorem codimFormula_eq_cCodim_add_shift
    (hN : 1 ≤ N) (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) :
    codimFormula d r =
      cCodim d r h + ((r * (d 0 + d (Fin.last N) - r) : ℕ) : ℤ) := by
  rw [codimFormula, cCodim_eq_aoyagi_cValue hN d r h]

/-- Codimension of the multiplication fibre, stated directly with Aoyagi's codimension formula.
`k : Type` (universe 0) matches the Lehalleur–Rimányi engine's central theorem
(`Core.FibreCodimFinal.codimRepCanonical_fibre_eq_cCodim_add_shift`), which is stated at `Type`. -/
theorem codimRepCanonical_fibre_eq_aoyagiCodimFormula (k : Type)
    [Field k] [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r) :
    codimRepCanonical (fibre d B) = ((codimFormula d r).toNat : ℕ∞) := by
  -- `codim = C.toNat + shift`, `codimFormula = C + shift` with `0 ≤ C`, so the `toNat` splits.
  have hcodim := codimRepCanonical_fibre_eq_cCodim_add_shift d r h B hB
  have hform := codimFormula_eq_cCodim_add_shift (N := N + 1) (by omega) d r h
  rw [hcodim, hform]
  have hcc : 0 ≤ cCodim d r h := cCodim_nonneg h
  -- `(C + (n:ℤ)).toNat = C.toNat + n`; the shift summands agree (ℕ add-comm under the subtraction).
  rw [Int.toNat_add hcc (by positivity)]
  have hshift : (r * (d 0 + d (Fin.last (N + 1)) - r) : ℕ)
      = (r * (d (Fin.last (N + 1)) + d 0 - r) : ℕ) := by rw [Nat.add_comm (d 0)]
  rw [Int.toNat_natCast, hshift, Nat.cast_add]

/-- Codimension of the fibre, with the target matrix rank filled in automatically.
`k : Type` matches the Lehalleur–Rimányi engine (see `..._eq_aoyagiCodimFormula`). -/
theorem codimRepCanonical_fibre_eq_aoyagiCodimOfTarget (k : Type)
    [Field k] [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k)
    (h : (kostantPartitions d B.rank).Nonempty) :
    codimRepCanonical (fibre d B) = ((codimOfTarget d B).toNat : ℕ∞) := by
  simpa [codimOfTarget] using
    codimRepCanonical_fibre_eq_aoyagiCodimFormula k d B.rank h B rfl

/-- The same fibre codimension statement in Aoyagi's `lambda` units.
`k : Type` matches the Lehalleur–Rimányi engine (see `..._eq_aoyagiCodimFormula`). -/
theorem codimRepCanonical_fibre_eq_two_aoyagiLambda (k : Type)
    [Field k] [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r) :
    ((codimRepCanonical (fibre d B)).toNat : ℚ) = 2 * lambda d r := by
  -- rank bounds from Kostant nonemptiness: `r ≤ d 0` (and `≤ d_last`), so `r ≤ d 0 + d_last`.
  have hq : r ≤ d 0 := corner_le_dim_of_mem h.choose_spec 0
  have hr : r ≤ d 0 + d (Fin.last (N + 1)) := le_trans hq (Nat.le_add_right _ _)
  -- (4): `codim = (codimFormula).toNat` (a `ℕ` cast into `ℕ∞`); its `ℕ∞.toNat` peels back.
  rw [codimRepCanonical_fibre_eq_aoyagiCodimFormula k d r h B hB, ENat.toNat_coe]
  -- `0 ≤ codimFormula` (`= C + shift ≥ 0`), so `((codimFormula).toNat : ℚ) = (codimFormula : ℚ)`.
  have hcf0 : 0 ≤ codimFormula d r := by
    rw [codimFormula_eq_cCodim_add_shift (N := N + 1) (by omega) d r h]
    have := cCodim_nonneg h; positivity
  have hcast : (((codimFormula d r).toNat : ℕ) : ℚ) = (codimFormula d r : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hcf0
  rw [hcast]
  -- (3): `2·lambda = codimFormula` over ℚ.
  rw [two_lambda_eq_codimFormula d r (by omega) hr]

/-! ## Aoyagi's own Definition-3 active-set size `paperEll` (the closed fidelity gap)

The objects above select the active-set size with the Lehalleur–Rimányi threshold `ell = qipM`.
This section instead builds Aoyagi's *own* Definition-3 `ℓ` (`paperEll`) and proves it gives the
**identical** closed-form λ (`paperLambda_eq_lambda`), turning the value-equality across ~3000
inputs into a theorem and a definition-by-definition recovery of Aoyagi's closed form.

Everything is over a monotone `M : Fin (N + 1) → ℕ` (the running `shiftedSorted d r`). With
`qipA M l = (∑_{i=0}^l M_i) − l·M_l = T_l − l·M_l` (clamped, `Core.qipA`):

* `qipM M = Nat.findGreatest (0 ≤ qipA M ·) N` — last index with `qipA M · ≥ 0`;
* `paperEll M := Nat.findGreatest (1 ≤ qipA M ·) N` — last index with the active threshold *strict*.

`qipA M ·` is non-increasing for monotone `M` (`qipA_succ`/`qipA_antitone` below), so `paperEll ≤
qipM` and `qipA M j = 0` strictly between them — the zero-run that powers the step-invariance. -/

/-- **The `qipA` successor recurrence (general `l < N`).** `qipA M (l+1) = qipA M l −
l·(M_{l+1} − M_l)` (the clamps at `l` and `l+1` are inert below `N`). Generalises the existing
`Core.qipA_succ_qipM` (which fixes `l = qipM M`) needed for the antitone argument. -/
theorem qipA_succ (M : Fin (N + 1) → ℕ) {l : ℕ} (hl : l < N) :
    qipA M (l + 1)
      = qipA M l
        - (l : ℤ) * ((M ⟨l + 1, by omega⟩ : ℤ) - (M ⟨l, by omega⟩ : ℤ)) := by
  unfold qipA
  rw [Finset.sum_range_succ]
  have hl1 : (M ⟨min (l + 1) N, Nat.lt_succ_of_le (min_le_right (l + 1) N)⟩ : ℤ)
      = (M ⟨l + 1, by omega⟩ : ℤ) :=
    congrArg (fun x ↦ (M x : ℤ)) (Fin.ext (by simp [Nat.min_eq_left (by omega : l + 1 ≤ N)]))
  have hl0 : (M ⟨min l N, Nat.lt_succ_of_le (min_le_right l N)⟩ : ℤ) = (M ⟨l, by omega⟩ : ℤ) :=
    congrArg (fun x ↦ (M x : ℤ)) (Fin.ext (by simp [Nat.min_eq_left (by omega : l ≤ N)]))
  rw [hl1, hl0]; push_cast; ring

/-- **`qipA M ·` is non-increasing on `[0, N]`** for monotone `M`: `qipA M (l+1) ≤ qipA M l`
(`l < N`), since `l·(M_{l+1} − M_l) ≥ 0`. -/
theorem qipA_succ_le (M : Fin (N + 1) → ℕ) (hM : Monotone M) {l : ℕ} (hl : l < N) :
    qipA M (l + 1) ≤ qipA M l := by
  rw [qipA_succ M hl]
  have hmono : (M ⟨l, by omega⟩ : ℤ) ≤ (M ⟨l + 1, by omega⟩ : ℤ) := by
    have : M ⟨l, by omega⟩ ≤ M ⟨l + 1, by omega⟩ := hM (Fin.mk_le_mk.mpr (by omega))
    exact_mod_cast this
  have : (0 : ℤ) ≤ (l : ℤ) * ((M ⟨l + 1, by omega⟩ : ℤ) - (M ⟨l, by omega⟩ : ℤ)) := by
    have : (0 : ℤ) ≤ (M ⟨l + 1, by omega⟩ : ℤ) - (M ⟨l, by omega⟩ : ℤ) := by linarith
    positivity
  linarith

/-- **`qipA M ·` is antitone on `[a, b]` with `b ≤ N`.** For monotone `M`, `a ≤ b ≤ N ⟹
qipA M b ≤ qipA M a` (iterate `qipA_succ_le`). -/
theorem qipA_antitone (M : Fin (N + 1) → ℕ) (hM : Monotone M) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ N) : qipA M b ≤ qipA M a := by
  induction b with
  | zero => simp_all
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · have hba : a ≤ b := by omega
      exact le_trans (qipA_succ_le M hM (by omega)) (ih hba (by omega))
    · have : a = b + 1 := by omega
      rw [this]

/-- **The strict active predicate** `1 ≤ qipA M l` (Aoyagi's Definition-3 active threshold,
`T_l > l·M_l`; decidable). -/
def paperPred (M : Fin (N + 1) → ℕ) (l : ℕ) : Prop := 1 ≤ qipA M l

instance (M : Fin (N + 1) → ℕ) : DecidablePred (paperPred M) :=
  fun l ↦ inferInstanceAs (Decidable (1 ≤ qipA M l))

/-- **Aoyagi's Definition-3 active-set size** `paperEll M := max { l ≤ N : qipA M l ≥ 1 }` — the
last index where the active threshold is *strict* (`T_l > l·M_l`), as against `qipM`'s `≥ 0`. -/
noncomputable def paperEll (M : Fin (N + 1) → ℕ) : ℕ := Nat.findGreatest (paperPred M) N

/-- `paperEll M ≤ N`. -/
theorem paperEll_le (M : Fin (N + 1) → ℕ) : paperEll M ≤ N := Nat.findGreatest_le N

/-- `paperPred M 1` holds (`qipA M 1 = M 0 ≥ 1`) when `1 ≤ N` and `1 ≤ M 0`. -/
theorem paperPred_one (M : Fin (N + 1) → ℕ) (hN : 1 ≤ N) (hM0 : 1 ≤ M 0) : paperPred M 1 := by
  rw [paperPred, qipA_one M hN]; exact_mod_cast hM0

/-- `paperEll M ≥ 1` (the strict-active prefix is nonempty) when `1 ≤ N` and `1 ≤ M 0`. -/
theorem paperEll_ge_one (M : Fin (N + 1) → ℕ) (hN : 1 ≤ N) (hM0 : 1 ≤ M 0) : 1 ≤ paperEll M :=
  Nat.le_findGreatest hN (paperPred_one M hN hM0)

/-- **`paperEll` qualifies**: `1 ≤ qipA M (paperEll M)` when `1 ≤ N` and `1 ≤ M 0`. -/
theorem paperPred_paperEll (M : Fin (N + 1) → ℕ) (hN : 1 ≤ N) (hM0 : 1 ≤ M 0) :
    1 ≤ qipA M (paperEll M) :=
  Nat.findGreatest_spec hN (paperPred_one M hN hM0)

/-- `¬paperPred M l` for `paperEll M < l ≤ N` (`paperEll` is greatest). -/
theorem not_paperPred_of_gt (M : Fin (N + 1) → ℕ) {l : ℕ} (h : paperEll M < l) (h' : l ≤ N) :
    ¬ paperPred M l := Nat.findGreatest_is_greatest h h'

/-- **`paperEll ≤ qipM`** (`1 ≤ N`): a strict-active index (`qipA ≥ 1`) is in particular active
(`qipA ≥ 0`), so it lies in `qipM`'s qualifying prefix. -/
theorem paperEll_le_qipM (M : Fin (N + 1) → ℕ) (hN : 1 ≤ N) (hM0 : 1 ≤ M 0) :
    paperEll M ≤ qipM M := by
  refine Nat.le_findGreatest (paperEll_le M) ?_
  rw [qipPred]; linarith [paperPred_paperEll M hN hM0]

/-- **The zero-run.** For monotone `M` and `paperEll M < j ≤ qipM M`, `qipA M j = 0`: squeezed
between `0 ≤ qipA M j` (`j ≤ qipM`) and `qipA M j ≤ qipA M (paperEll+1) ≤ 0` (antitone +
`¬paperPred (paperEll+1)`). -/
theorem qipA_eq_zero_of_between (M : Fin (N + 1) → ℕ) (hM : Monotone M) (hN : 1 ≤ N)
    {j : ℕ} (hj1 : paperEll M < j) (hj2 : j ≤ qipM M) : qipA M j = 0 := by
  have hjN : j ≤ N := le_trans hj2 (qipM_le M)
  have hlow : 0 ≤ qipA M j := by
    -- `qipA` antitone + `qipA (qipM M) ≥ 0` (qipPred); `j ≤ qipM` gives `qipA j ≥ qipA qipM`.
    have hpred : 0 ≤ qipA M (qipM M) := qipPred_qipM M hN
    exact le_trans hpred (qipA_antitone M hM hj2 (qipM_le M))
  -- upper bound: `¬paperPred (paperEll+1)` gives `qipA (paperEll+1) ≤ 0`; antitone down to `j`.
  have hub : qipA M (paperEll M + 1) ≤ 0 := by
    have hpe1 : paperEll M + 1 ≤ N := by omega
    have := not_paperPred_of_gt M (by omega) hpe1
    rw [paperPred, not_le] at this; omega
  have hdown : qipA M j ≤ qipA M (paperEll M + 1) :=
    qipA_antitone M hM (by omega) hjN
  linarith

/-! ## The cutoff-parametrised core `coreFormula M ℓ`

Aoyagi's displayed zero-rank core as a function of a fixed monotone `M` and a *cutoff* `ℓ` (the
active-set size minus one). Specialising at `ℓ = qipM M` recovers the LR `lambdaCore`; at
`ℓ = paperEll M` it is `paperLambdaCore`. The proof that the two cutoffs give the same value is the
step-invariance below. -/

/-- The prefix sum `T_ℓ := ∑_{i=0}^{ℓ} M_i` (clamped index, total in `ℓ`). -/
noncomputable def coreActiveSum (M : Fin (N + 1) → ℕ) (ℓ : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (ℓ + 1), (M (clampedFin N i) : ℤ)

/-- The ceiling `⌈T_ℓ / ℓ⌉ = (T_ℓ + ℓ − 1) / ℓ` (Int division). -/
noncomputable def coreCeilingM (M : Fin (N + 1) → ℕ) (ℓ : ℕ) : ℤ :=
  (coreActiveSum M ℓ + (ℓ : ℤ) - 1) / (ℓ : ℤ)

/-- The residue `a := T_ℓ − (⌈T_ℓ/ℓ⌉ − 1)·ℓ`. -/
noncomputable def coreResidueA (M : Fin (N + 1) → ℕ) (ℓ : ℕ) : ℤ :=
  coreActiveSum M ℓ - (coreCeilingM M ℓ - 1) * (ℓ : ℤ)

/-- The pair sum `∑_{0 ≤ i < j ≤ ℓ} M_i M_j` (clamped indices). -/
noncomputable def coreActivePairSum (M : Fin (N + 1) → ℕ) (ℓ : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (ℓ + 1),
    ∑ j ∈ Finset.Icc (i + 1) ℓ, (M (clampedFin N i) : ℤ) * (M (clampedFin N j) : ℤ)

/-- Aoyagi's displayed zero-rank core at cutoff `ℓ`:
`a(ℓ−a)/(4ℓ) − (ℓ(ℓ−1)/4)(T_ℓ/ℓ)² + ½·pairSum`. -/
noncomputable def coreFormula (M : Fin (N + 1) → ℕ) (ℓ : ℕ) : ℚ :=
    ((coreResidueA M ℓ : ℚ) * ((ℓ : ℚ) - (coreResidueA M ℓ : ℚ))) / (4 * (ℓ : ℚ))
  - (((ℓ : ℚ) * ((ℓ : ℚ) - 1)) / 4) * (((coreActiveSum M ℓ : ℚ) / (ℓ : ℚ)) ^ 2)
  + (1 / 2 : ℚ) * (coreActivePairSum M ℓ : ℚ)

/-- **`lambdaCore` is `coreFormula` at the LR cutoff** `ℓ = qipM`. The LR `activeSum`/`residueA`/
`activePairSum` are exactly the `core*` data at `ℓ = qipM (shiftedSorted d r)` (definitional). -/
theorem lambdaCore_eq_coreFormula (d : Fin (N + 1) → ℕ) (r : ℕ) :
    lambdaCore d r = coreFormula (shiftedSorted d r) (qipM (shiftedSorted d r)) := by
  rfl

/-! ## Aoyagi's own-Definition-3 closed-form objects (`paper` prefix)

Mirror the LR objects with `paperEll` in place of `ell = qipM`; the rank shift `lambdaShift` is
ℓ-independent and is shared. -/

/-- The active sum `∑_{i=0}^{paperEll} M_i` over Aoyagi's Definition-3 prefix. -/
noncomputable def paperActiveSum (d : Fin (N + 1) → ℕ) (r : ℕ) : ℤ :=
  coreActiveSum (shiftedSorted d r) (paperEll (shiftedSorted d r))

/-- Aoyagi's ceiling integer over her Definition-3 prefix. -/
noncomputable def paperCeilingM (d : Fin (N + 1) → ℕ) (r : ℕ) : ℤ :=
  coreCeilingM (shiftedSorted d r) (paperEll (shiftedSorted d r))

/-- Aoyagi's residue over her Definition-3 prefix. -/
noncomputable def paperResidueA (d : Fin (N + 1) → ℕ) (r : ℕ) : ℤ :=
  coreResidueA (shiftedSorted d r) (paperEll (shiftedSorted d r))

/-- The pair sum over Aoyagi's Definition-3 prefix. -/
noncomputable def paperActivePairSum (d : Fin (N + 1) → ℕ) (r : ℕ) : ℤ :=
  coreActivePairSum (shiftedSorted d r) (paperEll (shiftedSorted d r))

/-- Aoyagi's zero-rank core with her own Definition-3 active-set size. -/
noncomputable def paperLambdaCore (d : Fin (N + 1) → ℕ) (r : ℕ) : ℚ :=
  coreFormula (shiftedSorted d r) (paperEll (shiftedSorted d r))

/-- Aoyagi's full displayed `lambda` with her own Definition-3 active-set size (shared shift). -/
noncomputable def paperLambda (d : Fin (N + 1) → ℕ) (r : ℕ) : ℚ :=
  lambdaShift d r + paperLambdaCore d r

/-! ## Certification: `paperEll` realises Aoyagi's Definition 3

Aoyagi's Definition 3 reads, through its binding cases under sortedness: the active threshold is
*strict* up to `ℓ` (`T_ℓ > ℓ·M_ℓ`, i.e. `qipA M ℓ ≥ 1`) and *fails* one step further
(`T_ℓ ≤ ℓ·M_{ℓ+1}`, i.e. `qipA M (ℓ+1) ≤ 0`) unless `ℓ = N`. Her per-element conditions collapse to
these two by monotonicity: condition (ii) over the active widths binds hardest at the *largest*
active `M_ℓ`, the inactive condition over the inactive widths binds hardest at the *smallest*
inactive `M_{ℓ+1}`. (Aoyagi writes `𝓜` as a *set*; the faithful reading is the indexed prefix —
duplicate widths each contribute to `T_ℓ` — which the indexed `M : Fin (N+1) → ℕ` summed over
indices realises directly.) This is the corrected reading of the misprinted inactive bound
`(ℓ−1)→ℓ` (flagged in the module docstring) — matching her own Theorem-1 case rule. `paperEll` is
the **unique** solution. -/

/-- **Aoyagi's Definition-3 active-set predicate**, reduced to its binding inequalities (active
`qipA M ℓ ≥ 1`, inactive `qipA M (ℓ+1) ≤ 0` unless `ℓ = N`). -/
def IsAoyagiEll (M : Fin (N + 1) → ℕ) (l : ℕ) : Prop :=
  1 ≤ qipA M l ∧ (l = N ∨ qipA M (l + 1) ≤ 0)

/-- **Existence.** `paperEll M` satisfies Aoyagi's Definition-3 conditions (`1 ≤ N`, `1 ≤ M 0`). -/
theorem isAoyagiEll_paperEll (M : Fin (N + 1) → ℕ) (hN : 1 ≤ N) (hM0 : 1 ≤ M 0) :
    IsAoyagiEll M (paperEll M) := by
  refine ⟨paperPred_paperEll M hN hM0, ?_⟩
  rcases eq_or_lt_of_le (paperEll_le M) with hEq | hLt
  · exact Or.inl hEq
  · refine Or.inr ?_
    have := not_paperPred_of_gt M (by omega) (by omega : paperEll M + 1 ≤ N)
    rw [paperPred, not_le] at this; omega

/-- **Uniqueness.** On the domain `l ≤ N` (with monotone `M`, `1 ≤ N`, `1 ≤ M 0`), Aoyagi's
Definition-3 conditions pin `l = paperEll M` — the two binding inequalities + antitonicity of
`qipA M ·` admit no other active-set size. -/
theorem paperEll_unique (M : Fin (N + 1) → ℕ) (hM : Monotone M) (hN : 1 ≤ N) (hM0 : 1 ≤ M 0)
    {l : ℕ} (hl : l ≤ N) (hAoyagi : IsAoyagiEll M l) : l = paperEll M := by
  obtain ⟨hactive, hinactive⟩ := hAoyagi
  -- `l ≤ paperEll`: `l` is a strict-active index in `[0, N]`.
  have hle : l ≤ paperEll M := Nat.le_findGreatest hl hactive
  -- `paperEll ≤ l`: else `qipA (l+1) ≤ 0` (inactive) antitonically forces `qipA paperEll ≤ 0`.
  have hge : paperEll M ≤ l := by
    by_contra hlt
    rw [not_le] at hlt
    have hlN : l < N := lt_of_lt_of_le hlt (paperEll_le M)
    have hzero : qipA M (l + 1) ≤ 0 := hinactive.resolve_left (by omega)
    have hdown : qipA M (paperEll M) ≤ qipA M (l + 1) :=
      qipA_antitone M hM (by omega) (by have := paperEll_le M; omega)
    linarith [paperPred_paperEll M hN hM0]
  omega

/-! ## Step-invariance of `coreFormula` across a zero of `qipA`

The crux: when `qipA M (ℓ+1) = 0` (the running average `M_{ℓ+1} = T_ℓ/ℓ` is an integer, the
inactive boundary), advancing the cutoff `ℓ → ℓ+1` leaves `coreFormula` unchanged. Both residue
terms vanish (`a = ℓ`, `a' = ℓ+1`), and the change in the quadratic term `−(ℓ(ℓ−1)/4)(S/ℓ)²`
exactly cancels the change `+(ℓ/2)(S/ℓ)²` in `½·pairSum`. -/

/-- **`coreActiveSum` successor** (`ℓ+1 ≤ N`): `T_{ℓ+1} = T_ℓ + M_{ℓ+1}` (clamp inert at `ℓ+1`). -/
theorem coreActiveSum_succ (M : Fin (N + 1) → ℕ) {ℓ : ℕ} (hℓ : ℓ + 1 ≤ N) :
    coreActiveSum M (ℓ + 1) = coreActiveSum M ℓ + (M ⟨ℓ + 1, by omega⟩ : ℤ) := by
  unfold coreActiveSum
  rw [Finset.sum_range_succ]
  have : (M (clampedFin N (ℓ + 1)) : ℤ) = (M ⟨ℓ + 1, by omega⟩ : ℤ) :=
    congrArg (fun x ↦ (M x : ℤ)) (Fin.ext (by simp [clampedFin, Nat.min_eq_left hℓ]))
  rw [this]

/-- **`qipA` via `coreActiveSum`** (`ℓ+1 ≤ N`): `qipA M (ℓ+1) = T_ℓ − ℓ·M_{ℓ+1}`. So `qipA M (ℓ+1) =
0 ⟺ T_ℓ = ℓ·M_{ℓ+1}` (the integer running-average condition). -/
theorem qipA_succ_eq_coreActiveSum (M : Fin (N + 1) → ℕ) {ℓ : ℕ} (hℓ : ℓ + 1 ≤ N) :
    qipA M (ℓ + 1) = coreActiveSum M ℓ - (ℓ : ℤ) * (M ⟨ℓ + 1, by omega⟩ : ℤ) := by
  -- `coreActiveSum M ℓ` is the `qipA`-style prefix sum (clampedFin = the `min`-mk index).
  have hpref : coreActiveSum M ℓ
      = ∑ i ∈ Finset.range (ℓ + 1),
          (M ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ : ℤ) := rfl
  unfold qipA
  rw [Finset.sum_range_succ, hpref]
  have hcl : (M ⟨min (ℓ + 1) N, Nat.lt_succ_of_le (min_le_right (ℓ + 1) N)⟩ : ℤ)
      = (M ⟨ℓ + 1, by omega⟩ : ℤ) :=
    congrArg (fun x ↦ (M x : ℤ)) (Fin.ext (by simp [Nat.min_eq_left hℓ]))
  rw [hcl]; push_cast; ring

/-- **`coreActivePairSum` successor** (`ℓ+1 ≤ N`): advancing the cutoff adds the new row `j = ℓ+1`
against every `i ≤ ℓ`, i.e. `+ M_{ℓ+1}·T_ℓ`. The new `i = ℓ+1` row is empty (`Icc (ℓ+2) (ℓ+1) =
∅`); each old `i`-row gains the single `j = ℓ+1` term. -/
theorem coreActivePairSum_succ (M : Fin (N + 1) → ℕ) {ℓ : ℕ} (hℓ : ℓ + 1 ≤ N) :
    coreActivePairSum M (ℓ + 1)
      = coreActivePairSum M ℓ + (M ⟨ℓ + 1, by omega⟩ : ℤ) * coreActiveSum M ℓ := by
  -- `coreActiveSum M ℓ = ∑_{range(ℓ+1)} M(clampedFin N i)` (definitional), and `M(clampedFin (ℓ+1))
  -- = M⟨ℓ+1⟩` (clamp inert at `ℓ+1`).
  have hpref : coreActiveSum M ℓ
      = ∑ i ∈ Finset.range (ℓ + 1), (M (clampedFin N i) : ℤ) := rfl
  have hcl' : (M (clampedFin N (ℓ + 1)) : ℤ) = (M ⟨ℓ + 1, by omega⟩ : ℤ) :=
    congrArg (fun x ↦ (M x : ℤ)) (Fin.ext (by simp [clampedFin, Nat.min_eq_left hℓ]))
  unfold coreActivePairSum
  -- peel the new `i = ℓ+1` outer term (empty inner Icc), then the new `j = ℓ+1` per old row.
  rw [Finset.sum_range_succ]
  have hempty : (∑ j ∈ Finset.Icc (ℓ + 1 + 1) (ℓ + 1),
      (M (clampedFin N (ℓ + 1)) : ℤ) * (M (clampedFin N j) : ℤ)) = 0 := by
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
  rw [hempty, add_zero]
  -- each old row `i ∈ range(ℓ+1)`: `Icc(i+1)(ℓ+1) = insert (ℓ+1) (Icc(i+1)ℓ)`, peel `j = ℓ+1`.
  have hrow : ∀ i ∈ Finset.range (ℓ + 1),
      (∑ j ∈ Finset.Icc (i + 1) (ℓ + 1), (M (clampedFin N i) : ℤ) * (M (clampedFin N j) : ℤ))
        = (∑ j ∈ Finset.Icc (i + 1) ℓ, (M (clampedFin N i) : ℤ) * (M (clampedFin N j) : ℤ))
          + (M (clampedFin N i) : ℤ) * (M (clampedFin N (ℓ + 1)) : ℤ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show Finset.Icc (i + 1) (ℓ + 1) = insert (ℓ + 1) (Finset.Icc (i + 1) ℓ) from ?_,
      Finset.sum_insert (by simp)]
    · ring
    · ext j; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, hcl', hpref, ← Finset.sum_mul, mul_comm]

/-- **Residue at an exact multiple.** If `T_ℓ = ℓ·w` (the running average is the integer `w`) and
`1 ≤ ℓ`, then `coreCeilingM M ℓ = w` and so `coreResidueA M ℓ = ℓ`: the residue is *full*, killing
the term `a(ℓ−a)/(4ℓ)`. -/
theorem coreResidueA_eq_of_exact (M : Fin (N + 1) → ℕ) {ℓ : ℕ} (w : ℤ) (hℓ : 1 ≤ ℓ)
    (hexact : coreActiveSum M ℓ = (ℓ : ℤ) * w) :
    coreResidueA M ℓ = (ℓ : ℤ) := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hℓ
  have hℓpos : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ
  -- `coreCeilingM = (ℓw + ℓ − 1)/ℓ = w`: write `ℓw + ℓ − 1 = (ℓ−1) + w·ℓ`, `0 ≤ ℓ−1 < ℓ`.
  have hceil : coreCeilingM M ℓ = w := by
    rw [coreCeilingM, hexact]
    rw [show (ℓ : ℤ) * w + (ℓ : ℤ) - 1 = ((ℓ : ℤ) - 1) + w * (ℓ : ℤ) from by ring,
      Int.add_mul_ediv_right _ _ hℓ0,
      Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]
  rw [coreResidueA, hexact, hceil]; ring

/-- **Step-invariance (the crux).** If `qipA M (ℓ+1) = 0` (the running average `M_{ℓ+1} = T_ℓ/ℓ` is
an integer) and `1 ≤ ℓ`, advancing the cutoff `ℓ → ℓ+1` leaves `coreFormula` unchanged. Both
residue terms vanish (`a = ℓ`, `a' = ℓ+1`); the quadratic term changes by `−(ℓ/2)(T_ℓ/ℓ)²` and the
`½·pairSum` term gains `+(ℓ/2)(T_ℓ/ℓ)²`, cancelling. -/
theorem coreFormula_step_invariant (M : Fin (N + 1) → ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓN : ℓ + 1 ≤ N)
    (hzero : qipA M (ℓ + 1) = 0) :
    coreFormula M ℓ = coreFormula M (ℓ + 1) := by
  set w : ℤ := (M ⟨ℓ + 1, by omega⟩ : ℤ) with hw
  -- `qipA (ℓ+1) = 0` ⟹ `T_ℓ = ℓ·w` (the integer running average).
  have hSℓ : coreActiveSum M ℓ = (ℓ : ℤ) * w := by
    have := qipA_succ_eq_coreActiveSum M hℓN
    rw [hzero] at this; rw [← hw] at this; linarith
  -- `T_{ℓ+1} = (ℓ+1)·w`.
  have hSℓ1 : coreActiveSum M (ℓ + 1) = ((ℓ : ℤ) + 1) * w := by
    rw [coreActiveSum_succ M hℓN, hSℓ, ← hw]; ring
  -- residues are full: `a = ℓ`, `a' = ℓ+1`.
  have hAℓ : coreResidueA M ℓ = (ℓ : ℤ) := coreResidueA_eq_of_exact M w hℓ hSℓ
  have hAℓ1 : coreResidueA M (ℓ + 1) = ((ℓ : ℕ) + 1 : ℤ) := by
    have := coreResidueA_eq_of_exact M w (ℓ := ℓ + 1) (by omega)
      (by rw [hSℓ1]; push_cast; ring)
    rw [this]; push_cast; ring
  -- pair-sum gains `w·T_ℓ = ℓ·w²`.
  have hPℓ1 : coreActivePairSum M (ℓ + 1) = coreActivePairSum M ℓ + w * ((ℓ : ℤ) * w) := by
    rw [coreActivePairSum_succ M hℓN, hSℓ, ← hw]
  -- assemble over ℚ: cast the integer identities, clear `4ℓ` and `4(ℓ+1)`.
  rw [coreFormula, coreFormula]
  have hℓQ : (0 : ℚ) < (ℓ : ℚ) := by exact_mod_cast hℓ
  have hℓ1Q : (0 : ℚ) < ((ℓ : ℚ) + 1) := by positivity
  have hcastℓ1 : (((ℓ + 1 : ℕ) : ℤ) : ℚ) = (ℓ : ℚ) + 1 := by push_cast; ring
  -- push the ℤ facts to ℚ.
  have hSℓQ : (coreActiveSum M ℓ : ℚ) = (ℓ : ℚ) * (w : ℚ) := by exact_mod_cast hSℓ
  have hSℓ1Q : (coreActiveSum M (ℓ + 1) : ℚ) = ((ℓ : ℚ) + 1) * (w : ℚ) := by exact_mod_cast hSℓ1
  have hAℓQ : (coreResidueA M ℓ : ℚ) = (ℓ : ℚ) := by exact_mod_cast hAℓ
  have hAℓ1Q : (coreResidueA M (ℓ + 1) : ℚ) = (ℓ : ℚ) + 1 := by
    rw [show (coreResidueA M (ℓ + 1) : ℚ) = (((ℓ + 1 : ℕ) : ℤ) : ℚ) from by exact_mod_cast hAℓ1]
    exact hcastℓ1
  have hPℓ1Q : (coreActivePairSum M (ℓ + 1) : ℚ)
      = (coreActivePairSum M ℓ : ℚ) + (w : ℚ) * ((ℓ : ℚ) * (w : ℚ)) := by exact_mod_cast hPℓ1
  -- `(ℓ+1 : ℕ) : ℚ = ℓ+1` in the cast `coreActiveSum`/`coreResidueA` indices; rewrite all.
  rw [hAℓQ, hAℓ1Q, hSℓQ, hSℓ1Q, hPℓ1Q]
  -- the cast of `(ℓ+1 : ℕ)` appearing as the `(↑(ℓ+1) : ℚ)` coefficient factors:
  push_cast
  field_simp
  ring

/-! ## Assembling `paperLambdaCore = lambdaCore` (the core equality) -/

/-- **The zero-run telescope.** For monotone `M` (`1 ≤ N`, `1 ≤ M 0`), `coreFormula` is constant
across the whole run `paperEll → qipM` where `qipA M ·` vanishes: `coreFormula M (paperEll M) =
coreFormula M (qipM M)`. (Iterates the step-invariance; the run can have length > 1.) -/
theorem coreFormula_paperEll_eq_qipM (M : Fin (N + 1) → ℕ) (hM : Monotone M) (hN : 1 ≤ N)
    (hM0 : 1 ≤ M 0) :
    coreFormula M (paperEll M) = coreFormula M (qipM M) := by
  have hle : paperEll M ≤ qipM M := paperEll_le_qipM M hN hM0
  have hpe1 : 1 ≤ paperEll M := paperEll_ge_one M hN hM0
  -- telescope: `coreFormula (paperEll) = coreFormula (paperEll + k)` for every reachable `k`.
  have hstep : ∀ k : ℕ, paperEll M + k ≤ qipM M →
      coreFormula M (paperEll M) = coreFormula M (paperEll M + k) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hkle : paperEll M + k ≤ qipM M := by omega
      rw [ih hkle]
      -- the step `paperEll+k → paperEll+k+1` is a zero-step (qipA vanishes above paperEll).
      have hzero : qipA M (paperEll M + k + 1) = 0 :=
        qipA_eq_zero_of_between M hM hN (by omega) (by omega)
      have hℓN : paperEll M + k + 1 ≤ N := le_trans hk (qipM_le M)
      exact coreFormula_step_invariant M (by omega) hℓN hzero
  have := hstep (qipM M - paperEll M) (by omega)
  rwa [show paperEll M + (qipM M - paperEll M) = qipM M from by omega] at this

/-- **`cValue` vanishes when the corner is zero.** If `M 0 = 0` then `cValue M = 0`: the feasible
face `{e : ∑ e = M 0 = 0}` is the singleton `{0}`, so `qipMin M = Gqip M 0 = 0` (`qipMin_eq_cValue`
folds it onto `cValue`). -/
theorem cValue_eq_zero_of_corner_zero (M : Fin (N + 1) → ℕ) (hM : Monotone M) (hM0 : M 0 = 0) :
    cValue M = 0 := by
  -- the feasible face is the singleton `{0}` (the only ℕ-vector summing to `M 0 = 0`).
  have hsingle : qipFeasible M = {(0 : Fin N → ℕ)} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · rw [qipFeasible, Finset.mem_finAntidiagonal, hM0]; simp
    · intro e he
      rw [qipFeasible, Finset.mem_finAntidiagonal, hM0] at he
      funext i
      have : e i ≤ ∑ j, e j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      rw [he] at this; simpa using Nat.le_zero.mp this
  have hne : (qipFeasible M).Nonempty := ⟨0, by rw [hsingle]; exact Finset.mem_singleton_self _⟩
  have hmin := qipMin_eq_cValue M hM hne
  -- `Gqip M 0 = 0` and the feasible face is `{0}`, so `qipMin = 0`.
  have hG0 : Gqip M (0 : Fin N → ℕ) = 0 := by simp [Gqip]
  have h0feas : (0 : Fin N → ℕ) ∈ qipFeasible M := by
    rw [hsingle]; exact Finset.mem_singleton_self _
  have hqm0 : qipMin M hne = 0 := by
    refine le_antisymm ?_ ?_
    · rw [qipMin]; exact le_trans (Finset.inf'_le _ h0feas) (le_of_eq hG0)
    · rw [qipMin]; refine Finset.le_inf' _ _ (fun b hb ↦ ?_)
      rw [hsingle, Finset.mem_singleton] at hb; rw [hb, hG0]
  rw [← hmin, hqm0]

/-- **The core equality (unconditional).** Aoyagi's own-Definition-3 core equals the LR core:
`paperLambdaCore d r = lambdaCore d r`. Cases on the corner `shiftedSorted d r 0`: when `≥ 1`, both
are `coreFormula` and the zero-run telescope identifies the two cutoffs; when `= 0`, `paperEll = 0`
and both cores are `0` (the latter via `cValue_eq_zero_of_corner_zero`). -/
theorem paperLambdaCore_eq_lambdaCore (d : Fin (N + 1) → ℕ) (r : ℕ) :
    paperLambdaCore d r = lambdaCore d r := by
  set M := shiftedSorted d r with hM
  have hmono : Monotone M := by rw [hM, shiftedSorted]; exact _root_.Tuple.monotone_sort _
  rw [paperLambdaCore, lambdaCore_eq_coreFormula, ← hM]
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- `N = 0`: `paperEll = qipM = 0` (both `≤ N = 0`); the cutoffs coincide.
    have hpe : paperEll M = 0 := Nat.le_zero.mp (hN0 ▸ paperEll_le M)
    have hqm : qipM M = 0 := Nat.le_zero.mp (hN0 ▸ qipM_le M)
    rw [hpe, hqm]
  rcases Nat.lt_or_ge 0 (M 0) with hpos | hzero
  · -- `1 ≤ M 0`: the zero-run telescope.
    exact coreFormula_paperEll_eq_qipM M hmono hNpos hpos
  · -- `M 0 = 0`: `paperEll = 0` and both cores are `0`.
    have hM00 : M 0 = 0 := Nat.le_zero.mp hzero
    -- `paperEll = 0`: no `l ∈ [1, N]` is strict-active (`qipA M l ≤ qipA M 1 = M 0 = 0 < 1`).
    have hpe0 : paperEll M = 0 := by
      rw [paperEll, Nat.findGreatest_eq_zero_iff]
      intro m hm0 hmN
      rw [paperPred, not_le]
      have hA1 : qipA M 1 = (M 0 : ℤ) := qipA_one M hNpos
      have hdown : qipA M m ≤ qipA M 1 := qipA_antitone M hmono (by omega) hmN
      rw [hA1, hM00, Nat.cast_zero] at hdown; omega
    -- `paperLambdaCore` (`= coreFormula M 0`) is `0`.
    have hcore0 : coreFormula M 0 = 0 := by
      simp [coreFormula, coreActiveSum, coreResidueA, coreCeilingM, coreActivePairSum, hM00,
        clampedFin]
    -- `lambdaCore` (`= coreFormula M (qipM M) = cValue/2`) is `0`.
    have hlam0 : coreFormula M (qipM M) = 0 := by
      have h2 : 2 * coreFormula M (qipM M) = (cValue M : ℚ) := by
        rw [← lambdaCore_eq_coreFormula]
        rcases Nat.lt_or_ge 0 N with hN1 | hN1
        · exact two_lambdaCore_eq_cValue d r hN1
        · omega
      rw [cValue_eq_zero_of_corner_zero M hmono hM00] at h2
      simpa using h2
    rw [hpe0, hcore0, hlam0]

/-! ## Capstone: definition-by-definition Aoyagi recovery -/

/-- **`paperLambda = lambda`** — Aoyagi's full displayed λ with her *own* Definition-3 active-set
size equals the Lehalleur–Rimányi-engine λ, unconditionally. (The rank shift `lambdaShift` is
ℓ-independent and shared; the cores agree by `paperLambdaCore_eq_lambdaCore`.) -/
theorem paperLambda_eq_lambda (d : Fin (N + 1) → ℕ) (r : ℕ) : paperLambda d r = lambda d r := by
  rw [paperLambda, lambda, paperLambdaCore_eq_lambdaCore]

/-- **The headline: codim = 2·(Aoyagi's λ with her own Definition-3 ℓ).** The multiplication-fibre
codimension is twice Aoyagi's displayed λ formula evaluated with `paperEll` (Definition 3), a
definition-by-definition recovery of her closed form (certified by `isAoyagiEll_paperEll` /
`paperEll_unique`). `k : Type` matches the Lehalleur–Rimányi engine (see
`..._eq_aoyagiCodimFormula`). -/
theorem codimRepCanonical_fibre_eq_two_paperLambda (k : Type)
    [Field k] [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r) :
    ((codimRepCanonical (fibre d B)).toNat : ℚ) = 2 * paperLambda d r := by
  rw [paperLambda_eq_lambda]
  exact codimRepCanonical_fibre_eq_two_aoyagiLambda k d r h B hB

end Aoyagi

end DLNFibre.DLN
