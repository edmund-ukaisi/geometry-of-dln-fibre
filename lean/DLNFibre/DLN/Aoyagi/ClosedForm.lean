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

**Selection surrogate (fidelity note).** The active-set size `ell`, ceiling `ceilingM`, and
residue `residueA` are built from the Lehalleur–Rimányi engine (`qipM`/`qipS`/`qipRound` on
`shiftedSorted`), NOT from Aoyagi's own Definition 3. They yield the same closed-form λ *value*
(verified: `2·lambdaCore = cValue` and `residueA·(ell − residueA) = |qipDelta|·(ell − |qipDelta|)`
across ~3000 inputs), but the intermediate `ell = qipM` need not equal Aoyagi's `Card(𝓜) − 1`
pointwise — e.g. at sorted shifted widths `(1,1,2)`, `qipM = 2` while Aoyagi's `ℓ = 1` (both give
the same λ; the formula is robust at the active/inactive boundary). For reference, Aoyagi's
Definition 3 inactive condition is misprinted as `∑ M^{(S_k)} ≤ (ℓ−1)M^{(s)}`; the consistent
reading (matching her own Theorem 1 case rule) is `≤ ℓ M^{(s)}`.
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

end Aoyagi

end DLNFibre.DLN
