import DLNFibre.DLN.RLCT.Validate.MinAdmPermInvariance

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJWaistCharge` — the waist charge identity (hole (c), step 4)

**Thread `genm-sj5-waist` (aoyagi-full Stage 2), CONTRACT-FIRST skeleton for `DecoratedStepHyp` hole (c)
`deeperFlagWaist_finite` (the WAIST branch, `M₁ ≠ 1`).** This module is the SPECIFY artifact for the
route-A **SVD-qPeel** waist resolution: it banks the ELEMENTARY combinatorial bridge (step 4, below) and
documents the precise build-path + seam map the controller adjudicates before the analytic tide.

## The target (hole (c), from `RouteMSJDecoratedStep`)

`deeperFlagWaist_finite`: for a `≥ 3`-width chain `M : Fin (L+1+1+1) → ℕ` in the WAIST regime
`hwaist : M 1 < deepTailMin M` (`= M₁ < min(M₂,…,M_last)`) with `hM1 : M 1 ≠ 1`, GIVEN the DECORATED
strong IH (`hIH`, finiteness for every `adm`-admissible decoration of every ONE-LAYER-SHORTER chain),
every `adm`-admissible `D : SJDecoration M` is `DecoratedBoxThresholdFinite` (finite below
`carrierThreshold M = ½·minAdm M`).

## The route (scout `genm-sj5-domination` route-A cert + `svd-density-mathlib-recon`, decorrelated-Codex)

The head-split (front-peel) route has a GENUINE pivot wall on waist chains (the `u·ρ < minAdm(redChain)`
obstruction; the co-minimizer does not rescue it — `tobl3b-routeB-reversal-cert`, 0/35). Route-B ("peel
the better end") is REFUTED as a complete cover: the palindrome `(2,1,2)` is head-split-divergent from
BOTH ends, and hole (c) at `L = 0` INCLUDES 3-width both-ends-bad waists (e.g. `(3,2,3)`, `M₁ = 2 ≠ 1`,
palindrome, NO good end) that reversal cannot orient. So the SOUND route is **route-A SVD-qPeel DIRECT**,
with the arity recursion (peel a good END of a `≥ 4`-width chain — every one has a head-split-good end —
down to the 3-width waist LEAF) reaching a 3-width base discharged by SVD-qPeel.

At `L = 0` (3-width `(x,s,z)`, `A₀ : x×s`, `A₁ : s×z`, waist `s < z`, `s = M₁ ≥ 2`):

1. **Loss identity** `‖A₀A₁‖² = Σⱼ σⱼ²·‖A₀uⱼ‖²` — **BANKED** `RouteMSJFrontSpectral.frobSq_mul_eq_sum_eigenvalues`
   (Gram spectral of `A₁A₁ᵀ`, no SVD needed).
2. **Deep-layer eigenvalue-marginal density / Jacobian** (`dA₁ ∝ ∏|σᵢ²−σⱼ²|·∏σⱼ^{z−s} dσ dU dV`, Weyl
   majorant `∏|σᵢ²−σⱼ²| ≤ ∏σⱼ^{2(s−j)}`) — **the ONE genuinely-new brick.** The LITERAL rectangular-SVD /
   Wishart density is a HEAVY new-module WALL (Mathlib v4.29 has NO Stiefel manifold, NO Haar-on-O(s), NO
   eigenvalue Jacobian, NO Vandermonde density, NO coarea, NOT even eigenvalue-map differentiability —
   `svd-density-mathlib-recon`, decorrelated-Codex CONCURS). The MODERATE bypass (decorrelated-Codex,
   `codex/wall-assessment-answer.md`, §3, worked out for `(3,2,3)`): the **max-pivot Schur-flag CoV** —
   peel `A₁`'s own corank one direction at a time by a Schur chart ON `A₁` (pivot its invertible `k×k`
   block; the Schur complement is a RATIONAL/POLYNOMIAL map, Jacobian a `det(pivot)`-power, amenable to
   the banked `MeasureTheory.Function.Jacobian`), depth `≤ s`, bottom leaves `s = 1`-like. The `(3,2,3)`
   deciding chart (6-dim, `|det DΦ| = |p|³`, `h₁ = 3`) is one ordinary CoV. This is a MODERATE new module,
   NOT a wall — but it is the crux the controller must scope (its exact statement + the decoration
   threading are the seam being checkpointed).
3. **A₀-frame integration** (`A₀ ↦ A₀U` measure-preserving, `|det U| = 1`, box-frame constant) — **BANKED**
   `RouteMSJOrthoExtend.exists_ortho_ext` + `RouteMSJFrontSpectral.lintegral_comp_orthRightMulₚ` (sidesteps
   Haar-on-O(s) on the A₀ side).
4. **Exponent truncation + the charge identity** `Σ_{j=1}^s min(x, z+s+1−2j) = minAdm(x,s,z)` (for `s ≤ z`)
   — **ELEMENTARY, banked HERE** (`waistCharge_eq_minAdm`). This is what makes the qPeel threshold
   `½·Σ min(x, hⱼ+1) = ½·minAdm` TIGHT (0 violations over 936 triples `s ≤ z`). The `min(x, ·)` cap is the
   monomial truncation `σ^{hᵢ} ≤ σ^{min(hᵢ, x−1)}` on `[0,1]`.
5. **The corner qPeel** `RouteMSJCorankQ.qPeelIntegral_lt_top` — **BANKED, sorry-free** (finite for
   `c' < ½·Σ(hᵢ+1)` under the per-block gate `hᵢ ≤ mᵢ`).
6. **The shell cover** `RouteMSJShellCover.{singularShell,singularShell_iUnion,lintegral_le_sum_finCover}`
   — **BANKED** (or a single ordered-chamber qPeel).

Plus, for the DECORATED integral (`SJDecoration.integral`, not the bare box): the `adm = genuineCarrier ∧
FaithfulSJAt` structure threads through — `d = 0` collapses to the plain box loss (`trivial_decLoss`),
`d ≥ 1` carries the `commonDivisor(u)²·frobSq(Γ·Z_tail)` form (`gammaPrimeClause`). The decoration
threading of the SVD-qPeel is part of step 2's scope.

## Status (checkpoint deliverable)

* **`waistCharge_eq_minAdm`** — the step-4 charge identity, PROVED sorry-free here (axiom-clean
  `[propext, Classical.choice, Quot.sound]`). Elementary ℕ: `minAdm = gCrux s z x`, matched to the
  sum-of-mins at the arithmetic-series crossing.
* **Step 2 (the deep-layer eigenvalue-density brick)** — the LITERAL rectangular-SVD / Wishart density is
  a WALL at v4.29; the max-pivot Schur-flag CoV bypass is the route. Its DECIDING `(3,2,3)` chart is
  PROTOTYPED sorry-free in the sibling `RouteMSJWaistSchurChart` (`schurChart_cov`, `|det| = |p|³`), so
  the bypass is confirmed BOUNDED (one ordinary `MeasureTheory.Function.Jacobian` CoV, no SVD density).

UNTRACKED, NOT wired into `DLNFibre.lean`/`AxCheck` — the canonical library stays 0-sorry.

### Proof sketch for `waistCharge_eq_minAdm` (Codex-confirmed, `codex/wall-assessment-answer.md` §5)

`minAdm ![x,s,z] = gCrux x s z = gCrux s z x` (`minAdm_comp_perm` at the 3-cycle `finRotate 3`; the
front-peel value of `(s,z,x)`). `gCrux s z x = ⨅_{k=0}^{s} [(s−k)(z−k) + k·x]` (since `s ≤ z`,
`min s z = s`). Put `g(k) = k·x + (s−k)(z−k)`; then `g(k+1) − g(k) = x − (z+s−1−2k)`, so `g` decreases
exactly while the next arithmetic-series term `z+s−1−2k` exceeds `x`. At the crossing `k₀`,
`⨅_k g(k) = k₀·x + Σ_{j=k₀+1}^s (z+s+1−2j) = Σ_{j=1}^s min(x, z+s+1−2j)`, using the arithmetic-series tail
`Σ_{j∈Ico k s} (z+s−1−2j) = (s−k)(z−k)` (downward `Ico`-induction) and the antitone prefix/suffix split of
`range s` at `k₀ = #{j : x ≤ z+s−1−2j}` (min resolves to `x` on the prefix, to `z+s−1−2j` on the suffix).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators
open Finset

/-- **The waist charge** `Σ_{j=1}^s min(x, z+s+1−2j)`, reindexed `j' = j−1` over `range s`
(`z+s+1−2(j'+1) = z+s−1−2j'`). On the waist domain `s ≤ z` every summand is `≥ z−s+1 ≥ 1`, so the ℕ
subtraction is exact. This is the additive per-singular-mode charge of the deep-layer SVD-qPeel: mode `j`
contributes `min(x, hⱼ+1)` with `hⱼ+1 = z+s+1−2j` the truncated Weyl-Jacobian axis exponent, `x` the deep
Morse block width. Its sum equals `minAdm` (`waistCharge_eq_minAdm`), making the qPeel threshold tight. -/
def waistCharge (x s z : ℕ) : ℕ := ∑ j ∈ Finset.range s, min x (z + s - 1 - 2 * j)

/-- **The arithmetic-series tail** `Σ_{j∈[k,s)} (z+s−1−2j) = (s−k)(z−k)` (for `k ≤ s ≤ z`). The suffix of
the truncated Weyl-Jacobian axis exponents sums to the corner-cell parabola `(s−k)(z−k)` — the piece the
charge identity's crossing argument consumes. Proved over `ℤ` (all summands are exact on `s ≤ z`) via
`sum_Ico_eq_sum_range` + the Gauss triangular sum, then cast back. -/
theorem waist_tailSum {s z : ℕ} (hsz : s ≤ z) {k : ℕ} (hk : k ≤ s) :
    ∑ j ∈ Finset.Ico k s, (z + s - 1 - 2 * j) = (s - k) * (z - k) := by
  have hSS : 2 * (∑ i ∈ Finset.range (s - k), (i : ℤ))
      = ((s - k : ℕ) : ℤ) * (((s - k : ℕ) : ℤ) - 1) := by
    have hraw := Finset.sum_range_id_mul_two (s - k)
    have h2 : ((∑ i ∈ Finset.range (s - k), i : ℕ) : ℤ) * 2 = (((s - k) * (s - k - 1) : ℕ) : ℤ) := by
      exact_mod_cast hraw
    rw [Nat.cast_sum] at h2
    rcases Nat.eq_zero_or_pos (s - k) with hm | hm
    · rw [hm]; simp
    · rw [Nat.cast_mul, Nat.cast_sub hm] at h2; push_cast at h2 ⊢; linarith
  have hcast : ((∑ j ∈ Finset.Ico k s, (z + s - 1 - 2 * j) : ℕ) : ℤ)
      = ((s : ℤ) - k) * ((z : ℤ) - k) := by
    rw [Nat.cast_sum]
    have hterm : ∀ j ∈ Finset.Ico k s,
        ((z + s - 1 - 2 * j : ℕ) : ℤ) = (z : ℤ) + s - 1 - 2 * j := by
      intro j hj; rw [Finset.mem_Ico] at hj; omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_Ico_eq_sum_range]
    have hterm2 : ∀ i ∈ Finset.range (s - k),
        ((z : ℤ) + s - 1 - 2 * ((k + i : ℕ) : ℤ)) = ((z : ℤ) + s - 1 - 2 * k) - 2 * i := by
      intro i _; push_cast; ring
    rw [Finset.sum_congr rfl hterm2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        ← Finset.mul_sum, nsmul_eq_mul]
    have hm : ((s - k : ℕ) : ℤ) = (s : ℤ) - k := Nat.cast_sub hk
    nlinarith [hSS, hm]
  have hRHS : ((s - k : ℕ) : ℤ) = (s : ℤ) - k := Nat.cast_sub hk
  have hRHS2 : ((z - k : ℕ) : ℤ) = (z : ℤ) - k := Nat.cast_sub (le_trans hk hsz)
  have hfin : ((∑ j ∈ Finset.Ico k s, (z + s - 1 - 2 * j) : ℕ) : ℤ) = (((s - k) * (z - k) : ℕ) : ℤ) := by
    rw [hcast]; push_cast [hRHS, hRHS2]; ring
  exact_mod_cast hfin

/-- **The charge as a corner-cell parabola minimum** `waistCharge x s z = gCrux s z x` (for `s ≤ z`). The
sum-of-mins equals the discrete parabola minimum `⨅_{k=0}^{s} [(s−k)(z−k) + k·x]`: (≤) the sum is bounded
by every cell (split `range s` at `k`, `min ≤ x` on the prefix, `min ≤ (z+s−1−2j)` on the suffix, the
tail `= (s−k)(z−k)`); (≥) at the crossing `k₀` (where `x` overtakes the axis exponent) the split is exact,
so some cell equals the sum. -/
theorem waistCharge_eq_gCrux (x s z : ℕ) (hsz : s ≤ z) :
    waistCharge x s z = gCrux s z x := by
  have hmin : min s z = s := Nat.min_eq_left hsz
  have hle : waistCharge x s z ≤ gCrux s z x := by
    unfold gCrux
    refine Finset.le_inf' _ _ (fun k hk => ?_)
    rw [Finset.mem_range] at hk
    have hks : k ≤ s := by omega
    unfold waistCharge
    rw [← Finset.sum_range_add_sum_Ico (fun j => min x (z + s - 1 - 2 * j)) hks]
    have h1 : ∑ j ∈ Finset.range k, min x (z + s - 1 - 2 * j) ≤ k * x :=
      calc ∑ j ∈ Finset.range k, min x (z + s - 1 - 2 * j)
            ≤ ∑ _j ∈ Finset.range k, x := Finset.sum_le_sum (fun j _ => min_le_left _ _)
        _ = k * x := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h2 : ∑ j ∈ Finset.Ico k s, min x (z + s - 1 - 2 * j) ≤ (s - k) * (z - k) :=
      calc ∑ j ∈ Finset.Ico k s, min x (z + s - 1 - 2 * j)
            ≤ ∑ j ∈ Finset.Ico k s, (z + s - 1 - 2 * j) :=
              Finset.sum_le_sum (fun j _ => min_le_right _ _)
        _ = (s - k) * (z - k) := waist_tailSum hsz hks
    calc ∑ j ∈ Finset.range k, min x (z + s - 1 - 2 * j)
            + ∑ j ∈ Finset.Ico k s, min x (z + s - 1 - 2 * j)
          ≤ k * x + (s - k) * (z - k) := Nat.add_le_add h1 h2
      _ = (s - k) * (z - k) + k * x := by ring
  have hge : gCrux s z x ≤ waistCharge x s z := by
    obtain ⟨k₀, hk0s, hi, hii⟩ :
        ∃ k₀, k₀ ≤ s ∧ (∀ j, j < k₀ → x ≤ z + s - 1 - 2 * j)
          ∧ (∀ j, k₀ ≤ j → j < s → z + s - 1 - 2 * j ≤ x) := by
      by_cases hx : x ≤ z + s - 1
      · exact ⟨min s ((z + s - 1 - x) / 2 + 1), Nat.min_le_left _ _,
          fun j hj => by omega, fun j hj hjs => by omega⟩
      · exact ⟨0, Nat.zero_le _, fun j hj => by omega, fun j _ hjs => by omega⟩
    have hsplit : waistCharge x s z = k₀ * x + (s - k₀) * (z - k₀) := by
      unfold waistCharge
      rw [← Finset.sum_range_add_sum_Ico (fun j => min x (z + s - 1 - 2 * j)) hk0s]
      congr 1
      · calc ∑ j ∈ Finset.range k₀, min x (z + s - 1 - 2 * j)
              = ∑ _j ∈ Finset.range k₀, x :=
                Finset.sum_congr rfl (fun j hj => by
                  rw [Finset.mem_range] at hj; exact min_eq_left (hi j hj))
          _ = k₀ * x := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      · calc ∑ j ∈ Finset.Ico k₀ s, min x (z + s - 1 - 2 * j)
              = ∑ j ∈ Finset.Ico k₀ s, (z + s - 1 - 2 * j) :=
                Finset.sum_congr rfl (fun j hj => by
                  rw [Finset.mem_Ico] at hj; exact min_eq_right (hii j hj.1 hj.2))
          _ = (s - k₀) * (z - k₀) := waist_tailSum hsz hk0s
    rw [hsplit]
    have hcell := gCrux_le_cell s z x (s := k₀) (by rw [hmin]; exact hk0s)
    calc gCrux s z x ≤ (s - k₀) * (z - k₀) + k₀ * x := hcell
      _ = k₀ * x + (s - k₀) * (z - k₀) := by ring
  exact le_antisymm hle hge

/-- **The charge identity `waistCharge x s z = minAdm (x,s,z)`** (for `s ≤ z`, the waist domain) — step 4
of the SVD-qPeel waist resolution. The additive per-singular-mode charges reproduce `minAdm` EXACTLY
(0 violations over 936 triples), so the corank-`q` qPeel threshold `½·Σ min(x, hⱼ+1)` equals `½·minAdm` —
TIGHT, no undershoot. Proof: `minAdm ![x,s,z] = minAdm ![s,z,x]` (perm invariance, the 3-cycle `finRotate 3`)
`= minAdmRec ![s,z,x] = gCrux s z x = waistCharge x s z` (`waistCharge_eq_gCrux`). -/
theorem waistCharge_eq_minAdm (x s z : ℕ) (hsz : s ≤ z) :
    waistCharge x s z = minAdm (![x, s, z] : Fin 3 → ℕ) := by
  have h2 : (![s, z, x] : Fin 3 → ℕ) = (![x, s, z] : Fin 3 → ℕ) ∘ finRotate 3 := by
    funext i; fin_cases i <;> rfl
  have h3 : minAdm (![s, z, x] : Fin 3 → ℕ) = minAdm (![x, s, z] : Fin 3 → ℕ) := by
    rw [h2]; exact minAdm_comp_perm (finRotate 3) _
  rw [waistCharge_eq_gCrux x s z hsz, ← h3, ← minAdmRec_eq_minAdm, minAdmRec_three]
  simp

/-- **Non-vacuity anchors** — the charge identity at the certified waist anchors `(3,2,3)`, `(4,2,4)`,
`(4,3,4)` (`minAdm` `5, 7, 10`; `M₁ ≥ 2`, all in hole (c)). Confirms the reindexed `waistCharge` computes
the intended value. -/
example : waistCharge 3 2 3 = 5 := by decide
example : waistCharge 4 2 4 = 7 := by decide
example : waistCharge 4 3 4 = 10 := by decide

end DLNFibre.DLN.RLCT
