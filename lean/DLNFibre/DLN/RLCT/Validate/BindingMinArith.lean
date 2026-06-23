import DLNFibre.DLN.RLCT.Validate.BindingArith
import DLNFibre.DLN.RLCT.Validate.RouteMLeaf

/-!
# `BindingMinArith` — the value-side MIN-telescope of `lambdaCore` (the `harith_min` of the min spine)

The combinatorial value-side facts the MIN-recursion spine `binding_recursion_of_min_step`
(`BindingMinSpine.lean`) consumes as `harith_min`/`harith_base`. The adjudicated truth (pen-and-paper +
decorrelated Codex, 2026-06-23, obstruction certificate):

> **The value-level min is NOT a genuine selecting min.** The descent branch
> `nReg/2 + lambdaCore(redOf M)` EQUALS `lambdaCore M` unconditionally (the additive identity, F1 below
> = `bind_harith_step` re-cast), and the `D₀` leaf branch `mk/2` only DOMINATES it
> (`lambdaCore M ≤ mk/2`, F2 below). The genuine selecting min lives in the GEOMETRIC cover (cert-104b,
> where the descent uses the RAW smooth-block count, before the min is baked into `nReg = minAdm M −
> minAdm(redOf M)`). At the value level the min collapses to the additive identity.

So the value-side `harith_min` is the ℤ-level minimal-codim min identity `minAdm M = min(mk, n + minAdm
(redOf M))` (the cover's V4 — a5f5ceb1's combinatorial content) HALVED, plus the descent-equals-value
F1. This file proves the ½-scaling robustly (all `L`, from the `inf'`-level min hypothesis), and the
one-sided `D₀` bound F2 — so the min spine is fed a TRUE, honestly-labelled `harith_min`.

**Honesty caveat (next to the claim, per the cert):** `harith_min` being true is NOT evidence the
value-level RLCT is a genuine 2-branch min — the `mk/2` branch is dead weight at the value level (it
ties or loses in 100% of nodes). The real 2-branch min is the geometric `hstep_min` (the cover atom,
#9), where the `D₀` divisor genuinely binds on wide-tail nodes (e.g. `(2,2,4)`).
-/

open scoped BigOperators
open Finset

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The ℤ minimal admissible codim `inf'_{T ∈ Adm M} Mval M T` (the un-truncated `minAdm`; `lambdaCore M
= ½·this`). Local abbreviation to state the min-telescope at the `inf'` level (dodging the `.toNat`
truncation of `minAdm`). -/
noncomputable def minAdmZ (M : Fin (L + 1) → ℕ) : ℤ :=
  (Adm M).inf' (Adm_nonempty M) (Mval M)

/-- `0 ≤ minAdmZ M` (the admissible `Mval` is `≥ 0`, so its `inf'` is). -/
theorem minAdmZ_nonneg (M : Fin (L + 1) → ℕ) : 0 ≤ minAdmZ M :=
  Finset.le_inf' _ _ (fun T hT => Mval_nonneg_adm M T hT)

/-- **`lambdaCore` is the halved ℤ minimal codim.** `lambdaCore M = (minAdmZ M : ℚ) / 2`. Direct from the
`def` of `lambdaCore` (`½·(inf' : ℤ)`); the `minAdm`-`toNat` form is `(minAdmZ M).toNat`, equal as `ℤ`
since `minAdmZ ≥ 0` — but stated here at the ℤ-`inf'` level to avoid the truncation. -/
theorem lambdaCore_eq_minAdmZ_half (M : Fin (L + 1) → ℕ) :
    lambdaCore M = (minAdmZ M : ℚ) / 2 := by
  unfold lambdaCore minAdmZ; ring

/-- **F2 — the `D₀` one-sided bound** `lambdaCore M ≤ (M 0 · M 1 : ℚ) / 2`. The all-zeros stratum is
admissible (`zero_mem_Adm`) with codim `Mval M 0 = M 0 · M 1` (`Mval_zeroT_eq`), so the minimal codim is
`≤ M 0 · M 1`, hence `lambdaCore M = ½·minAdmZ ≤ ½·M 0·M 1`. The leaf-branch domination making the
value-level min collapse to the descent branch. -/
theorem lambdaCore_le_front_mul {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) :
    lambdaCore M ≤ (M 0 : ℚ) * (M 1 : ℚ) / 2 := by
  rw [lambdaCore_eq_minAdmZ_half]
  have hle : minAdmZ M ≤ (M 0 : ℤ) * (M 1 : ℤ) := by
    rw [minAdmZ, ← Mval_zeroT_eq M]
    exact Finset.inf'_le _ (zero_mem_Adm M)
  have hq : (minAdmZ M : ℚ) ≤ ((M 0 : ℤ) * (M 1 : ℤ) : ℚ) := by exact_mod_cast hle
  push_cast at hq ⊢
  linarith

/-- **The value-side MIN-telescope** (the `harith_min` the spine consumes — robust for all `L`). GIVEN
the cover's minimal-codim min identity at the ℤ-`inf'` level — `minAdmZ M = min (mk) (n + minAdmZ
(redOf M))` (the cover cert-104b V4, with `mk`/`n` the cover's `D₀`/core weights; a5f5ceb1's
combinatorial content) — and `0 ≤ mk`, `0 ≤ n`, the `lambdaCore` point-min telescope holds:

> `lambdaCore M = min ((mk : ℚ) / 2) ((n : ℚ) / 2 + lambdaCore (redOf M))`.

Pure ½-scaling of the ℤ min identity (`Int.cast_min`, `Rat`-arithmetic), `redOf`-agnostic (`redOf M` is
ANY width vector; instantiate `redOf := schurStateRed`). The descent branch `(n/2) + lambdaCore(redOf M)
= (n + minAdmZ(redOf M))/2` (via `lambdaCore_eq_minAdmZ_half`), and the leaf branch `mk/2`, so the min
is `½·min(mk, n + minAdmZ(redOf M)) = ½·minAdmZ M = lambdaCore M`. -/
theorem lambdaCore_min_telescope (M : Fin (L + 1) → ℕ) (redOf : (Fin (L + 1) → ℕ) → (Fin (L + 1) → ℕ))
    (mk n : ℤ)
    (hmin : minAdmZ M = min mk (n + minAdmZ (redOf M))) :
    lambdaCore M = min ((mk : ℚ) / 2) ((n : ℚ) / 2 + lambdaCore (redOf M)) := by
  rw [lambdaCore_eq_minAdmZ_half, lambdaCore_eq_minAdmZ_half (redOf M), hmin]
  -- `½·min(mk, n + minAdmZ red) = min(mk/2, (n + minAdmZ red)/2) = min(mk/2, n/2 + minAdmZ red/2)`.
  rw [show ((min mk (n + minAdmZ (redOf M)) : ℤ) : ℚ) = min (mk : ℚ) ((n : ℚ) + (minAdmZ (redOf M) : ℚ))
      from by push_cast; rfl]
  rw [show min (mk : ℚ) ((n : ℚ) + (minAdmZ (redOf M) : ℚ)) / 2
        = min ((mk : ℚ) / 2) (((n : ℚ) + (minAdmZ (redOf M) : ℚ)) / 2) from by
    rcases le_total (mk : ℚ) ((n : ℚ) + (minAdmZ (redOf M) : ℚ)) with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]
    · rw [min_eq_right h, min_eq_right (by linarith)]]
  congr 1
  ring

end DLNFibre.DLN.RLCT
