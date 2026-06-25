/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.DLN.RlctPayoffGeneral
import DLNFibre.Core.FibreCodimFinal
import DLNFibre.Core.RankLocusClosed

/-!
# `DLNFibre.DLN.BundleShiftDischarge` — discharging the bundle-shift interface from Core

The expedition's CLOSING rung. `DLN.RlctPayoffGeneral` carries the geometric bundle shift
`codim mult⁻¹(B) = codim Σ̄^r + r(d_0+d_N−r)` as an **Assumed** hypothesis (the field
`cited_bundle_shift` of `BundleShiftInterface`). That codimension identity is in fact PROVED,
zero-cite, in `Core.FibreCodimFinal.codimRepCanonical_fibre_eq_cCodim_add_shift`. Here we
**discharge the interface**: build a proved instance `bundleShift_of_core` (a
`BundleShiftInterface d K ι`) whose
field is derived from Core, and rewire the rank-`r` RLCT payoff to drop the `J` hypothesis, so the
payoff `rlct(K^DLN_B) = (cCodim + r(d_0+d_N−r))/2` rests on ONLY the Cited Aoyagi `RlctInterface`.

Three reconciliations:

1. **Indexing.** `BundleShiftInterface`/payoff index by `d : Fin (N + 1) → ℕ` under the `0 < N`
   guard; `Core.FibreCodimFinal` indexes by `d : Fin (M + 2) → ℕ`. Under `0 < N` we
   `obtain ⟨M, rfl⟩ : ∃ M, N = M + 1`, after which `Fin (N + 1) = Fin ((M+1)+1)` is **defeq** to
   `Fin (M + 2)` — no transport cast. `Fin.last N = Fin.last (M+1)` and `d 0` align definitionally;
   the shift differs only by `+`-commutativity inside the `Nat` subtraction.

2. **Base-change ℝ→K.** `cited_bundle_shift` concerns `fibre (B.map ι)` for `B : Matrix … ℝ` of
   rank `r`. Core needs `(B.map ι).rank = r`. The injective field hom `ι : ℝ →+* K` preserves rank
   (`Matrix.rank_map_eq_of_injective`, proved below via the in-repo determinantal-rank bridge
   `Core.rank_le_iff_forall_submatrix_det_eq_zero` + `RingHom.map_det` + injectivity).

3. **Kostant-nonempty.** `(kostantPartitions d r).Nonempty` from `0 < N` + `∀ k, r ≤ d k`, via
   `Core.kostantPartitions_nonempty_of_le`.

**Dependency rule:** `DLN` depends on `Core`; `Core` never imports `DLN`. This module is DLN-layer.
-/

namespace DLNFibre.DLN

open Matrix DLNFibre.Core

variable {N : ℕ}

/-! ## Wrinkle 2 — rank is preserved by an injective ring hom (determinantal-rank bridge) -/

/-- **Matrix rank is preserved by an injective ring hom.** For an injective `ι : R →+* S` between
commutative rings where the determinantal-rank bridge holds on both sides (here: fields), the
entrywise map `B ↦ B.map ι` preserves rank. Proof: `(B.map ι).rank ≤ r ↔ B.rank ≤ r` for every `r`,
because each `(r+1)×(r+1)` minor satisfies `det ((B.map ι).submatrix er ec) = ι (det (B.submatrix
er ec))` (`Matrix.submatrix_map` + `RingHom.map_det`), and `ι` injective gives `ι x = 0 ↔ x = 0`. -/
theorem Matrix.rank_map_eq_of_injective {R S : Type*} [Field R] [Field S]
    {p q : ℕ} (B : Matrix (Fin p) (Fin q) R) (ι : R →+* S) (hι : Function.Injective ι) :
    (B.map ι).rank = B.rank := by
  have hiff : ∀ r : ℕ, (B.map ι).rank ≤ r ↔ B.rank ≤ r := by
    intro r
    rw [Core.rank_le_iff_forall_submatrix_det_eq_zero (B.map ι),
      Core.rank_le_iff_forall_submatrix_det_eq_zero B]
    refine forall₂_congr (fun er ec ↦ ?_)
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact map_eq_zero_iff ι hι
  exact le_antisymm ((hiff _).2 le_rfl) ((hiff _).1 le_rfl)

/-! ## The discharge — a proved `BundleShiftInterface` instance from Core -/

section Discharge

variable (d : Fin (N + 1) → ℕ)
  (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ι : ℝ →+* K)

/-- **The bundle-shift interface, PROVED from Core.** The geometric bundle shift carried as the
`cited_bundle_shift` field is derived from `Core.FibreCodimFinal`'s
`codimRepCanonical_fibre_eq_cCodim_add_shift`
(the zero-cite codim identity) by: writing `N = M + 1` under `0 < N` (so the `Fin (N+1)` index is
defeq `Fin (M+2)`), preserving the target rank across `ι` (`Matrix.rank_map_eq_of_injective`), and
supplying Kostant-nonemptiness (`Core.kostantPartitions_nonempty_of_le`). The geometric half is now
Proved — no `BundleShiftInterface` is left as a hypothesis in any consumer of this instance.
`K : Type` (universe `0`): the Core codim identity is itself `Type 0` (the Schur-side no-drop fixes
the index type at `Type 0`); the RLCT story lands at `ℂ` / `AlgebraicClosure ℚ`, both `Type 0`. -/
noncomputable def bundleShift_of_core : BundleShiftInterface d K ι where
  cited_bundle_shift B r hN hB hr := by
    -- write `N = M + 1` so the `Fin (N+1)` index is defeq `Fin (M+2)`; Core applies directly.
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    -- Kostant-nonemptiness from `0 < N` and `∀ k, r ≤ d k`.
    have hkost : (kostantPartitions d r).Nonempty :=
      kostantPartitions_nonempty_of_le (by omega) hr
    -- the base-changed target has rank `r` (rank preserved by the injective field hom `ι`).
    have hBmap : (B.map ι).rank = r := by
      rw [Matrix.rank_map_eq_of_injective B ι ι.injective, hB]
    -- Core's central identity: `codim (fibre (B.map ι)) = (cCodim d r).toNat + δ`.
    have hCore := codimRepCanonical_fibre_eq_cCodim_add_shift (k := K) d r hkost (B.map ι) hBmap
    -- Brick A rewrites `codim Σ̄^r = (cCodim d r).toNat`.
    rw [hCore, codimRepCanonical_productRankLocusLE_eq_cCodim_enat (k := K) d r hkost]
    -- the shift terms differ only by `+`-commutativity inside the `Nat` subtraction.
    rw [Nat.add_comm (d (Fin.last (M + 1))) (d 0)]

end Discharge

/-! ## R2-general (rewired) — the payoff with only the Cited Aoyagi interface -/

section R2General

variable {d : Fin (N + 1) → ℕ}
  {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {ι : ℝ →+* K}

/-- **The general-`r` RLCT payoff, through ONLY the Cited Aoyagi rlct interface.** The geometric
bundle-shift half is now Proved from `Core` (via `bundleShift_of_core`), so the only carried
dependency is `I : RlctInterface` (the Cited Aoyagi `rlct = ½·codim`). For a genuine deep network
(`0 < N`) and `B` of rank `r ≤ min d`, the rlct of the DLN square-Frobenius loss `K^DLN_B` equals
`(cCodim d r + r(d_0+d_N−r))/2`: the combinatorial `C/2` plus the half-shift. `via_aoyagi` names the
lone Cited source; `[IsAlgClosed K] [CharZero K]` (the scope where `C` is the geometric
codimension). -/
theorem rlct_lossDLN_eq_half_cCodim_add_shift
    (I : RlctInterface d K ι)
    {B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ} {r : ℕ}
    (hN : 0 < N) (hB : B.rank = r) (hr : ∀ k', r ≤ d k') (h : (kostantPartitions d r).Nonempty) :
    I.rlct (lossDLN d B)
      = (((cCodim d r h).toNat : ℝ) + (r * (d 0 + d (Fin.last N) - r) : ℕ)) / 2 :=
  rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi I (bundleShift_of_core d K ι) hN hB hr h

end R2General

/-! ## Non-vacuity witness — `(2,2,2)`, `r = 1`, through the discharged shift -/

section Witness

/-- **`(2,2,2)`, `r = 1`: the RLCT payoff `rlct(K^DLN_B) = 2`**, over `ℂ`, for `B` of rank `1`,
through ONLY the Cited Aoyagi interface `I` — the bundle shift is now Proved from `Core`. The
combinatorial `C = cCodim d222 1 = 1` and the shift `1·(2+2−1) = 3` give `rlct = (1+3)/2 = 2`: the
`(2,2,2)` rank-`1` DLN is mildly singular. `(2,2,2)` has `N = 2 > 0`. -/
theorem rlct_lossDLN_d222_one_eq_two
    (I : RlctInterface Core.d222 ℂ Complex.ofRealHom)
    {B : Matrix (Fin (Core.d222 (Fin.last 2))) (Fin (Core.d222 0)) ℝ} (hB : B.rank = 1) :
    I.rlct (lossDLN Core.d222 B) = 2 := by
  have hr : ∀ k', (1 : ℕ) ≤ Core.d222 k' := Core.d222_one_le
  rw [rlct_lossDLN_eq_half_cCodim_add_shift I (by norm_num) hB hr
    Core.kostantPartitions_d222_one_nonempty, Core.cCodim_d222_one]
  have hshift : (1 : ℕ) * (Core.d222 0 + Core.d222 (Fin.last 2) - 1) = 3 := by decide
  rw [hshift]
  norm_num

end Witness

end DLNFibre.DLN
