import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId3333
import DLNFibre.DLN.RLCT.Validate.RouteMGenLeafIntegrand

/-!
# `RouteMFlatChartProbe3333` — C1 keystone risk-probe on (3,3,3,3) (route-c rate transfer)

The bounded risk-probe for the route-c keystone (`threads/36-genM-jacobian-det/design.md` §3b): build the
flat chart `chartParamsFlat` for (3,3,3,3) via a `Bflat` decoder reading the block data from flat coords,
and confirm the BANKED rate identity `routeMCore_phiGen` TRANSFERS to it for free (the keystone identity
`chartParamsFlat u = chartParamsGen (u p) M t (Bflat u) hle`).

## Finding (the probe's verdict)
The keystone, in its **rate-transfer role**, is de-risked: with `chartParamsFlat` defined as
`chartParamsGen (x 0) M3 t3 (Bflat3333 x) hle3` (the decoder composed with the abstract chain), the keystone
is definitional (`rfl`) and `routeMCore M3 (paramsEquivFlat ∘ chartParamsFlat) = (x 0)²·V` follows from the
banked `routeMCore_phiGen` with the identity-boundary `hC0` discharged via `chainQ_cZero` (the
`genBlk3spec` pattern). So **the rate transfers to the flat chart with NO re-proof** — the C1 keystone's
PAYOFF lands.

The HARD direction (an *independent, det-computable* flat-frame chart proven equal to `chartParamsGen ∘
Bflat`) is `chainA_213_entry`-style entry extraction: `chainA`'s `finSplit` reindex resolves to explicit
matrix entries via the banked `finSplit_refl` / `finSumFinEquiv_symm_apply_{castAdd,natAdd}` (as
`chainQ_cZero` demonstrated), so it is MECHANICAL (bookkeeping), not a cast wall — but per-entry and not
free. `chainA_213_entry` here banks one boundary's entry law as the template.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

open Matrix

/-! ## The `Bflat` decoder for (3,3,3,3) (block data from flat coords) -/

/-- A clean modular flat index `Fin 27`. -/
def flatIdx27 (n : ℕ) : Fin 27 := ⟨n % 27, Nat.mod_lt _ (by norm_num)⟩

/-- **The `Bflat` decoder** for (3,3,3,3): reads the `GenBlk M3spec t3spec` block data from the flat
coordinates `x : Fin 27 → ℝ`, with the IDENTITY boundary at `k = 0` (`Bmat 0 = 1`, `Rmat 0 = 0`,
the empty residual `Nblk 0`) so the suffix bridge's `C 0 = 1` is reachable (`chainQ_cZero`). The other
boundaries read free coordinates. The decoder shape the route-c keystone consumes. -/
noncomputable def Bflat3333 (x : Fin 27 → ℝ) : GenBlk M3spec t3spec where
  Bmat := fun k => match k with
    | 0 => (1 : Matrix (Fin 3) (Fin 3) ℝ)
    | (k + 1) => Matrix.of (fun i j => x (flatIdx27 (i.val * 7 + j.val + (k + 1) * 3)))
  Nblk := fun k => Matrix.of (fun i j => x (flatIdx27 (i.val + j.val + k * 5 + 1)))
  Wblk := fun k => Matrix.of (fun i j => x (flatIdx27 (i.val + j.val + k * 5 + 2)))
  Rmat := fun k => match k with
    | 0 => (0 : Matrix (Fin 3) (Fin 3) ℝ)
    | (k + 1) => Matrix.of (fun i j => x (flatIdx27 (i.val + j.val + (k + 1) * 5 + 3)))
  Rfin := fun k => Matrix.of (fun i j => x (flatIdx27 (i.val + j.val + k * 5 + 4)))

/-- The flat chart parameter for (3,3,3,3): the decoder composed with the abstract chain — so the
keystone identity is definitional (`rfl`) and the rate transfers for free. -/
noncomputable def chartParamsFlat3333 (x : Fin 27 → ℝ) : Params M3spec :=
  chartParamsGen (x 0) M3spec t3spec (Bflat3333 x) hle3spec

/-- **The keystone identity** (definitional): `chartParamsFlat = chartParamsGen (x 0) M t (Bflat x) hle`. -/
theorem chartParamsFlat3333_eq (x : Fin 27 → ℝ) :
    chartParamsFlat3333 x = chartParamsGen (x 0) M3spec t3spec (Bflat3333 x) hle3spec := rfl

/-! ## `C 0 = 1` for the `Bflat` decoder (the identity boundary, via `chainQ_cZero`) -/

/-- **`C 0 = 1`** for the flat decoder (identity boundary). `Bmat 0 = 1`, `chainQ(N_0) = I` at `c_0 = 0`
(`chainQ_cZero`), `Rmat 0 = 0` ⟹ `C 0 = 1·I + (x 0)•0 = 1`. -/
theorem Bflat3333_C0_eq_one (x : Fin 27 → ℝ) :
    (chainOfMt (x 0) M3spec t3spec (Bflat3333 x) hle3spec).toChain.C 0
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [chainOfMt_C_zero (x 0) M3spec t3spec _ hle3spec (by norm_num)]
  have hQ : chainQ (genWidthEq M3spec t3spec hle3spec 0 (by norm_num)) ((Bflat3333 x).Nblk 0)
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) := chainQ_cZero _ _
  have hB : (Bflat3333 x).Bmat 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := rfl
  have hR : (Bflat3333 x).Rmat 0 = (0 : Matrix (Fin 3) (Fin 3) ℝ) := rfl
  rw [hQ, hB, hR]
  show (1 : Matrix (Fin 3) (Fin 3) ℝ) * (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + (x 0) • (0 : Matrix (Fin 3) (Fin 3) ℝ) = (1 : Matrix (Fin 3) (Fin 3) ℝ)
  rw [Matrix.one_mul, smul_zero, add_zero]

/-! ## The RATE TRANSFER (the keystone's payoff — the rate lands on the flat chart for free) -/

/-- **The rate transfers to the flat chart** (the C1 keystone payoff). `routeMCore M3 (paramsEquivFlat ∘
chartParamsFlat) = (x 0)²·V`, from the BANKED `routeMCore_phiGen` (the keystone identity being `rfl`),
with `hC0` discharged via `Bflat3333_C0_eq_one`. NO re-proof of the telescope/cast rate work. -/
theorem routeMCore_chartParamsFlat3333 (x : Fin 27 → ℝ) :
    routeMCore M3spec (paramsEquivFlat M3spec (chartParamsFlat3333 x))
      = (x 0) ^ 2 * VvalGen (x 0) M3spec t3spec (Bflat3333 x) hle3spec := by
  rw [chartParamsFlat3333]
  -- `paramsEquivFlat ∘ chartParamsGen = phiGen` definitionally; apply the banked rate identity.
  have hC0 : (chainOfMt (x 0) M3spec t3spec (Bflat3333 x) hle3spec).toChain.C 0
        * (chainOfMt (x 0) M3spec t3spec (Bflat3333 x) hle3spec).toChain.suffix 0 (Nat.zero_le 3)
      = (chainOfMt (x 0) M3spec t3spec (Bflat3333 x) hle3spec).toChain.suffix 0 (Nat.zero_le 3) := by
    rw [Bflat3333_C0_eq_one x]; exact Matrix.one_mul _
  exact routeMCore_phiGen (x 0) M3spec t3spec (Bflat3333 x) hle3spec hC0

/-! ## The hard direction: `chainA` resolves to explicit entries (MECHANICAL, the bookkeeping)

A genuinely-independent det-computable flat-frame chart would have explicit `!![…]` layers; proving it
equals `chartParamsGen ∘ Bflat` reduces (per layer) to `chainA = explicit`. This is the entry-extraction
below — the `finSplit` reindex resolves to explicit matrix rows via the banked
`finSumFinEquiv_symm_apply_{castAdd,natAdd}` (as `chainQ_cZero` already does). It is MECHANICAL (per-entry
bookkeeping), NOT a cast wall. Banked here for the `t=2,c=1` boundary as the template. -/

set_option maxHeartbeats 800000 in
/-- **`chainA` entry law** (the `t=2,c=1,M'=3,m'=3` boundary): `chainA … i j = (C−N·W) ⟨i,_⟩ j` for
`i < 2` (the kept rows), `= W ⟨i−2,_⟩ j` for `i ≥ 2` (the lift row). The `finSplit` reindex resolves to
the explicit row partition — the per-entry bookkeeping a full `chainA = !![…]` flat-layer equality runs
(MECHANICAL via the banked `finSumFinEquiv_symm_apply_*`; NOT a cast wall). -/
theorem chainA_213_entry (N : Matrix (Fin 2) (Fin 1) ℝ) (W : Matrix (Fin 1) (Fin 3) ℝ)
    (C : Matrix (Fin 2) (Fin 3) ℝ) (j : Fin 3) :
    chainA (show (2 : ℕ) + 1 = 3 by rfl) N W C 0 j = (C - N * W) 0 j
      ∧ chainA (show (2 : ℕ) + 1 = 3 by rfl) N W C 1 j = (C - N * W) 1 j
      ∧ chainA (show (2 : ℕ) + 1 = 3 by rfl) N W C 2 j = W 0 j := by
  have hrow : ∀ a : Fin 2, finSplit (show (2:ℕ) ≤ 3 by norm_num) (a.castAdd 1 : Fin 3) = Sum.inl a := by
    intro a
    simp only [finSplit, Equiv.trans_apply, finCongr_apply]
    rw [show (Fin.cast (show (3:ℕ) = 2 + (3 - 2) by norm_num) (a.castAdd 1 : Fin 3))
          = Fin.castAdd (3 - 2) a from by apply Fin.ext; simp]
    exact finSumFinEquiv_symm_apply_castAdd a
  have hlift : finSplit (show (2:ℕ) ≤ 3 by norm_num) (2 : Fin 3) = Sum.inr (0 : Fin (3 - 2)) := by
    simp only [finSplit, Equiv.trans_apply, finCongr_apply]
    rw [show (Fin.cast (show (3:ℕ) = 2 + (3 - 2) by norm_num) (2 : Fin 3))
          = Fin.natAdd 2 (0 : Fin (3 - 2)) from by apply Fin.ext; simp]
    exact finSumFinEquiv_symm_apply_natAdd 0
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [chainA, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_symm,
      Equiv.refl_apply, Equiv.symm_symm]
  · rw [show (0 : Fin 3) = ((0 : Fin 2).castAdd 1 : Fin 3) from by apply Fin.ext; simp, hrow 0,
      Sum.elim_inl]
  · rw [show (1 : Fin 3) = ((1 : Fin 2).castAdd 1 : Fin 3) from by apply Fin.ext; simp, hrow 1,
      Sum.elim_inl]
  · rw [hlift, Sum.elim_inr, Matrix.submatrix_apply]
    congr 1

end DLNFibre.DLN.RLCT
