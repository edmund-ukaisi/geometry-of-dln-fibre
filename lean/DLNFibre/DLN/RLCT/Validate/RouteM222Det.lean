import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatStruct

/-!
# `RouteM222Det` — the `(2,2,2)` ROUTE-2a validate-small (the genuine multi-boundary node)

The first end-to-end Route-2a achiever chart through the GENERAL `chainOfMt`/`GenBlk` engine, on the
smallest genuinely MULTI-BOUNDARY node `M = (2,2,2)` (`minAdm = 3`, two rank-drops: the Schur boundary
`k = 1` and the leaf). Per `certificate-rate-det-route.md` (ROUTE 2a, build-ready):

* the chart is `φ_det x := phiGen (x p) M t (B_det222 x) hle` — ONE chart, both legs;
* the RATE is the BANKED decoder-agnostic `routeMCore_phiGen` instantiated at the FULL-RANK decoder
  `B_det222` (one-line; re-check only `hC0`); NO bridge, NO new telescope — the banked backward
  `chain_telescope` already does `prod = u·H` for any chain, here with two drops telescoping to ONE `u`;
* the FULL-RANK fix (defeating UPDATE-11's D1 dead-slot bug): `Rfin 2 ≠ 0` (the leaf residual is LIVE),
  with the pivot residual entry the FIXED `1` scaled by `u = x p` to the pivot output.

## The widths + the decoder (`Text = [2,2,1]`, `Wext = [2,2,2]`, `N = 8`)

`t222 = (2,1,0)` (`t 0 = M 0 = 2` the identity-boundary convention; `t 1 = 1`, `t 2 = 0` the descent).
`Text 0 = Text 1 = 2` (identity boundary `k = 0`), `Text 2 = 1` (the Schur drop `2 → 1` at `k = 1`),
leaf rank `1` (`C 2 = u·Rfin 2`, `1×2`). minAdm `= 3 = 1` (the `k=1` E-block `1×1`) `+ 2` (the leaf
`Rfin` `1×2`). The radial scalar is `u = x 0`; the 7 other coords feed the blocks.

Verified EXACT (sympy): `prod = u·H` (all 4 entries divisible by exactly `u`), so `F = u²·‖H‖²`; the
8×8 flat Jacobian det `= −x 4 · (x 0)²` (full-rank off `{x 0 = 0}`; `|det| = |x 4|·|x 0|²` = a
spectator `|x 4|` times `|x 0|^{minAdm−1}`).

Axiom-clean target `[propext, Classical.choice, Quot.sound]` (rate leg via the banked engine; no S2).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-- `M222 = (2,2,2)` (the smallest genuinely multi-boundary achiever node). -/
abbrev M222 : Fin 3 → ℕ := ![2, 2, 2]

/-- The descent path `t222 = (2,1,0)`: `t 0 = M 0 = 2` (the identity-boundary convention, `Text 1 =
Text 0`), `t 1 = 1` (the Schur drop `2 → 1`), `t 2 = 0`. -/
abbrev t222 : Fin 3 → ℕ := ![2, 1, 0]

theorem minAdm_M222 : minAdm M222 = 3 := by rw [← minAdmRec_eq_minAdm]; decide

theorem routeMAmbient_M222 : routeMAmbient M222 = 8 := by decide

/-! ## The widths (all `rfl` at the concrete node) -/

theorem Text222_0 : Text M222 t222 0 = 2 := rfl
theorem Text222_1 : Text M222 t222 1 = 2 := rfl
theorem Text222_2 : Text M222 t222 2 = 1 := rfl
theorem Wext222_0 : Wext M222 0 = 2 := rfl
theorem Wext222_1 : Wext M222 1 = 2 := rfl
theorem Wext222_2 : Wext M222 2 = 2 := rfl

/-- The chain admissibility `hle : Text(k+1) ≤ Wext k` for `(2,2,2)` (all `k < 2`: `Text 1 = 2 ≤ 2`,
`Text 2 = 1 ≤ 2`). -/
theorem hle222 : ∀ k, k < 2 → Text M222 t222 (k + 1) ≤ Wext M222 k := by
  intro k hk
  interval_cases k <;> decide

/-! ## The full-rank decoder `B_det222 : GenBlk M222 t222`

The five block fields, at the concrete `(2,2,2)` widths. The leaf `Rfin 2 = !![1, x 7]` is NONZERO
(the D1 fix; entry `(0,0) = 1` the fixed pivot residual, `(0,1) = x 7` the active leaf direction). The
other coords: `x 1 = n` (the `Nblk 1` chaining residual), `x 2, x 3 = w0, w1` (the `Wblk 1` lift),
`x 4, x 5 = b0, b1` (the `Bmat 1` kept column), `x 6 = e` (the `Rmat 1` E-block). The radial `u = x 0`
is supplied separately to `phiGen`. -/

/-- The full-rank `(2,2,2)` decoder. Identity boundary `k = 0` (`Bmat 0 = 1`, `Rmat 0 = 0`, `Nblk 0`
empty); the Schur drop at `k = 1`; the LIVE leaf `Rfin 2 = !![1, x 7]` (the D1 fix). -/
noncomputable def B_det222 (x : Fin 8 → ℝ) : GenBlk M222 t222 where
  Bmat := fun k => match k with
    | 0 => Matrix.reindex (Equiv.refl _)
        (finCongr (show Text M222 t222 0 = Text M222 t222 1 from rfl))
        (1 : Matrix (Fin (Text M222 t222 0)) (Fin (Text M222 t222 0)) ℝ)
    | 1 => (!![x 4; x 5] : Matrix (Fin 2) (Fin 1) ℝ)
    | (_ + 2) => 0
  Nblk := fun k => match k with
    | 1 => (!![x 1] : Matrix (Fin 1) (Fin 1) ℝ)
    | _ => 0
  Wblk := fun k => match k with
    | 1 => (!![x 2, x 3] : Matrix (Fin 1) (Fin 2) ℝ)
    | _ => 0
  Rmat := fun k => match k with
    | 1 => (!![0, 0; 0, x 6] : Matrix (Fin 2) (Fin 2) ℝ)
    | _ => 0
  Rfin := fun k => match k with
    | 2 => (!![1, x 7] : Matrix (Fin 1) (Fin 2) ℝ)
    | _ => 0

/-! ## The rate leg (one-line via the banked decoder-agnostic `routeMCore_phiGen`)

The chart `φ_det222 x := phiGen (x 0) M222 t222 (B_det222 x) hle222` (radial `u = x 0`). The RATE
`routeMCore M222 (φ_det222 x) = (x 0)² · V` is the BANKED `routeMCore_phiGen` instantiated at
`B_det222 x`, re-checking only the identity boundary `hC0` (`C 0 = 1`). -/

/-- **The identity boundary `C 0 = 1`** for `B_det222` (the `C0_eq_one` pattern): `C 0 = Bmat 0 ·
chainQ(N_0) + u·Rmat 0 = (reindex 1)·I + u·0 = 1`. `Bmat 0 = reindex 1`, `Rmat 0 = 0`,
`chainQ(N_0) = I` at `c_0 = Wext 0 − Text 1 = 0`. -/
theorem C0_eq_one_222 (u : ℝ) :
    (chainOfMt u M222 t222 (B_det222 (fun _ => u)) hle222).toChain.C 0
      = (1 : Matrix (Fin (Text M222 t222 0)) (Fin (Text M222 t222 0)) ℝ) := by
  rw [chainOfMt_C_zero u M222 t222 _ hle222 (by norm_num),
    show (B_det222 (fun _ => u)).Rmat 0 = 0 from rfl, smul_zero, add_zero]
  have hBmat : (B_det222 (fun _ => u)).Bmat 0
      = Matrix.reindex (Equiv.refl _)
          (finCongr (show Text M222 t222 0 = Text M222 t222 1 from rfl))
          (1 : Matrix (Fin (Text M222 t222 0)) (Fin (Text M222 t222 0)) ℝ) := rfl
  rw [hBmat]
  ext i j
  rw [Matrix.mul_apply,
    Finset.sum_eq_single (Fin.cast (show Text M222 t222 0 = Text M222 t222 1 from rfl) i)]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Matrix.one_apply_eq, one_mul]
    have hjcol : (j : Fin (Wext M222 0)) = Fin.cast (genWidthEq M222 t222 hle222 0 (by norm_num))
        (Fin.castAdd (Wext M222 0 - Text M222 t222 (0 + 1))
          (Fin.cast (show Text M222 t222 1 = Wext M222 0 from rfl).symm j)) := by
      apply Fin.ext; simp
    rw [hjcol, chainQ_apply_castAdd, Matrix.one_apply, Matrix.one_apply]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos (by apply Fin.ext; simpa using h), if_pos (by apply Fin.ext; simpa using h)]
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),
        if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc))]
  · intro b _ hb
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply]
    rw [show (1 : Matrix (Fin (Text M222 t222 0)) (Fin (Text M222 t222 0)) ℝ) i
          (Fin.cast (show Text M222 t222 0 = Text M222 t222 1 from rfl).symm b) = 0 from by
      rw [Matrix.one_apply, if_neg]; intro hc; apply hb; rw [hc]; apply Fin.ext; simp]
    rw [zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **`hC0` for `B_det222`** (`C 0 · suffix 0 = suffix 0` from `C 0 = 1`). -/
theorem hC0_222 (u : ℝ) :
    (chainOfMt u M222 t222 (B_det222 (fun _ => u)) hle222).toChain.C 0
        * (chainOfMt u M222 t222 (B_det222 (fun _ => u)) hle222).toChain.suffix 0 (Nat.zero_le 2)
      = (chainOfMt u M222 t222 (B_det222 (fun _ => u)) hle222).toChain.suffix 0 (Nat.zero_le 2) := by
  rw [C0_eq_one_222 u]; exact Matrix.one_mul _

/-- **The `(2,2,2)` structured flat chart** `phiDet222 u := phiGen u M222 t222 (B_det222 (fun _ => u))
hle222`. (As in `phiFlatStruct`, the decoder is fed the constant `u`-vector; the genuine `x`-dependence
of `B_det222` is exercised by the det leg's coordinate map.) -/
noncomputable def phiDet222 (u : ℝ) : Fin (routeMAmbient M222) → ℝ :=
  phiGen u M222 t222 (B_det222 (fun _ => u)) hle222

/-- **The RATE leg (one-line, banked).** `routeMCore M222 (phiDet222 u) = u²·V` via the banked
decoder-agnostic `routeMCore_phiGen` at the full-rank `B_det222`, re-checking only `hC0_222`. NO
bridge, NO new telescope — the validated Route-2a rate on the genuine multi-boundary node. -/
theorem routeMCore_phiDet222 (u : ℝ) :
    routeMCore M222 (phiDet222 u)
      = u ^ 2 * VvalGen u M222 t222 (B_det222 (fun _ => u)) hle222 :=
  routeMCore_phiGen u M222 t222 (B_det222 (fun _ => u)) hle222 (hC0_222 u)

end DLNFibre.DLN.RLCT
