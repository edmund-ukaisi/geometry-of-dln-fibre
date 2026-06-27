import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatStruct
import DLNFibre.DLN.RLCT.Validate.RouteM222StructAdm
import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet
import Mathlib.Algebra.MvPolynomial.Basic

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

`tach222 = (2,1,0)` (`t 0 = M 0 = 2` the identity-boundary convention; `t 1 = 1`, `t 2 = 0` the descent).
`Text 0 = Text 1 = 2` (identity boundary `k = 0`), `Text 2 = 1` (the Schur drop `2 → 1` at `k = 1`),
leaf rank `1` (`C 2 = u·Rfin 2`, `1×2`). minAdm `= 3 = 1` (the `k=1` E-block `1×1`) `+ 2` (the leaf
`Rfin` `1×2`). The radial scalar is `u = x 0`; the 7 other coords feed the blocks.

Verified EXACT (sympy): `prod = u·H` (all 4 entries divisible by exactly `u`), so `F = u²·‖H‖²`; the
8×8 flat Jacobian det `= −x 4 · (x 0)²` (full-rank off `{x 0 = 0}`; `|det| = |x 4|·|x 0|²` = a
spectator `|x 4|` times `|x 0|^{minAdm−1}`).

Axiom-clean target `[propext, Classical.choice, Quot.sound]` (rate leg via the banked engine; no S2).
-/

open Matrix MeasureTheory
open scoped BigOperators ENNReal

namespace DLNFibre.DLN.RLCT

/-- The ACHIEVER descent path for `(2,2,2)`: `tach222 = (2,1,0)` (`t 0 = M 0 = 2` the identity-boundary
convention, `Text 1 = Text 0`; `t 1 = 1` the Schur drop `2 → 1`; `t 2 = 0`). DISTINCT from the
rate-only `RouteM222StructAdm.t222 = (2,1,1)` (which has chain-codim 1 ≠ minAdm 3 — the decoder-fix cert
§4a); this is the genuine achiever path (`Text = [2,2,1]`, chain-codim `= minAdm = 3`). Reuses the
shared `M222 = ![2,2,2]` from `RouteM222StructAdm`. -/
abbrev tach222 : Fin 3 → ℕ := ![2, 1, 0]

theorem minAdm_M222 : minAdm M222 = 3 := by rw [← minAdmRec_eq_minAdm]; decide

/-! ## The widths (all `rfl` at the concrete node) -/

theorem Text222_0 : Text M222 tach222 0 = 2 := rfl
theorem Text222_1 : Text M222 tach222 1 = 2 := rfl
theorem Text222_2 : Text M222 tach222 2 = 1 := rfl
theorem Wext222_0 : Wext M222 0 = 2 := rfl
theorem Wext222_1 : Wext M222 1 = 2 := rfl
theorem Wext222_2 : Wext M222 2 = 2 := rfl

/-- The chain admissibility `hle : Text(k+1) ≤ Wext k` for `(2,2,2)` (all `k < 2`: `Text 1 = 2 ≤ 2`,
`Text 2 = 1 ≤ 2`). -/
theorem hleach222 : ∀ k, k < 2 → Text M222 tach222 (k + 1) ≤ Wext M222 k := by
  intro k hk
  interval_cases k <;> decide

/-! ## The full-rank decoder `B_det222 : GenBlk M222 tach222`

The five block fields, at the concrete `(2,2,2)` widths. The leaf `Rfin 2 = !![1, x 7]` is NONZERO
(the D1 fix; entry `(0,0) = 1` the fixed pivot residual, `(0,1) = x 7` the active leaf direction). The
other coords: `x 1 = n` (the `Nblk 1` chaining residual), `x 2, x 3 = w0, w1` (the `Wblk 1` lift),
`x 4, x 5 = b0, b1` (the `Bmat 1` kept column), `x 6 = e` (the `Rmat 1` E-block). The radial `u = x 0`
is supplied separately to `phiGen`. -/

/-- The full-rank `(2,2,2)` decoder. Identity boundary `k = 0` (`Bmat 0 = 1`, `Rmat 0 = 0`, `Nblk 0`
empty); the Schur drop at `k = 1`; the LIVE leaf `Rfin 2 = !![1, x 7]` (the D1 fix). -/
noncomputable def B_det222 (x : Fin 8 → ℝ) : GenBlk M222 tach222 where
  Bmat := fun k => match k with
    | 0 => Matrix.reindex (Equiv.refl _)
        (finCongr (show Text M222 tach222 0 = Text M222 tach222 1 from rfl))
        (1 : Matrix (Fin (Text M222 tach222 0)) (Fin (Text M222 tach222 0)) ℝ)
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

The chart `φ_det222 x := phiGen (x 0) M222 tach222 (B_det222 x) hleach222` (radial `u = x 0`). The RATE
`routeMCore M222 (φ_det222 x) = (x 0)² · V` is the BANKED `routeMCore_phiGen` instantiated at
`B_det222 x`, re-checking only the identity boundary `hC0` (`C 0 = 1`). -/

/-- **The identity boundary `C 0 = 1`** for `B_det222` (the `C0_eq_one` pattern): `C 0 = Bmat 0 ·
chainQ(N_0) + u·Rmat 0 = (reindex 1)·I + u·0 = 1`. `Bmat 0 = reindex 1`, `Rmat 0 = 0`,
`chainQ(N_0) = I` at `c_0 = Wext 0 − Text 1 = 0`. -/
theorem C0_eq_one_222 (u : ℝ) :
    (chainOfMt u M222 tach222 (B_det222 (fun _ => u)) hleach222).toChain.C 0
      = (1 : Matrix (Fin (Text M222 tach222 0)) (Fin (Text M222 tach222 0)) ℝ) := by
  rw [chainOfMt_C_zero u M222 tach222 _ hleach222 (by norm_num),
    show (B_det222 (fun _ => u)).Rmat 0 = 0 from rfl, smul_zero, add_zero]
  have hBmat : (B_det222 (fun _ => u)).Bmat 0
      = Matrix.reindex (Equiv.refl _)
          (finCongr (show Text M222 tach222 0 = Text M222 tach222 1 from rfl))
          (1 : Matrix (Fin (Text M222 tach222 0)) (Fin (Text M222 tach222 0)) ℝ) := rfl
  rw [hBmat]
  ext i j
  rw [Matrix.mul_apply,
    Finset.sum_eq_single (Fin.cast (show Text M222 tach222 0 = Text M222 tach222 1 from rfl) i)]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Matrix.one_apply_eq, one_mul]
    have hjcol : (j : Fin (Wext M222 0)) = Fin.cast (genWidthEq M222 tach222 hleach222 0 (by norm_num))
        (Fin.castAdd (Wext M222 0 - Text M222 tach222 (0 + 1))
          (Fin.cast (show Text M222 tach222 1 = Wext M222 0 from rfl).symm j)) := by
      apply Fin.ext; simp
    rw [hjcol, chainQ_apply_castAdd, Matrix.one_apply, Matrix.one_apply]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos (by apply Fin.ext; simpa using h), if_pos (by apply Fin.ext; simpa using h)]
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),
        if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc))]
  · intro b _ hb
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply]
    rw [show (1 : Matrix (Fin (Text M222 tach222 0)) (Fin (Text M222 tach222 0)) ℝ) i
          (Fin.cast (show Text M222 tach222 0 = Text M222 tach222 1 from rfl).symm b) = 0 from by
      rw [Matrix.one_apply, if_neg]; intro hc; apply hb; rw [hc]; apply Fin.ext; simp]
    rw [zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **`hC0` for `B_det222`** (`C 0 · suffix 0 = suffix 0` from `C 0 = 1`). -/
theorem hC0_222 (u : ℝ) :
    (chainOfMt u M222 tach222 (B_det222 (fun _ => u)) hleach222).toChain.C 0
        * (chainOfMt u M222 tach222 (B_det222 (fun _ => u)) hleach222).toChain.suffix 0 (Nat.zero_le 2)
      = (chainOfMt u M222 tach222 (B_det222 (fun _ => u)) hleach222).toChain.suffix 0 (Nat.zero_le 2) := by
  rw [C0_eq_one_222 u]; exact Matrix.one_mul _

/-- **The `(2,2,2)` structured flat chart** `phiDet222 u := phiGen u M222 tach222 (B_det222 (fun _ => u))
hleach222`. (As in `phiFlatStruct`, the decoder is fed the constant `u`-vector; the genuine `x`-dependence
of `B_det222` is exercised by the det leg's coordinate map.) -/
noncomputable def phiDet222 (u : ℝ) : Fin (routeMAmbient M222) → ℝ :=
  phiGen u M222 tach222 (B_det222 (fun _ => u)) hleach222

/-- **The RATE leg (one-line, banked).** `routeMCore M222 (phiDet222 u) = u²·V` via the banked
decoder-agnostic `routeMCore_phiGen` at the full-rank `B_det222`, re-checking only `hC0_222`. NO
bridge, NO new telescope — the validated Route-2a rate on the genuine multi-boundary node. -/
theorem routeMCore_phiDet222 (u : ℝ) :
    routeMCore M222 (phiDet222 u)
      = u ^ 2 * VvalGen u M222 tach222 (B_det222 (fun _ => u)) hleach222 :=
  routeMCore_phiGen u M222 tach222 (B_det222 (fun _ => u)) hleach222 (hC0_222 u)

/-! ## The DET leg — the explicit layer matrices + the bridge `chartParamsGen = chartParams222`

The det leg needs the genuine `x`-dependence of `B_det222` (the rate leg fed the constant `u`-vector;
here the decoder reads the full `x`). The chart `φ_det222 x := phiGen (x 0) M222 tach222 (B_det222 x)
hleach222 = paramsEquivFlat M222 (chartParamsGen (x 0) M222 tach222 (B_det222 x) hleach222)`.

The bridge `chartParamsGen_eq_chartParams222` identifies the chain's layers with the EXPLICIT layer
matrices (verified EXACT, sympy `/tmp/sanity222.py`):

* `chartA0_222 x = !![x4, x4·x1; x5, x5·x1 + x6·x0]` (layer 0 = `C 1`, the Schur frame);
* `chartA1_222 x = !![x0 − x1·x2, x0·x7 − x1·x3; x2, x3]` (layer 1 = `chainA(N1)(W1)(C2)`).

The flat Jacobian det `= −x0²·x4`, so `|det Dφ_det222| = |x0|²·|x4| = |x0|^{minAdm−1}·|x4|` (the radial
`|x0|²` times the spectator `|x4|`). -/

/-- **Layer-0 chart matrix** `A⁽⁰⁾ = C 1 = Bmat 1 · chainQ(N_1) + u·Rmat 1` (`2×2`): the Schur frame at
boundary `k = 1`. `x0` the radial pivot, `x1` the chaining residual, `x4,x5` the kept column, `x6` the
E-block. -/
noncomputable def chartA0_222 (x : Fin 8 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x 4, x 4 * x 1; x 5, x 5 * x 1 + x 6 * x 0]

/-- **Layer-1 chart matrix** `A⁽¹⁾ = chainA(N_1)(W_1)(C 2)` (`2×2`): the kept row `C 2 − N_1·W_1` over
the lift row `W_1`. `C 2 = u·Rfin 2 = x0·!![1, x7]`, `N_1 = !![x1]`, `W_1 = !![x2, x3]`. -/
noncomputable def chartA1_222 (x : Fin 8 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x 0 - x 1 * x 2, x 0 * x 7 - x 1 * x 3; x 2, x 3]

/-- The genuine `Params M222` from the explicit chart matrices (`L = 2`, two layers). -/
noncomputable def chartParams222 (x : Fin 8 → ℝ) : Params M222 :=
  Fin.cons (chartA0_222 x) (Fin.cons (chartA1_222 x) (fun i => i.elim0))

/-! ### The transition + chaining-row reductions at the concrete node -/

/-- The leaf transition `C 2 = u·Rfin 2 = x0 • !![1, x7]` (`dif_neg`, `Rfin 2` value). -/
theorem Cgen222_leaf (x : Fin 8 → ℝ) :
    Cgen (x 0) M222 tach222 (B_det222 x) hleach222 2
      = (x 0) • (!![1, x 7] : Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ) := by
  show Cgen (x 0) M222 tach222 (B_det222 x) hleach222 2 = _
  unfold Cgen; rw [dif_neg (by norm_num)]; rfl

/-- The block values of `B_det222` at boundary `1` (all `rfl`). -/
theorem N1_eq222 (x : Fin 8 → ℝ) :
    (B_det222 x).Nblk 1
      = (!![x 1] : Matrix (Fin (Text M222 tach222 2))
          (Fin (Wext M222 1 - Text M222 tach222 2)) ℝ) := rfl
theorem W1_eq222 (x : Fin 8 → ℝ) :
    (B_det222 x).Wblk 1
      = (!![x 2, x 3] : Matrix (Fin (Wext M222 1 - Text M222 tach222 2))
          (Fin (Wext M222 2)) ℝ) := rfl
theorem Bmat1_eq222 (x : Fin 8 → ℝ) :
    (B_det222 x).Bmat 1
      = (!![x 4; x 5] : Matrix (Fin (Text M222 tach222 1)) (Fin (Text M222 tach222 2)) ℝ) := rfl
theorem Rmat1_eq222 (x : Fin 8 → ℝ) :
    (B_det222 x).Rmat 1
      = (!![0, 0; 0, x 6] : Matrix (Fin (Text M222 tach222 1)) (Fin (Wext M222 1)) ℝ) := rfl

/-! ### Layer 1 = `chainA(N_1)(W_1)(C 2)` = `chartA1_222` (over `Wext` widths)

The dependent-`Fin`-width cast kernel (the recurring quirk, `lean/CLAUDE.md`): after `ext i j;
fin_cases`, the row/col indices are `Fin.mk`s typed at `Fin (Wext M222 …)` (defeq `Fin 2` but not
syntactic), so the matrix-apply `simp` lemmas (`cons_val_zero/_one`, `sub_apply`, `mul_apply`) do NOT
fire. The fix (decorrelated Codex `codex/fincases-index-{prompt,answer}.md`): prove each entry as a
`have` at EXPLICIT `⟨_, by decide⟩` indices — the LHS row index rewritten to the `castAdd`/`natAdd`
kept/lift form (so `chainA_apply_castAdd`/`_natAdd` fire), the residual scalar `show`-normalized to the
clean `Fin (Text …)`-typed form so `simp` reduces it — then `exact` it into the `fin_cases` goal
(Fin proof-irrelevance unifies the `⟨0, ⋯⟩` index with the `⟨0, by decide⟩` one up to defeq). -/

/-- **Layer 1 of the chain equals the explicit `chartA1_222`** (at the `Wext`-typed widths). The kept
row (`castAdd`) is `C 2 − N_1·W_1`, the lift row (`natAdd`) is `W_1`. -/
theorem Agen1_222_eq (x : Fin 8 → ℝ) :
    Agen (x 0) M222 tach222 (B_det222 x) hleach222 1
      = (!![x 0 - x 1 * x 2, x 0 * x 7 - x 1 * x 3; x 2, x 3]
          : Matrix (Fin (Wext M222 1)) (Fin (Wext M222 2)) ℝ) := by
  have hA : Agen (x 0) M222 tach222 (B_det222 x) hleach222 1
      = chainA (genWidthEq M222 tach222 hleach222 1 (by norm_num))
          ((B_det222 x).Nblk 1) ((B_det222 x).Wblk 1)
          (Cgen (x 0) M222 tach222 (B_det222 x) hleach222 2) := by
    unfold Agen; rw [dif_pos (by norm_num)]
  -- the kept-row entry law (rewrites the LHS row index to the `castAdd` kept block)
  have kept : ∀ j : Fin (Wext M222 2),
      chainA (genWidthEq M222 tach222 hleach222 1 (by norm_num)) ((B_det222 x).Nblk 1)
          ((B_det222 x).Wblk 1) (Cgen (x 0) M222 tach222 (B_det222 x) hleach222 2)
          (⟨0, by decide⟩ : Fin (Wext M222 1)) j
        = (Cgen (x 0) M222 tach222 (B_det222 x) hleach222 2
            - (B_det222 x).Nblk 1 * (B_det222 x).Wblk 1)
            (⟨0, by decide⟩ : Fin (Text M222 tach222 2)) j := by
    intro j
    conv_lhs => rw [show (⟨0, by decide⟩ : Fin (Wext M222 1))
        = Fin.cast (genWidthEq M222 tach222 hleach222 1 (by norm_num))
            (Fin.castAdd (Wext M222 1 - Text M222 tach222 2)
              (⟨0, by decide⟩ : Fin (Text M222 tach222 2))) from by apply Fin.ext; simp]
    rw [chainA_apply_castAdd]
  -- the lift-row entry law (rewrites the LHS row index to the `natAdd` lift block)
  have lift : ∀ j : Fin (Wext M222 2),
      chainA (genWidthEq M222 tach222 hleach222 1 (by norm_num)) ((B_det222 x).Nblk 1)
          ((B_det222 x).Wblk 1) (Cgen (x 0) M222 tach222 (B_det222 x) hleach222 2)
          (⟨1, by decide⟩ : Fin (Wext M222 1)) j
        = (B_det222 x).Wblk 1 (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2)) j := by
    intro j
    conv_lhs => rw [show (⟨1, by decide⟩ : Fin (Wext M222 1))
        = Fin.cast (genWidthEq M222 tach222 hleach222 1 (by norm_num))
            (Fin.natAdd (Text M222 tach222 2)
              (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2))) from by apply Fin.ext; simp]
    rw [chainA_apply_natAdd]
  -- the four entries, each at explicit `⟨_, by decide⟩` indices (the scalar closer)
  have h00 : chainA (genWidthEq M222 tach222 hleach222 1 (by norm_num)) ((B_det222 x).Nblk 1)
      ((B_det222 x).Wblk 1) (Cgen (x 0) M222 tach222 (B_det222 x) hleach222 2)
      (⟨0, by decide⟩ : Fin (Wext M222 1)) (⟨0, by decide⟩ : Fin (Wext M222 2)) = x 0 - x 1 * x 2 := by
    rw [kept, Cgen222_leaf, N1_eq222, W1_eq222]
    show ((x 0 • (!![1, x 7] : Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ))
        - (!![x 1] : Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 1 - Text M222 tach222 2)) ℝ)
          * (!![x 2, x 3] : Matrix (Fin (Wext M222 1 - Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ))
        (⟨0, by decide⟩) (⟨0, by decide⟩) = x 0 - x 1 * x 2
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, smul_eq_mul]
    show x 0 * (1 : ℝ) - x 1 * x 2 = x 0 - x 1 * x 2; ring
  have h01 : chainA (genWidthEq M222 tach222 hleach222 1 (by norm_num)) ((B_det222 x).Nblk 1)
      ((B_det222 x).Wblk 1) (Cgen (x 0) M222 tach222 (B_det222 x) hleach222 2)
      (⟨0, by decide⟩ : Fin (Wext M222 1)) (⟨1, by decide⟩ : Fin (Wext M222 2))
        = x 0 * x 7 - x 1 * x 3 := by
    rw [kept, Cgen222_leaf, N1_eq222, W1_eq222]
    show ((x 0 • (!![1, x 7] : Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ))
        - (!![x 1] : Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 1 - Text M222 tach222 2)) ℝ)
          * (!![x 2, x 3] : Matrix (Fin (Wext M222 1 - Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ))
        (⟨0, by decide⟩) (⟨1, by decide⟩) = x 0 * x 7 - x 1 * x 3
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, smul_eq_mul]
    show x 0 * x 7 - x 1 * x 3 = x 0 * x 7 - x 1 * x 3; ring
  have h10 : chainA (genWidthEq M222 tach222 hleach222 1 (by norm_num)) ((B_det222 x).Nblk 1)
      ((B_det222 x).Wblk 1) (Cgen (x 0) M222 tach222 (B_det222 x) hleach222 2)
      (⟨1, by decide⟩ : Fin (Wext M222 1)) (⟨0, by decide⟩ : Fin (Wext M222 2)) = x 2 := by
    rw [lift, W1_eq222]; rfl
  have h11 : chainA (genWidthEq M222 tach222 hleach222 1 (by norm_num)) ((B_det222 x).Nblk 1)
      ((B_det222 x).Wblk 1) (Cgen (x 0) M222 tach222 (B_det222 x) hleach222 2)
      (⟨1, by decide⟩ : Fin (Wext M222 1)) (⟨1, by decide⟩ : Fin (Wext M222 2)) = x 3 := by
    rw [lift, W1_eq222]; rfl
  rw [hA]
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-! ### Layer 0 = `chainA(N_0)(W_0)(C 1)` = `chartA0_222` (over `Wext` widths)

At boundary `k = 0` the residual width `c_0 = Wext 0 − Text 1 = 0`, so `chainA` has NO lift block —
every row is `castAdd` and `Agen 0 = C 1 − N_0·W_0 = C 1` (`N_0 : 2×0`). `C 1 = Bmat 1 · chainQ(N_1) +
u·Rmat 1`; `chainQ(N_1)` columns are kept-`[1]` then residual-`[x1]`, so `C 1 = !![x4, x4·x1; x5,
x5·x1 + x0·x6]`. -/

/-- The chaining row `chainQ(N_1) = !![1, x1]` at the concrete node (`t = Text 2 = 1`, `c = Wext 1 −
Text 2 = 1`, `M' = Wext 1 = 2`): the kept column `[1]` then the residual column `[x1]`. -/
theorem chainQ1_eq222 (x : Fin 8 → ℝ) :
    chainQ (genWidthEq M222 tach222 hleach222 1 (by norm_num)) ((B_det222 x).Nblk 1)
      = (!![1, x 1] : Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 1)) ℝ) := by
  have c00 : chainQ (genWidthEq M222 tach222 hleach222 1 (by norm_num)) ((B_det222 x).Nblk 1)
      (⟨0, by decide⟩ : Fin (Text M222 tach222 2)) (⟨0, by decide⟩ : Fin (Wext M222 1)) = 1 := by
    conv_lhs => rw [show (⟨0, by decide⟩ : Fin (Wext M222 1))
        = Fin.cast (genWidthEq M222 tach222 hleach222 1 (by norm_num))
            (Fin.castAdd (Wext M222 1 - Text M222 tach222 2)
              (⟨0, by decide⟩ : Fin (Text M222 tach222 2))) from by apply Fin.ext; simp]
    rw [chainQ_apply_castAdd]; rfl
  have c01 : chainQ (genWidthEq M222 tach222 hleach222 1 (by norm_num)) ((B_det222 x).Nblk 1)
      (⟨0, by decide⟩ : Fin (Text M222 tach222 2)) (⟨1, by decide⟩ : Fin (Wext M222 1)) = x 1 := by
    conv_lhs => rw [show (⟨1, by decide⟩ : Fin (Wext M222 1))
        = Fin.cast (genWidthEq M222 tach222 hleach222 1 (by norm_num))
            (Fin.natAdd (Text M222 tach222 2)
              (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2))) from by apply Fin.ext; simp]
    rw [chainQ_apply_natAdd, N1_eq222]
    show (!![x 1] : Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 1 - Text M222 tach222 2)) ℝ)
      (⟨0, by decide⟩) (⟨0, by decide⟩) = x 1
    rfl
  ext i j
  fin_cases i <;> fin_cases j
  · exact c00
  · exact c01

/-- The Schur frame product `Bmat 1 · !![1, x1] + u·Rmat 1 = chartA0_222` at literal `Fin 2`. -/
theorem C1_lit222 (x : Fin 8 → ℝ) :
    (!![x 4; x 5] : Matrix (Fin 2) (Fin 1) ℝ) * (!![1, x 1] : Matrix (Fin 1) (Fin 2) ℝ)
        + (x 0) • (!![0, 0; 0, x 6] : Matrix (Fin 2) (Fin 2) ℝ)
      = (!![x 4, x 4 * x 1; x 5, x 5 * x 1 + x 6 * x 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_one, smul_eq_mul] <;>
    ring

/-- **The Schur frame `C 1 = chartA0_222`** (`C 1 = Bmat 1 · chainQ(N_1) + u·Rmat 1`): the
chaining-row product (`chainQ1_eq222`) reshaped to the explicit `2×2` block, transported to the
`Text`/`Wext` widths from the literal-`Fin` identity `C1_lit222`. -/
theorem C1_eq222 (x : Fin 8 → ℝ) :
    Cgen (x 0) M222 tach222 (B_det222 x) hleach222 1
      = (!![x 4, x 4 * x 1; x 5, x 5 * x 1 + x 6 * x 0]
          : Matrix (Fin (Text M222 tach222 1)) (Fin (Wext M222 1)) ℝ) := by
  have hC1 : Cgen (x 0) M222 tach222 (B_det222 x) hleach222 1
      = (B_det222 x).Bmat 1 * chainQ (genWidthEq M222 tach222 hleach222 1 (by norm_num))
            ((B_det222 x).Nblk 1) + (x 0) • (B_det222 x).Rmat 1 := by
    show Cgen (x 0) M222 tach222 (B_det222 x) hleach222 1 = _
    unfold Cgen; rw [dif_pos (by norm_num)]
  rw [hC1, chainQ1_eq222, Bmat1_eq222, Rmat1_eq222]
  have h1 : Text M222 tach222 1 = 2 := rfl
  have h2 : Text M222 tach222 2 = 1 := rfl
  have hw1 : Wext M222 1 = 2 := rfl
  simpa only [h1, h2, hw1] using C1_lit222 x

/-- **Layer 0 of the chain equals the explicit `chartA0_222`** (at the `Wext`-typed widths). At `c_0 =
0` the `chainA` lift block is empty (`N_0 : 2×0`, so `N_0·W_0 = 0`), so `Agen 0 = C 1` (every row is
`castAdd`). -/
theorem Agen0_222_eq (x : Fin 8 → ℝ) :
    Agen (x 0) M222 tach222 (B_det222 x) hleach222 0
      = (!![x 4, x 4 * x 1; x 5, x 5 * x 1 + x 6 * x 0]
          : Matrix (Fin (Wext M222 0)) (Fin (Wext M222 1)) ℝ) := by
  have hA : Agen (x 0) M222 tach222 (B_det222 x) hleach222 0
      = chainA (genWidthEq M222 tach222 hleach222 0 (by norm_num))
          ((B_det222 x).Nblk 0) ((B_det222 x).Wblk 0)
          (Cgen (x 0) M222 tach222 (B_det222 x) hleach222 1) := by
    unfold Agen; rw [dif_pos (by norm_num)]
  -- `N_0 · W_0 = 0` (the residual width `c_0 = 0`, so the sum is empty)
  have hN0W0 : (B_det222 x).Nblk 0 * (B_det222 x).Wblk 0 = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    exact (k.cast (show Wext M222 0 - Text M222 tach222 1 = 0 from rfl)).elim0
  -- the kept-row entry law of `chainA` at `k = 0` (every row is `castAdd`): `Agen 0 = C 1`
  have e : ∀ (r : Fin (Text M222 tach222 1)) (j : Fin (Wext M222 1)),
      Agen (x 0) M222 tach222 (B_det222 x) hleach222 0
          (Fin.cast (genWidthEq M222 tach222 hleach222 0 (by norm_num))
            (Fin.castAdd (Wext M222 0 - Text M222 tach222 1) r)) j
        = Cgen (x 0) M222 tach222 (B_det222 x) hleach222 1 r j := by
    intro r j
    rw [hA, chainA_apply_castAdd, hN0W0, Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  have e00 := e ⟨0, by decide⟩ ⟨0, by decide⟩
  have e01 := e ⟨0, by decide⟩ ⟨1, by decide⟩
  have e10 := e ⟨1, by decide⟩ ⟨0, by decide⟩
  have e11 := e ⟨1, by decide⟩ ⟨1, by decide⟩
  rw [C1_eq222] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j
  · rw [show (⟨0, by decide⟩ : Fin (Wext M222 0)) = Fin.cast (genWidthEq M222 tach222 hleach222 0
        (by norm_num)) (Fin.castAdd (Wext M222 0 - Text M222 tach222 1)
          (⟨0, by decide⟩ : Fin (Text M222 tach222 1))) from by apply Fin.ext; simp]
    exact e00
  · rw [show (⟨0, by decide⟩ : Fin (Wext M222 0)) = Fin.cast (genWidthEq M222 tach222 hleach222 0
        (by norm_num)) (Fin.castAdd (Wext M222 0 - Text M222 tach222 1)
          (⟨0, by decide⟩ : Fin (Text M222 tach222 1))) from by apply Fin.ext; simp]
    exact e01
  · rw [show (⟨1, by decide⟩ : Fin (Wext M222 0)) = Fin.cast (genWidthEq M222 tach222 hleach222 0
        (by norm_num)) (Fin.castAdd (Wext M222 0 - Text M222 tach222 1)
          (⟨1, by decide⟩ : Fin (Text M222 tach222 1))) from by apply Fin.ext; simp]
    exact e10
  · rw [show (⟨1, by decide⟩ : Fin (Wext M222 0)) = Fin.cast (genWidthEq M222 tach222 hleach222 0
        (by norm_num)) (Fin.castAdd (Wext M222 0 - Text M222 tach222 1)
          (⟨1, by decide⟩ : Fin (Text M222 tach222 1))) from by apply Fin.ext; simp]
    exact e11

/-! ### The bridge `chartParamsGen … = chartParams222` -/

/-- **The bridge** `chartParamsGen (x 0) M222 tach222 (B_det222 x) hleach222 = chartParams222 x` — the
chain's layers (`Agen 0`, `Agen 1`) reindexed to the `M`-widths ARE the explicit chart matrices
`chartA0_222`, `chartA1_222`. The reindexes are `finCongr` of `rfl`-true width equalities (`Wext M222 k
= M222 k`), value-preserving, so each reduces to the layer equalities `Agen0_222_eq`/`Agen1_222_eq`. -/
theorem chartParamsGen_eq_chartParams222 (x : Fin 8 → ℝ) :
    chartParamsGen (x 0) M222 tach222 (B_det222 x) hleach222 = chartParams222 x := by
  funext s
  fin_cases s
  · show Matrix.reindex _ _ (Agen (x 0) M222 tach222 (B_det222 x) hleach222 0) = chartA0_222 x
    rw [Agen0_222_eq]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply,
      Fin.cast_eq_self]
    rfl
  · show Matrix.reindex _ _ (Agen (x 0) M222 tach222 (B_det222 x) hleach222 1) = chartA1_222 x
    rw [Agen1_222_eq]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply,
      Fin.cast_eq_self]
    rfl

/-! ## The genuine achiever chart `phi222` + the rate `routeMCore (phi222 x) = (x0)²·V`

The chart for the `NodeAchieverChart` bundle is `phi222 x := paramsEquivFlat M222 (chartParams222 x)` —
the genuine `x`-dependent chart (the rate leg fed the constant `u`-vector; here the decoder reads the
full `x`). Via the bridge, `phi222 x = paramsEquivFlat (chartParamsGen (x 0) M222 tach222 (B_det222 x)
hleach222)`, so its loss is the banked `routeMCore_phiGen` rate at `B_det222 x`, re-checking `hC0` for
the arbitrary decoder argument `x`. -/

/-- **The genuine `(2,2,2)` achiever flat chart** `phi222 := paramsEquivFlat M222 ∘ chartParams222`. -/
noncomputable def phi222 (x : Fin 8 → ℝ) : Fin (routeMAmbient M222) → ℝ :=
  paramsEquivFlat M222 (chartParams222 x)

/-! ### The explicit unit factor (the `x0`-free polynomial)

The banked rate gives `F = x0²·VvalGen`, but for the bundle's positivity/boundedness I want the unit as
an explicit polynomial. The product `A0·A1` factors entrywise as `x0·(un-blown entry)` (sympy:
`P/x0 = !![x4, x4·x7; x2·x6+x5, x3·x6+x5·x7]`), so `F = ‖A0·A1‖² = x0²·Uval222` with `Uval222 =
x4² + (x4·x7)² + (x2·x6+x5)² + (x3·x6+x5·x7)²`. Proven directly from the explicit chart (the
`prod_two_layer221` entry form), independently of the `VvalGen` rate. -/

/-- The `(2,2,2)` un-blown product matrix `M222bar = A0·A1 / x0 = !![x4, x4·x7; x2·x6 + x5, x3·x6 +
x5·x7]` (the `x0`-stripped product). -/
noncomputable def M222bar (x : Fin 8 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x 4, x 4 * x 7; x 2 * x 6 + x 5, x 3 * x 6 + x 5 * x 7]

/-- The `(2,2,2)` unit factor `Uval222 = ‖M222bar‖²` (the `x0`-free factor of `F = x0²·U`). -/
noncomputable def Uval222 (x : Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, (M222bar x i j) ^ 2

/-- The `L = 2` layer-product entry form `(prod M A) i j = ∑_{k} A₀(i,k)·A₁(k,j)` (the explicit
two-matrix product `A⁽⁰⁾·A⁽¹⁾`, the `prodAux` dependent-`Fin`-cast closer). -/
theorem prod_two_layer_M222 (M : Fin 3 → ℕ) (A : Params M) (i : Fin (M 0)) (j : Fin (M 2)) :
    prod M A i j = ∑ k1 : Fin (M 1), A 0 i k1 * A 1 k1 j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  congr 2
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) k1 using 2

/-- The explicit `2×2` matrix product `chartA0_222 · chartA1_222 = x0 • M222bar` (the radial blow-up:
each of the 4 product entries carries one `x0`). A clean `Fin 2` matrix identity. -/
theorem chartA0_mul_chartA1_222 (x : Fin 8 → ℝ) :
    chartA0_222 x * chartA1_222 x = (x 0) • M222bar x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartA0_222, chartA1_222, M222bar, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.smul_apply,
      smul_eq_mul] <;> ring

/-- **The product as the explicit matrix product** `prod M222 (chartParams222 x) = chartA0 · chartA1`
(the `L = 2` layer product reshaped to the `Fin 2` matrix product). -/
theorem prod_chartParams222_eq (x : Fin 8 → ℝ) :
    prod M222 (chartParams222 x)
      = (chartA0_222 x * chartA1_222 x : Matrix (Fin (M222 0)) (Fin (M222 2)) ℝ) := by
  ext i j
  rw [prod_two_layer_M222 M222 (chartParams222 x) i j, Matrix.mul_apply]
  have hA0 : (chartParams222 x) 0 = chartA0_222 x := rfl
  have hA1 : (chartParams222 x) 1 = chartA1_222 x := rfl
  rw [hA0, hA1]
  rfl

/-- **The per-entry pivot factorization** `(A0·A1) i j = x0 · M222bar i j` — each product entry carries
exactly one `x0` (the radial pivot). Via the explicit `2×2` matrix product `chartA0_mul_chartA1_222`. -/
theorem prod_chartParams222_entry (x : Fin 8 → ℝ) (i j : Fin 2) :
    prod M222 (chartParams222 x) i j = x 0 * M222bar x i j := by
  rw [prod_chartParams222_eq, chartA0_mul_chartA1_222, Matrix.smul_apply, smul_eq_mul]

/-- **The loss factorization (explicit unit)** `dlnLoss M222 0 (chartParams222 x) = x0²·Uval222`. Each
of the 4 product entries is `x0·(M222bar entry)`, so the squared Frobenius norm is `x0²·Uval222`. -/
theorem dlnLoss_chartParams222_explicit (x : Fin 8 → ℝ) :
    dlnLoss M222 0 (chartParams222 x) = (x 0) ^ 2 * Uval222 x := by
  unfold dlnLoss
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  rw [Uval222, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [prod_chartParams222_entry]
  ring

/-- **The `routeMCore` factorization** `routeMCore M222 (phi222 x) = (x 0)²·U` (`U = Uval222 x`, the
explicit polynomial unit): the `symm`/`apply` cancel, leaving `dlnLoss M222 0 (chartParams222 x)`. -/
theorem routeMCore_phi222 (x : Fin 8 → ℝ) :
    routeMCore M222 (phi222 x) = (x 0) ^ 2 * Uval222 x := by
  rw [routeMCore, phi222, MeasurableEquiv.symm_apply_apply, dlnLoss_chartParams222_explicit]

/-- **`Uval222 ≥ 0`** (a sum of squares). -/
theorem Uval222_nonneg (x : Fin 8 → ℝ) : (0 : ℝ) ≤ Uval222 x := by
  rw [Uval222]; positivity

/-- `Uval222` is continuous (a polynomial in the chart coordinates), hence measurable. -/
theorem continuous_Uval222 : Continuous Uval222 := by
  unfold Uval222 M222bar
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply, Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val']
  fun_prop

/-! ## The factorization `chartParams222 = pack222 ∘ T222` and the chart Jacobian det `|x0|²·|x4|`

`phi222 = paramsEquivFlat ∘ chartParams222 = paramsEquivFlat ∘ pack222 ∘ T222 = Q222 ∘ T222`, where
`T222 = bsubst222 ∘ shear222 ∘ pb222` (the radial blow-up ∘ det-1 shear ∘ the `x4` cross-strip blow-up)
and `pack222` reshapes the 8 flat coords into the matrix slots (`Q222 = paramsEquivFlat ∘ pack222`
measure-preserving, `|det| = 1`). The det factorizes (decorrelated xhigh Codex
`codex/det222-factorization-{prompt,answer}.md`):

* `pb222 = pivotBlowupOn {0,6,7} 0` — blow up the 3 = minAdm radial directions (`x0` and the leaf/E
  normals `x6, x7`) by the pivot `x0`; det `|x0|²` (`pivotBlowupOnDeriv_det`, `active.card = 3 = minAdm`);
* `shear222` — the det-1 unitriangular Schur shear adding the bilinear KEPT terms (`−x1·x2` into slot 0,
  `+x5·x1` into slot 6, `−x1·x3` into slot 7), each reading OTHER coords (`I + M`, `M² = 0`);
* `bsubst222 = pivotBlowupOn {1,4} 4` — the cross-strip `b = x4·x1` substitution (slot 1 ↦ `x4·`slot 1);
  det `|x4|` (`pivotBlowupOnDeriv_det`, `active.card = 2`). The genuine spectator factor.

So `|det Dφ222| = |x0|²·|x4|` — radial `|x0|²` (`= minAdm−1`) TIMES the spectator `|x4|`. -/

/-- **The `(2,2,2)` radial blow-up** `pb222 = pivotBlowupOn {0,6,7} 0`: blow up the 3 radial directions
(`x0, x6, x7`) by the pivot `x0`. `det = x0² = x0^{minAdm−1}` (`active.card = 3 = minAdm`). -/
noncomputable def pb222 : (Fin 8 → ℝ) → (Fin 8 → ℝ) := pivotBlowupOn ({0, 6, 7} : Finset (Fin 8)) 0

/-- **The `(2,2,2)` Schur shear** `shear222`: the det-`1` unitriangular shear adding bilinear KEPT terms
to the blow-up coords `{0,6,7}` (each modified coord reads only OTHER coords, so `I + M`, `M² = 0`). -/
noncomputable def shear222 (p : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun i =>
    if i = 0 then p 0 - p 1 * p 2
    else if i = 6 then p 6 + p 5 * p 1
    else if i = 7 then p 7 - p 1 * p 3
    else p i

/-- **The `(2,2,2)` cross-strip substitution** `bsubst222 = pivotBlowupOn {1,4} 4`: the `b = x4·x1`
substitution (slot `1 ↦ x4·`slot 1). `det = x4` (`active.card = 2`). The spectator factor. -/
noncomputable def bsubst222 : (Fin 8 → ℝ) → (Fin 8 → ℝ) := pivotBlowupOn ({1, 4} : Finset (Fin 8)) 4

/-- **The flat composite** `T222 = bsubst222 ∘ shear222 ∘ pb222`; `pack222 ∘ T222 = chartParams222`
(`chartParams222_eq_pack_T`); `det DT222 = x0²·x4`. -/
noncomputable def T222 : (Fin 8 → ℝ) → (Fin 8 → ℝ) := bsubst222 ∘ shear222 ∘ pb222

/-- **`pb222` as an explicit vector**. -/
theorem pb222_apply (u : Fin 8 → ℝ) :
    pb222 u = ![u 0, u 1, u 2, u 3, u 4, u 5, u 0 * u 6, u 0 * u 7] := by
  funext i; fin_cases i <;> simp [pb222, pivotBlowupOn, Matrix.cons_val]

/-- **`T222` as an explicit vector**. -/
theorem T222_apply (u : Fin 8 → ℝ) :
    T222 u = ![u 0 - u 1 * u 2, u 4 * u 1, u 2, u 3, u 4, u 5, u 0 * u 6 + u 5 * u 1,
      u 0 * u 7 - u 1 * u 3] := by
  funext i
  simp only [T222, Function.comp_apply, pb222_apply]
  fin_cases i <;> simp [bsubst222, shear222, pivotBlowupOn, Matrix.cons_val] <;> ring

/-- **`pack222`** — the reshape `(Fin 8 → ℝ) → Params M222` sending the 8 `T222`-output coords (in the
semantic chart order) to the two matrix layers: `A0 = !![w4, w1; w5, w6]`, `A1 = !![w0, w7; w2, w3]`. -/
noncomputable def pack222 (w : Fin 8 → ℝ) : Params M222 :=
  Fin.cons (!![w 4, w 1; w 5, w 6] : Matrix (Fin 2) (Fin 2) ℝ)
    (Fin.cons (!![w 0, w 7; w 2, w 3] : Matrix (Fin 2) (Fin 2) ℝ) (fun i => i.elim0))

/-- **The factorization identity** `chartParams222 = pack222 ∘ T222`. -/
theorem chartParams222_eq_pack_T (x : Fin 8 → ℝ) :
    chartParams222 x = pack222 (T222 x) := by
  funext s
  fin_cases s
  · show chartA0_222 x = (pack222 (T222 x)) 0
    have hp : (pack222 (T222 x)) 0
        = (!![(T222 x) 4, (T222 x) 1; (T222 x) 5, (T222 x) 6] : Matrix (Fin 2) (Fin 2) ℝ) := rfl
    rw [hp, T222_apply]; funext i j; fin_cases i <;> fin_cases j <;> simp [chartA0_222] <;> ring
  · show chartA1_222 x = (pack222 (T222 x)) 1
    have hp : (pack222 (T222 x)) 1
        = (!![(T222 x) 0, (T222 x) 7; (T222 x) 2, (T222 x) 3] : Matrix (Fin 2) (Fin 2) ℝ) := rfl
    rw [hp, T222_apply]; funext i j; fin_cases i <;> fin_cases j <;> simp [chartA1_222] <;> ring

/-- **`shear222 ∘ pb222` as an explicit vector** (coord `1` fixed `= u 1`, the `bsubst222` pivot input). -/
theorem shear_pb222_apply (u : Fin 8 → ℝ) :
    shear222 (pb222 u)
      = ![u 0 - u 1 * u 2, u 1, u 2, u 3, u 4, u 5, u 0 * u 6 + u 5 * u 1, u 0 * u 7 - u 1 * u 3] := by
  rw [pb222_apply]
  funext i
  fin_cases i <;> simp [shear222, Matrix.cons_val] <;> ring

/-- The explicit fderiv of `shear222`: row `i` is `eᵢ` plus, on the 3 modified coords `{0,6,7}`, the
gradient of the added bilinear term (reading only KEPT coords). -/
noncomputable def shear222Deriv (p : Fin 8 → ℝ) : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    if i = 0 then (ContinuousLinearMap.proj (R := ℝ) 0)
        - ((p 1) • ContinuousLinearMap.proj 2 + (p 2) • ContinuousLinearMap.proj 1)
    else if i = 6 then (ContinuousLinearMap.proj (R := ℝ) 6)
        + ((p 5) • ContinuousLinearMap.proj 1 + (p 1) • ContinuousLinearMap.proj 5)
    else if i = 7 then (ContinuousLinearMap.proj (R := ℝ) 7)
        - ((p 1) • ContinuousLinearMap.proj 3 + (p 3) • ContinuousLinearMap.proj 1)
    else ContinuousLinearMap.proj i)

/-- **`shear222` has fderiv `shear222Deriv`** (product/sum rule on the 3 modified coords). -/
theorem shear222_hasFDerivAt (p : Fin 8 → ℝ) :
    HasFDerivAt shear222 (shear222Deriv p) p := by
  apply hasFDerivAt_pi''
  intro i
  have hap : ∀ k : Fin 8, HasFDerivAt (fun y : Fin 8 → ℝ => y k)
      (ContinuousLinearMap.proj (R := ℝ) k) p := fun k => hasFDerivAt_apply (𝕜 := ℝ) k p
  rw [shear222Deriv, ContinuousLinearMap.proj_pi]
  fin_cases i <;>
    simp only [shear222] <;>
    first
      | exact hap _
      | exact (hap 0).sub ((hap 1).mul (hap 2))
      | exact (hap 6).add ((hap 5).mul (hap 1))
      | exact (hap 7).sub ((hap 1).mul (hap 3))

/-- **Kept-row entry of `shear222Deriv`** (`i ∉ {0,6,7}`): row `i` is `proj i`, so the off-diagonal is
`0`. -/
theorem shear222Deriv_kept_row (p : Fin 8 → ℝ) (i j : Fin 8)
    (hbi : i ∉ ({0, 6, 7} : Finset (Fin 8))) (hji : i ≠ j) :
    (shear222Deriv p) (Pi.single j 1) i = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbi
  obtain ⟨n0, n6, n7⟩ := hbi
  rw [shear222Deriv, ContinuousLinearMap.pi_apply, if_neg n0, if_neg n6, if_neg n7]
  simp [ContinuousLinearMap.proj_apply, Pi.single_apply, Ne.symm hji]

set_option maxHeartbeats 1000000 in
/-- **The Schur shear determinant is `1`** (the unitriangular `I + N`, off-diagonal entries run only
from a modified row `{0,6,7}` to a KEPT column; block-triangular with identity diagonal blocks). -/
theorem shear222Deriv_det (p : Fin 8 → ℝ) : (shear222Deriv p).det = 1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  set M := LinearMap.toMatrix' (shear222Deriv p : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ)) with hM
  set b : Fin 8 → ℕ := fun i => if i ∈ ({0, 6, 7} : Finset (Fin 8)) then 0 else 1 with hb
  have hentry : ∀ i j : Fin 8, M i j = (shear222Deriv p) (Pi.single j 1) i := by
    intro i j; rw [hM, LinearMap.toMatrix'_apply]; rfl
  have hblock : ∀ i j : Fin 8, b i = b j → M i j = if i = j then 1 else 0 := by
    intro i j hbij
    rw [hentry]
    by_cases hi : i ∈ ({0, 6, 7} : Finset (Fin 8))
    · have hj : j ∈ ({0, 6, 7} : Finset (Fin 8)) := by
        by_contra h
        have e1 : b i = 0 := by simp only [hb, if_pos hi]
        have e2 : b j = 1 := by simp only [hb, if_neg h]
        rw [e1, e2] at hbij; exact absurd hbij (by norm_num)
      rw [shear222Deriv, ContinuousLinearMap.pi_apply]
      fin_cases hi <;> fin_cases hj <;>
        simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, Pi.single_apply]
    · by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        obtain ⟨n0, n6, n7⟩ := hi
        rw [shear222Deriv, ContinuousLinearMap.pi_apply, if_neg n0, if_neg n6, if_neg n7]
        simp [ContinuousLinearMap.proj_apply, Pi.single_apply]
      · rw [if_neg hij, shear222Deriv_kept_row p i j hi hij]
  have htri : M.BlockTriangular b := by
    intro i j hij
    rw [hentry]
    have hbi : i ∉ ({0, 6, 7} : Finset (Fin 8)) := by
      by_contra h
      have e1 : b i = 0 := by simp only [hb, if_pos h]
      rw [e1] at hij; exact absurd hij (Nat.not_lt_zero _)
    have hbj : j ∈ ({0, 6, 7} : Finset (Fin 8)) := by
      by_contra h
      have e1 : b i = 1 := by simp only [hb, if_neg hbi]
      have e2 : b j = 1 := by simp only [hb, if_neg h]
      rw [e1, e2] at hij; exact absurd hij (by norm_num)
    exact shear222Deriv_kept_row p i j hbi (fun heq => hbi (heq ▸ hbj))
  rw [htri.det]
  apply Finset.prod_eq_one
  intro a _
  have hid : M.toSquareBlock b a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have hMij : M.toSquareBlock b a ⟨i, hi⟩ ⟨j, hj⟩ = M i j := rfl
    rw [hMij, hblock i j (by rw [hi, hj]), Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (by rw [Subtype.mk_eq_mk]; exact h)]
  rw [hid, Matrix.det_one]

/-- The composite fderiv of `T222 = bsubst222 ∘ shear222 ∘ pb222` at `u` (the chain rule CLM). -/
noncomputable def T222Deriv (u : Fin 8 → ℝ) : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ) :=
  (pivotBlowupOnDeriv ({1, 4} : Finset (Fin 8)) 4 (shear222 (pb222 u))).comp
    ((shear222Deriv (pb222 u)).comp
      (pivotBlowupOnDeriv ({0, 6, 7} : Finset (Fin 8)) 0 u))

/-- **`T222` has fderiv `T222Deriv`** (chain rule). -/
theorem T222_hasFDerivAt (u : Fin 8 → ℝ) : HasFDerivAt T222 (T222Deriv u) u := by
  have hpb : HasFDerivAt pb222 (pivotBlowupOnDeriv ({0, 6, 7} : Finset (Fin 8)) 0 u) u :=
    hasFDerivWithinAt_univ.mp (pivotBlowupOn_hasFDerivWithinAt _ _ Set.univ u)
  have hsh : HasFDerivAt shear222 (shear222Deriv (pb222 u)) (pb222 u) := shear222_hasFDerivAt _
  have hbs : HasFDerivAt bsubst222
      (pivotBlowupOnDeriv ({1, 4} : Finset (Fin 8)) 4 (shear222 (pb222 u)))
      (shear222 (pb222 u)) :=
    hasFDerivWithinAt_univ.mp (pivotBlowupOn_hasFDerivWithinAt _ _ Set.univ (shear222 (pb222 u)))
  exact (hbs.comp u (hsh.comp u hpb))

/-- **The structural Jacobian determinant** `|det DT222| = |u 0|²·|u 4|` — `det D(pb222) = u₀²` (3 active
coords), `det D(shear222) = 1`, `det D(bsubst222) = u₄` (2 active coords; coord `4` fixed by shear/pb). -/
theorem T222Deriv_abs_det (u : Fin 8 → ℝ) :
    |(T222Deriv u).det| = |u 0| ^ 2 * |u 4| := by
  have hpbdet : (pivotBlowupOnDeriv ({0, 6, 7} : Finset (Fin 8)) 0 u).det = (u 0) ^ 2 := by
    rw [pivotBlowupOnDeriv_det _ _ (by decide)]
    norm_num [show ({0, 6, 7} : Finset (Fin 8)).card = 3 from by decide]
  have hbsdet : (pivotBlowupOnDeriv ({1, 4} : Finset (Fin 8)) 4 (shear222 (pb222 u))).det
      = (u 4) ^ 1 := by
    rw [pivotBlowupOnDeriv_det _ _ (by decide)]
    have hc4 : (shear222 (pb222 u)) 4 = u 4 := by rw [shear_pb222_apply]; rfl
    rw [hc4]; norm_num [show ({1, 4} : Finset (Fin 8)).card = 2 from by decide]
  have hshdet : (shear222Deriv (pb222 u)).det = 1 := shear222Deriv_det _
  rw [T222Deriv, ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp,
    ContinuousLinearMap.coe_comp, LinearMap.det_comp,
    ← ContinuousLinearMap.det, ← ContinuousLinearMap.det, ← ContinuousLinearMap.det,
    hpbdet, hshdet, hbsdet]
  rw [abs_mul, abs_mul]
  simp only [pow_one, abs_one, mul_one, one_mul, abs_pow]
  ring

/-! ## The outer reshape `Q222 = paramsEquivFlat ∘ pack222` (measure-preserving, `|det| = 1`) -/

/-- `pack222` as a continuous ℝ-linear map (each output matrix entry is one input coordinate). -/
noncomputable def pack222CLM : (Fin 8 → ℝ) →L[ℝ] Params M222 :=
  ContinuousLinearMap.pi (fun s =>
    match s with
    | ⟨0, _⟩ => ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
        ContinuousLinearMap.proj (![![4, 1], ![5, 6]] i j : Fin 8)))
    | ⟨1, _⟩ => ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
        ContinuousLinearMap.proj (![![0, 7], ![2, 3]] i j : Fin 8)))
    | ⟨n + 2, h⟩ => absurd h (by omega))

/-- `pack222CLM` has underlying function `pack222`. -/
theorem pack222CLM_coe : ⇑pack222CLM = pack222 := by
  funext w s
  fin_cases s
  · funext i j; fin_cases i <;> fin_cases j <;> rfl
  · funext i j; fin_cases i <;> fin_cases j <;> rfl

/-- **The outer-reindex CLM** `Q222CLM = paramsEquivFlatCLE ∘ pack222CLM`. -/
noncomputable def Q222CLM : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ) :=
  (paramsEquivFlatCLE M222).toContinuousLinearMap.comp pack222CLM

/-- The explicit slot bijection `Fin 8 ≃ FlatIdx M222` pinning `pack222`'s flat-coord → matrix-slot
order (A0 = `!![w4,w1;w5,w6]`, A1 = `!![w0,w7;w2,w3]`). `decide`-checked inverses. -/
noncomputable def fin8EquivFlatIdxDet222 : Fin 8 ≃ FlatIdx M222 where
  toFun := fun k =>
    match k with
    | ⟨0, _⟩ => ⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨0, by decide⟩⟩
    | ⟨1, _⟩ => ⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ⟨1, by decide⟩⟩
    | ⟨2, _⟩ => ⟨⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, ⟨0, by decide⟩⟩
    | ⟨3, _⟩ => ⟨⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, ⟨1, by decide⟩⟩
    | ⟨4, _⟩ => ⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ⟨0, by decide⟩⟩
    | ⟨5, _⟩ => ⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, ⟨0, by decide⟩⟩
    | ⟨6, _⟩ => ⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, ⟨1, by decide⟩⟩
    | ⟨7, _⟩ => ⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨1, by decide⟩⟩
    | ⟨n + 8, h⟩ => absurd h (by omega)
  invFun := fun q =>
    match q with
    | ⟨⟨⟨1, _⟩, ⟨0, _⟩⟩, ⟨0, _⟩⟩ => 0 | ⟨⟨⟨0, _⟩, ⟨0, _⟩⟩, ⟨1, _⟩⟩ => 1
    | ⟨⟨⟨1, _⟩, ⟨1, _⟩⟩, ⟨0, _⟩⟩ => 2 | ⟨⟨⟨1, _⟩, ⟨1, _⟩⟩, ⟨1, _⟩⟩ => 3
    | ⟨⟨⟨0, _⟩, ⟨0, _⟩⟩, ⟨0, _⟩⟩ => 4 | ⟨⟨⟨0, _⟩, ⟨1, _⟩⟩, ⟨0, _⟩⟩ => 5
    | ⟨⟨⟨0, _⟩, ⟨1, _⟩⟩, ⟨1, _⟩⟩ => 6 | ⟨⟨⟨1, _⟩, ⟨0, _⟩⟩, ⟨1, _⟩⟩ => 7
  left_inv := by decide
  right_inv := by decide

/-- **The slot equation** `pack222 w q.1.1 q.1.2 q.2 = w (fin8EquivFlatIdxDet222.symm q)` (`rfl` per slot). -/
theorem hpack222 (w : Fin 8 → ℝ) (q : FlatIdx M222) :
    pack222 w q.1.1 q.1.2 q.2 = w (fin8EquivFlatIdxDet222.symm q) := by
  obtain ⟨⟨s, i⟩, j⟩ := q
  fin_cases s <;> fin_cases i <;> fin_cases j <;> rfl

/-- **`pack222` is measure-preserving** — the reusable reshape-MP at `fin8EquivFlatIdxDet222`. -/
theorem measurePreserving_pack222 :
    MeasurePreserving pack222 (volume : Measure (Fin 8 → ℝ)) (volume : Measure (Params M222)) :=
  measurePreserving_paramsPack_of_flatIdxEquiv M222 fin8EquivFlatIdxDet222 pack222 hpack222

/-- **`Q222CLM = paramsEquivFlat ∘ pack222` is measure-preserving.** -/
theorem measurePreserving_Q222CLM :
    MeasurePreserving (Q222CLM : (Fin 8 → ℝ) → (Fin 8 → ℝ))
      (volume : Measure (Fin 8 → ℝ)) volume := by
  have hcomp : (Q222CLM : (Fin 8 → ℝ) → (Fin 8 → ℝ)) = (paramsEquivFlat M222) ∘ pack222 := by
    funext w
    have h1 : Q222CLM w = paramsEquivFlatCLE M222 (pack222CLM w) := rfl
    rw [Function.comp_apply, h1, paramsEquivFlatCLE_coe, pack222CLM_coe]
  rw [hcomp]
  exact (measurePreserving_paramsEquivFlat _).comp measurePreserving_pack222

/-- **`|det Q222CLM| = 1`** — the outer reshape is a measure-preserving coordinate permutation. -/
theorem Q222CLM_abs_det : |LinearMap.det (Q222CLM : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ))| = 1 :=
  continuousLinearMap_abs_det_eq_one_of_measurePreserving Q222CLM measurePreserving_Q222CLM

/-! ## The chart fderiv `phi222` + the structural determinant `|det Dφ| = |x0|²·|x4|` -/

/-- `pack222` (linear) has constant fderiv `pack222CLM`. -/
theorem pack222_hasFDerivAt (w : Fin 8 → ℝ) : HasFDerivAt pack222 pack222CLM w := by
  have h : HasFDerivAt (⇑pack222CLM) pack222CLM w := pack222CLM.hasFDerivAt
  exact h.congr_of_eventuallyEq (by filter_upwards with v; rw [pack222CLM_coe])

/-- **The `(2,2,2)` chart fderiv** `phi222Deriv u = Q222CLM ∘L T222Deriv u`. -/
noncomputable def phi222Deriv (u : Fin 8 → ℝ) : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ) :=
  Q222CLM.comp (T222Deriv u)

/-- **`phi222` has fderiv `phi222Deriv`** — the chain rule for `phi222 = paramsEquivFlat ∘ pack222 ∘ T222`. -/
theorem phi222_hasFDerivAt (u : Fin 8 → ℝ) : HasFDerivAt phi222 (phi222Deriv u) u := by
  have hchart : HasFDerivAt chartParams222 (pack222CLM.comp (T222Deriv u)) u := by
    have hcomp : HasFDerivAt (fun v => pack222 (T222 v)) (pack222CLM.comp (T222Deriv u)) u :=
      (pack222_hasFDerivAt (T222 u)).comp u (T222_hasFDerivAt u)
    exact hcomp.congr_of_eventuallyEq (by filter_upwards with v; rw [chartParams222_eq_pack_T])
  have hflat : HasFDerivAt (paramsEquivFlat M222)
      ((paramsEquivFlatCLE M222).toContinuousLinearMap) (chartParams222 u) :=
    hasFDerivAt_paramsEquivFlat _ _
  have : HasFDerivAt (fun u => paramsEquivFlat M222 (chartParams222 u))
      (((paramsEquivFlatCLE M222).toContinuousLinearMap).comp (pack222CLM.comp (T222Deriv u))) u :=
    hflat.comp u hchart
  rw [phi222Deriv, Q222CLM]
  exact this

/-- **The genuine chart Jacobian determinant** `|det Dφ222| = |x0|²·|x4|` (radial `|x0|² = |x0|^{minAdm−1}`
times the spectator `|x4|`). `phi222Deriv = Q222CLM ∘ T222Deriv` has `|det| = 1 · (|x0|²·|x4|)`. -/
theorem phi222_abs_det (u : Fin 8 → ℝ) :
    |(phi222Deriv u).det| = |u 0| ^ 2 * |u 4| := by
  rw [phi222Deriv, ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp,
    abs_mul, Q222CLM_abs_det, one_mul, ← ContinuousLinearMap.det, T222Deriv_abs_det]

/-- `phi222` is differentiable (C¹). -/
theorem differentiable_phi222 : Differentiable ℝ phi222 :=
  fun u => (phi222_hasFDerivAt u).differentiableAt

/-! ## Injectivity off `{x0 = 0} ∪ {x4 = 0}`, continuity, image containment

The chart is a local diffeo exactly off `{x0 = 0} ∪ {x4 = 0}` (the det `|x0|²·|x4|` vanishing locus). It
is `InjOn` there: the spectators `x2, x3, x4, x5` are read directly; `x1` via `÷ x4` (needs `x4 ≠ 0`);
`x0 = A1(0,0) + x1·x2`; `x6, x7` via `÷ x0` (needs `x0 ≠ 0`). Both exceptional sets are null, so the
cov runs on the doubly-punctured complement (the `{x4 = 0}` slice added back as a two-sided null
contribution, exactly as the `(3,3,4)` `{u 1 = 0}` slice). -/

/-- **`chartParams222` is injective off `{x0 = 0} ∪ {x4 = 0}`**. -/
theorem chartParams222_injOn :
    Set.InjOn chartParams222 {u : Fin 8 → ℝ | u 0 ≠ 0 ∧ u 4 ≠ 0} := by
  rintro u ⟨hu0, hu4⟩ v ⟨hv0, hv4⟩ huv
  have hA0 : chartA0_222 u = chartA0_222 v := congrFun huv 0
  have hA1 : chartA1_222 u = chartA1_222 v := congrFun huv 1
  have eA0 := fun i j => congrFun (congrFun hA0 i) j
  have eA1 := fun i j => congrFun (congrFun hA1 i) j
  -- spectators read directly
  have h4 : u 4 = v 4 := by have := eA0 0 0; simpa [chartA0_222] using this
  have h5 : u 5 = v 5 := by have := eA0 1 0; simpa [chartA0_222] using this
  have h2 : u 2 = v 2 := by have := eA1 1 0; simpa [chartA1_222] using this
  have h3 : u 3 = v 3 := by have := eA1 1 1; simpa [chartA1_222] using this
  -- x1 via ÷ x4 (A0(0,1) = x4·x1)
  have h1 : u 1 = v 1 := by
    have he := eA0 0 1
    simp only [chartA0_222, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply, Matrix.cons_val] at he
    rw [h4] at he
    exact mul_left_cancel₀ hv4 he
  -- x0 = A1(0,0) + x1·x2
  have h0 : u 0 = v 0 := by
    have he := eA1 0 0
    simp only [chartA1_222, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply, Matrix.cons_val] at he
    rw [h1, h2] at he; linarith [he]
  -- x6 via ÷ x0 (A0(1,1) = x5·x1 + x6·x0)
  have h6 : u 6 = v 6 := by
    have he := eA0 1 1
    simp only [chartA0_222, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply, Matrix.cons_val] at he
    rw [h5, h1, h0] at he
    have : u 6 * v 0 = v 6 * v 0 := by linarith [he]
    exact mul_right_cancel₀ hv0 this
  -- x7 via ÷ x0 (A1(0,1) = x0·x7 − x1·x3)
  have h7 : u 7 = v 7 := by
    have he := eA1 0 1
    simp only [chartA1_222, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply, Matrix.cons_val] at he
    rw [h1, h3, h0] at he
    have : v 0 * u 7 = v 0 * v 7 := by linarith [he]
    exact mul_left_cancel₀ hv0 this
  funext j; fin_cases j <;>
    first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7

/-- **`phi222` is injective off `{x0 = 0} ∪ {x4 = 0}`**. -/
theorem phi222_injOn : Set.InjOn phi222 {u : Fin 8 → ℝ | u 0 ≠ 0 ∧ u 4 ≠ 0} := by
  intro u hu v hv huv
  exact chartParams222_injOn hu hv ((paramsEquivFlat M222).injective huv)

/-- `chartParams222` is continuous (each layer matrix is a polynomial). -/
theorem continuous_chartParams222 : Continuous chartParams222 := by
  apply continuous_pi
  intro s
  fin_cases s
  · change Continuous chartA0_222
    unfold chartA0_222
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ continuous_const) <;>
      (refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ continuous_const) <;> fun_prop)
  · change Continuous chartA1_222
    unfold chartA1_222
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ continuous_const) <;>
      (refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ continuous_const) <;> fun_prop)

/-- **`phi222` is continuous**. -/
theorem continuous_phi222 : Continuous phi222 :=
  (continuous_paramsEquivFlat _).comp continuous_chartParams222

/-- **`phi222 0 = 0`** — the chart reaches the deepest point (every entry is a monomial in the coords). -/
theorem phi222_zero : phi222 (0 : Fin 8 → ℝ) = 0 := by
  have hchart : chartParams222 (0 : Fin 8 → ℝ) = (fun _ => 0 : Params M222) := by
    funext s
    fin_cases s
    · change chartA0_222 (0 : Fin 8 → ℝ) = 0
      funext i j; fin_cases i <;> fin_cases j <;> simp [chartA0_222]
    · change chartA1_222 (0 : Fin 8 → ℝ) = 0
      funext i j; fin_cases i <;> fin_cases j <;> simp [chartA1_222]
  rw [phi222, hchart]
  exact paramsEquivFlat_deepest _

/-- The `(2,2,2)` leaf Jacobian exponents on `Fin 8` (`= Fin (routeMAmbient M222)` defeq): `2` on the
binding pivot axis `0` (the radial `|x0|² = |x0|^{minAdm−1}`); `1` on the spectator axis `4` (the `|x4|`
factor, a `k = 0` axis); `0` elsewhere. -/
def leafH222 : Fin 8 → ℕ := fun j => if j = 0 then 2 else if j = 4 then 1 else 0

/-- `leafH222 0 = 2 = minAdm M222 − 1` (the binding axis carries the radial exponent). -/
theorem leafH222_pivot : leafH222 (0 : Fin 8) = minAdm M222 - 1 := by
  rw [minAdm_M222]; rfl

/-- **The Jacobian weight `∏_j |u_j|^{leafH222 j} = |u 0|²·|u 4|`** — the genuine `|det Dφ|`. -/
theorem leafH222_prod_eq (u : Fin 8 → ℝ) :
    (∏ j, |u j| ^ (leafH222 j)) = |u 0| ^ 2 * |u 4| := by
  rw [Fintype.prod_eq_mul (0 : Fin 8) (4 : Fin 8) (by decide)
    (fun x ⟨hx0, hx4⟩ => by simp [leafH222, hx0, hx4])]
  simp [leafH222]

/-- **The `{x4 = 0}` slice image is null** — the C¹ image of `(V \ {x0=0}) ∩ {x4=0}` is Lebesgue-null. -/
theorem phi222_slice_image_null (V : Set (Fin 8 → ℝ)) :
    (volume : Measure (Fin 8 → ℝ)) (phi222 '' ((V \ {x | x 0 = 0}) ∩ {x | x 4 = 0})) = 0 := by
  refine MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    differentiable_phi222.differentiableOn ?_
  exact measure_mono_null Set.inter_subset_right (coordZero_null 4)

/-- **The genuine geometric change-of-variables for `phi222`** (the `cov` field): the Jacobian c-o-v on
the doubly-punctured `(V \ {x0=0}) \ {x4=0}` (where `phi222` is `InjOn`), with `|det Dφ| = |x0|²·|x4|`;
then the `{x4=0}` slice added back as a TWO-SIDED null contribution (LHS image null —
`phi222_slice_image_null`; RHS weight `|x4| = 0`, the slice null — `coordZero_null 4`). -/
theorem phi222_cov (V : Set (Fin 8 → ℝ)) (hV : MeasurableSet V) (g : (Fin 8 → ℝ) → ℝ≥0∞) :
    ∫⁻ x in phi222 '' (V \ {x | x 0 = 0}), g x
      = ∫⁻ u in V \ {x | x 0 = 0}, ENNReal.ofReal (∏ j, |u j| ^ (leafH222 j)) * g (phi222 u) := by
  simp only [leafH222_prod_eq]
  set S := V \ {x : Fin 8 → ℝ | x 0 = 0} with hS
  set Sg := S \ {x : Fin 8 → ℝ | x 4 = 0} with hSg
  have hSmeas : MeasurableSet S :=
    hV.diff (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)
  have hSgmeas : MeasurableSet Sg :=
    hSmeas.diff (measurableSet_eq_fun (measurable_pi_apply 4) measurable_const)
  have hcov : ∫⁻ x in phi222 '' Sg, g x
      = ∫⁻ u in Sg, ENNReal.ofReal |(phi222Deriv u).det| * g (phi222 u) := by
    refine lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSgmeas
      (fun x _ => (phi222_hasFDerivAt x).hasFDerivWithinAt) ?_ g
    intro x hx y hy hxy
    exact phi222_injOn ⟨hx.1.2, hx.2⟩ ⟨hy.1.2, hy.2⟩ hxy
  have hcov' : ∫⁻ x in phi222 '' Sg, g x
      = ∫⁻ u in Sg, ENNReal.ofReal (|u 0| ^ 2 * |u 4|) * g (phi222 u) := by
    rw [hcov]; refine setLIntegral_congr_fun hSgmeas (fun u _ => ?_); rw [phi222_abs_det]
  have hLHS : ∫⁻ x in phi222 '' S, g x = ∫⁻ x in phi222 '' Sg, g x := by
    refine setLIntegral_congr ?_
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (phi222_slice_image_null V)
      rintro y ⟨⟨x, hxS, rfl⟩, hy⟩
      by_cases hx4 : x 4 = 0
      · exact ⟨x, ⟨hxS, hx4⟩, rfl⟩
      · exact absurd ⟨x, ⟨hxS, hx4⟩, rfl⟩ hy
    · rw [show phi222 '' Sg \ phi222 '' S = ∅ from by
        rw [Set.diff_eq_empty]; exact Set.image_mono Set.diff_subset]
      exact measure_empty
  have hRHS : ∫⁻ u in Sg, ENNReal.ofReal (|u 0| ^ 2 * |u 4|) * g (phi222 u)
      = ∫⁻ u in S, ENNReal.ofReal (|u 0| ^ 2 * |u 4|) * g (phi222 u) := by
    refine setLIntegral_congr (MeasureTheory.diff_ae_eq_self.2 ?_)
    exact measure_mono_null Set.inter_subset_right (coordZero_null 4)
  rw [hLHS, hcov', hRHS]

/-- **Image containment**: a small source box `[0,δ]⁸` maps into `cubeBox 8 ε`. -/
theorem phi222_image_subset_cubeBox (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, phi222 '' (Set.univ.pi (fun _ : Fin 8 => Set.Icc (0 : ℝ) δ))
      ⊆ cubeBox (routeMAmbient M222) ε := by
  have hopen : IsOpen (Set.univ.pi (fun _ : Fin 8 => Set.Ioo (-ε) ε)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hmem : (0 : Fin 8 → ℝ) ∈ phi222 ⁻¹' (Set.univ.pi (fun _ : Fin 8 => Set.Ioo (-ε) ε)) := by
    simp only [Set.mem_preimage, phi222_zero, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ioo, Pi.zero_apply]
    exact fun i => ⟨by linarith, hε⟩
  obtain ⟨δ, hδ, hsub⟩ := cubeBox_subset_of_isOpen (hopen.preimage continuous_phi222) hmem
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxcube : x ∈ cubeBox 8 δ := by
    simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx ⊢
    intro i; exact ⟨le_trans (by linarith [hδ]) (hx i).1, (hx i).2⟩
  have hxmem : phi222 x ∈ Set.univ.pi (fun _ : Fin 8 => Set.Ioo (-ε) ε) :=
    Set.mem_preimage.mp (hsub hxcube)
  refine Set.mem_pi.mpr (fun i _ => ?_)
  have hi := (Set.mem_pi.mp hxmem) i (Set.mem_univ i)
  rw [Set.mem_Ioo] at hi
  rw [Set.mem_Icc]
  exact ⟨hi.1.le, hi.2.le⟩

/-! ## The `U > 0` a.e. positivity (the genuine-polynomial null-zero-set route)

`Uval222 = x4² + (x4·x7)² + (x2·x6+x5)² + (x3·x6+x5·x7)²` is `eval u UPoly222` for a nonzero
`MvPolynomial`, so `{Uval222 = 0}` is Lebesgue-null (`MvPolynomial.ae_eval_ne_zero`). -/

open MvPolynomial in
/-- The formal polynomial `UPoly222` with `eval u UPoly222 = Uval222 u` (the `Uval222` expression with
`X k` for coord `k`). -/
noncomputable def UPoly222 : MvPolynomial (Fin 8) ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    ((!![X 4, X 4 * X 7; X 2 * X 6 + X 5, X 3 * X 6 + X 5 * X 7]
        : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 8) ℝ)) i j) ^ 2

open MvPolynomial in
/-- `eval u UPoly222 = Uval222 u` (the encoding identity; `eval` a ring hom). -/
theorem eval_UPoly222 (u : Fin 8 → ℝ) : MvPolynomial.eval u UPoly222 = Uval222 u := by
  rw [UPoly222, Uval222, M222bar]
  simp only [map_sum, map_pow]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  refine congrArg (· ^ 2) ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val, MvPolynomial.eval_X]

open MvPolynomial in
/-- **`UPoly222 ≠ 0`** — the witness `x4 = 1` (others `0`): `M222bar = !![1,0;0,0]`, `Uval222 = 1 ≠ 0`. -/
theorem UPoly222_ne_zero : UPoly222 ≠ 0 := by
  intro h0
  set w : Fin 8 → ℝ := Pi.single 4 1 with hw
  have hval : Uval222 w = 1 := by
    rw [Uval222, M222bar]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply, Matrix.cons_val]
    simp only [hw, Pi.single_apply, Fin.reduceEq, if_true, if_false]
    norm_num
  have : MvPolynomial.eval w UPoly222 = 1 := by rw [eval_UPoly222]; exact hval
  rw [h0] at this; simp at this

/-- **`Uval222 > 0` a.e.** (the soundness-critical positivity). -/
theorem Uval222_ae_pos : ∀ᵐ u : Fin 8 → ℝ, 0 < Uval222 u := by
  have hae := MvPolynomial.ae_eval_ne_zero UPoly222 UPoly222_ne_zero
  filter_upwards [hae] with u hu
  rw [eval_UPoly222] at hu
  exact lt_of_le_of_ne (Uval222_nonneg u) (Ne.symm hu)

/-- `Uval222` is bounded above on the source box `[0,δ]⁸` (continuous on a compact box). -/
theorem Uval222_le_on_box (δ : ℝ) :
    ∃ B, 0 < B ∧ ∀ u ∈ Set.univ.pi (fun _ : Fin 8 => Set.Icc (0 : ℝ) δ), Uval222 u ≤ B := by
  have hcpt : IsCompact (Set.univ.pi (fun _ : Fin 8 => Set.Icc (0 : ℝ) δ)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  rcases (Set.univ.pi (fun _ : Fin 8 => Set.Icc (0 : ℝ) δ)).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun u hu => absurd (he ▸ hu) (Set.mem_empty_iff_false u).mp⟩
  · obtain ⟨u0, _, hu0⟩ := hcpt.exists_isMaxOn hne continuous_Uval222.continuousOn
    exact ⟨max 1 (Uval222 u0), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun u hu => le_trans (hu0 hu) (le_max_right _ _)⟩

/-! ## The leaf monomial + the `NodeAchieverChart M222` bundle + the atom discharge

`leafH222 0 = 2 = minAdm−1` (the radial pivot), `leafH222 4 = 1` (the spectator `x4`, on a `k = 0`
axis so it does NOT lower the threshold). Binding axis `0`, threshold `(2+1)/(2·1) = 3/2 = ½·minAdm`. -/

/-- **The leaf-integrand identity for the `(2,2,2)` achiever chart**: `(∏_j |u_j|^{leafH222 j}) ·
|routeMCore M222 (phi222 u)|^{−c} = monomialIntegrand · (Uval222 u)^{−c}`. -/
theorem leaf_integrand222 (c : ℝ) (u : Fin 8 → ℝ) :
    (∏ j, |u j| ^ (leafH222 j)) * |routeMCore M222 (phi222 u)| ^ (-c)
      = monomialIntegrand 8 (nodeLeafK 8 0) leafH222 c u
        * (Uval222 u) ^ (-c) := by
  have hmono : monomialIntegrand 8 (nodeLeafK 8 0) leafH222 c u
      = (|u 0| ^ 2 * |u 4|) * (|u 0| ^ 2) ^ (-c) := by
    unfold monomialIntegrand
    rw [leafH222_prod_eq]
    congr 1
    rw [Finset.prod_eq_single (0 : Fin 8)]
    · simp [nodeLeafK]
    · intro j _ hj; simp [nodeLeafK, hj]
    · intro h; exact absurd (Finset.mem_univ (0 : Fin 8)) h
  rw [hmono, leafH222_prod_eq, routeMCore_phi222]
  have hUnn : (0 : ℝ) ≤ Uval222 u := Uval222_nonneg u
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hUnn),
    Real.mul_rpow (sq_nonneg _) hUnn, ← sq_abs (u 0)]
  ring

/-- **The `(2,2,2)` achiever chart bundle** — Route 2a on the genuine MULTI-boundary node, built through
the general `chainOfMt`/`GenBlk` engine (the bridge `chartParamsGen_eq_chartParams222`), with the genuine
Schur-coupled Jacobian `|det Dφ| = |x0|²·|x4|` (radial `|x0|² = |x0|^{minAdm−1}` × spectator `|x4|`).
All fields banked sorry-free. -/
noncomputable def nodeChart222 : NodeAchieverChart M222 where
  hpos := by rw [minAdm_M222]; norm_num
  phi := phi222
  p := (⟨0, by decide⟩ : Fin (routeMAmbient M222))
  leafH := leafH222
  leafH_pivot := leafH222_pivot
  Ufun := Uval222
  Ubound := fun δ => by
    obtain ⟨B, hB0, hBle⟩ := Uval222_le_on_box δ
    exact ⟨B, hB0, hBle, ae_restrict_of_ae Uval222_ae_pos⟩
  Umeas := continuous_Uval222.measurable
  -- the pointwise rate ⟹ the a.e. `leaf_integrand` field (free `of_forall` — `phi222` is polynomial)
  leaf_integrand := fun c => Filter.Eventually.of_forall (leaf_integrand222 c)
  cov := phi222_cov
  image_subset := phi222_image_subset_cubeBox

/-- **`routeMCore_box_diverges_achiever` for `M = (2,2,2)`** — the achiever-path box-divergence atom
discharged at the smallest genuinely MULTI-boundary node `(2,2,2)` (`minAdm = 3`, two rank-drops),
via the chart bundle `nodeChart222` fed through the M-agnostic assembly
`routeMCore_box_diverges_of_nodeChart`. ROUTE 2a end-to-end: the chart goes through the general
`chainOfMt`/`GenBlk` engine (the full-rank decoder `B_det222`, the bridge to the explicit Schur-frame
matrices), so the multi-boundary Schur coupling — load-bearing for the rate — IS exercised (unlike the
pure-radial `(2,2,1)`/`(4,4,2,2)` anchors). The headline (2,2,2) validate-small. -/
theorem routeMCore_box_diverges_achiever_222 (c' : NNReal)
    (hc' : (minAdm M222 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M222) ε,
      ENNReal.ofReal (|routeMCore M222 x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_nodeChart M222 nodeChart222 c' hc' ε hε

end DLNFibre.DLN.RLCT
