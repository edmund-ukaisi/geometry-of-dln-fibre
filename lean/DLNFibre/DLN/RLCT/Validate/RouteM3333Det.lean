import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId
import DLNFibre.DLN.RLCT.Validate.RouteMGenChainBridge
import DLNFibre.DLN.RLCT.Validate.RouteM3333
import DLNFibre.DLN.RLCT.Validate.RouteM3333Atom

/-!
# `RouteM3333Det` — the `(3,3,3,3)` ROUTE-2a parametric-bridge VALIDATE-SMALL (3-boundary)

The genuine 3-boundary validate-small for the ∀M parametric bridge (`certificate-genM-det.md`, ROUTE (i)
PARAMETRIC). `(3,3,3,3)` drops rank at ALL THREE boundaries (`t* = (2,1,0)`, `minAdm = 6`), exercising
the multi-boundary Schur/LDU coupling that the single-drop anchors `(2,2,1)`/`(4,4,2,2)` and the
two-boundary `(2,2,2)` do not.

The headline: the FULL-RANK decoder `B_det3333` (the `(2,2,2)` `B_det222` pattern at `L = 3`) reproduces
the BANKED hand-built explicit chart `chartParams3333` (`RouteM3333`) through the general
`chainOfMt`/`GenBlk` engine. The bridge `chartParamsGen_eq_chartParams3333` is the width-parametric funext
template (sympy-verified EXACT, `/tmp/match3333.py`: all three chain layers `A_0/A_1/A_2` equal
`chartA3333`/`chartB3333`/`chartC3333`):

* boundary `k = 0` identity (`Bmat 0 = I`, `c_0 = 0`);
* boundary `k = 1` Schur frame `Bmat 1` (3×2, the deepest LDU core `K`), `Nblk 1 = [m₁;m₂]`, `Wblk 1 =
  [r]`, `Rmat 1 = e₂₂` (the fixed-`1` pivot scaled by `u`);
* boundary `k = 2` Schur frame `Bmat 2 = [b; ℓb]` (2×1), `Nblk 2 = [n₁,n₂]`, `Wblk 2 = [h₁;h₂]`,
  `Rmat 2 = [[0],[0,η]]`;
* LIVE leaf `Rfin 3 = [ζ]` (1×3) — the D1 fix.

Since `phiGen (x 0) M3333 tach3333 (B_det3333 x) hle = paramsEquivFlat (chartParamsGen …) =
paramsEquivFlat (chartParams3333 x) = phi3333 x` (the bridge), the BANKED `phi3333`-based det / cov / atom
(`RouteM3333`/`RouteM3333Atom`: `phi3333_abs_det = |u0|⁵·|u1|⁴·|u4|²·|u9|³`, `nodeChart3333`,
`routeMCore_box_diverges_achiever_3333`) transfer to the ROUTE-2a chart for free — no new bundle.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the bridge is pure matrix algebra).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-- The ACHIEVER descent path for `(3,3,3,3)`: `tach3333 = (3,2,1,0)` (`t 0 = M 0 = 3` the identity-
boundary convention; Aoyagi `T* = (2,1,0)`). `Text = [3,3,2,1,0]`, `Wext = [3,3,3,3]`, chain-codim
`= minAdm = 6`. -/
abbrev tach3333 : Fin 4 → ℕ := ![3, 2, 1, 0]

/-! ## The widths (all `rfl`/`decide` at the concrete node) -/

theorem Text3333_0 : Text M3333 tach3333 0 = 3 := rfl
theorem Text3333_1 : Text M3333 tach3333 1 = 3 := rfl
theorem Text3333_2 : Text M3333 tach3333 2 = 2 := rfl
theorem Text3333_3 : Text M3333 tach3333 3 = 1 := rfl
theorem Wext3333_0 : Wext M3333 0 = 3 := rfl
theorem Wext3333_1 : Wext M3333 1 = 3 := rfl
theorem Wext3333_2 : Wext M3333 2 = 3 := rfl
theorem Wext3333_3 : Wext M3333 3 = 3 := rfl

/-- The chain admissibility `hle : Text(k+1) ≤ Wext k` for `(3,3,3,3)` (all `k < 3`). -/
theorem hleach3333 : ∀ k, k < 3 → Text M3333 tach3333 (k + 1) ≤ Wext M3333 k := by
  intro k hk
  interval_cases k <;> decide

/-! ## The full-rank decoder `B_det3333 : GenBlk M3333 tach3333`

(sympy-verified EXACT — `/tmp/match3333.py`.) Widths: `Text = [3,3,2,1,0]`, `Wext = [3,3,3,3]`.
- `Bmat 0 = I₃` (identity boundary); `Bmat 1` (3×2, the deepest LDU core `K` rows);
  `Bmat 2 = [[b],[ℓ·b]]` (2×1).
- `Nblk 1 = [[m₁],[m₂]]` (2×1); `Nblk 2 = [[n₁,n₂]]` (1×2).
- `Wblk 1 = [[r₀,r₁,r₂]]` (1×3); `Wblk 2 = [[h₁],[h₂]]` (2×3).
- `Rmat 1 = e₂₂` (the fixed-`1` pivot, scaled by `u`); `Rmat 2 = [[0,0,0],[0,η₁,η₂]]`; `Rmat 0 = 0`.
- `Rfin 3 = [[ζ₀,ζ₁,ζ₂]]` (1×3) — the LIVE leaf (D1 fix). -/
noncomputable def B_det3333 (x : Fin 27 → ℝ) : GenBlk M3333 tach3333 where
  Bmat := fun k => match k with
    | 0 => Matrix.reindex (Equiv.refl _)
        (finCongr (show Text M3333 tach3333 0 = Text M3333 tach3333 1 from rfl))
        (1 : Matrix (Fin (Text M3333 tach3333 0)) (Fin (Text M3333 tach3333 0)) ℝ)
    | 1 => (!![x 1, x 1 * x 2;
               x 1 * x 3, x 1 * x 2 * x 3 + x 4;
               x 1 * x 3 * x 6 + x 1 * x 5, x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4)]
              : Matrix (Fin 3) (Fin 2) ℝ)
    | 2 => (!![x 9; x 10 * x 9] : Matrix (Fin 2) (Fin 1) ℝ)
    | (_ + 3) => 0
  Nblk := fun k => match k with
    | 1 => (!![x 7; x 8] : Matrix (Fin 2) (Fin 1) ℝ)
    | 2 => (!![x 11, x 12] : Matrix (Fin 1) (Fin 2) ℝ)
    | _ => 0
  Wblk := fun k => match k with
    | 1 => (!![x 15, x 16, x 17] : Matrix (Fin 1) (Fin 3) ℝ)
    | 2 => (!![x 18, x 19, x 20; x 21, x 22, x 23] : Matrix (Fin 2) (Fin 3) ℝ)
    | _ => 0
  Rmat := fun k => match k with
    | 1 => (!![0, 0, 0; 0, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ)
    | 2 => (!![0, 0, 0; 0, x 13, x 14] : Matrix (Fin 2) (Fin 3) ℝ)
    | _ => 0
  Rfin := fun k => match k with
    | 3 => (!![x 24, x 25, x 26] : Matrix (Fin 1) (Fin 3) ℝ)
    | _ => 0

/-! ## The rate leg (one-line via the banked decoder-agnostic `routeMCore_phiGen`) -/

/-- **The identity boundary `C 0 = 1`** for `B_det3333` (the `C0_eq_one` pattern; `c_0 = Wext 0 −
Text 1 = 0`, so `chainQ(N_0) = I`, `Bmat 0 = reindex 1`, `Rmat 0 = 0`). -/
theorem C0_eq_one_3333 (u : ℝ) :
    (chainOfMt u M3333 tach3333 (B_det3333 (fun _ => u)) hleach3333).toChain.C 0
      = (1 : Matrix (Fin (Text M3333 tach3333 0)) (Fin (Text M3333 tach3333 0)) ℝ) := by
  rw [chainOfMt_C_zero u M3333 tach3333 _ hleach3333 (by norm_num),
    show (B_det3333 (fun _ => u)).Rmat 0 = 0 from rfl, smul_zero, add_zero]
  have hBmat : (B_det3333 (fun _ => u)).Bmat 0
      = Matrix.reindex (Equiv.refl _)
          (finCongr (show Text M3333 tach3333 0 = Text M3333 tach3333 1 from rfl))
          (1 : Matrix (Fin (Text M3333 tach3333 0)) (Fin (Text M3333 tach3333 0)) ℝ) := rfl
  rw [hBmat]
  ext i j
  rw [Matrix.mul_apply,
    Finset.sum_eq_single (Fin.cast (show Text M3333 tach3333 0 = Text M3333 tach3333 1 from rfl) i)]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Matrix.one_apply_eq, one_mul]
    have hjcol : (j : Fin (Wext M3333 0)) = Fin.cast (genWidthEq M3333 tach3333 hleach3333 0 (by norm_num))
        (Fin.castAdd (Wext M3333 0 - Text M3333 tach3333 (0 + 1))
          (Fin.cast (show Text M3333 tach3333 1 = Wext M3333 0 from rfl).symm j)) := by
      apply Fin.ext; simp
    rw [hjcol, chainQ_apply_castAdd, Matrix.one_apply, Matrix.one_apply]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos (by apply Fin.ext; simpa using h), if_pos (by apply Fin.ext; simpa using h)]
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),
        if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc))]
  · intro b _ hb
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply]
    rw [show (1 : Matrix (Fin (Text M3333 tach3333 0)) (Fin (Text M3333 tach3333 0)) ℝ) i
          (Fin.cast (show Text M3333 tach3333 0 = Text M3333 tach3333 1 from rfl).symm b) = 0 from by
      rw [Matrix.one_apply, if_neg]; intro hc; apply hb; rw [hc]; apply Fin.ext; simp]
    rw [zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **`hC0` for `B_det3333`** (`C 0 · suffix 0 = suffix 0` from `C 0 = 1`). -/
theorem hC0_3333 (u : ℝ) :
    (chainOfMt u M3333 tach3333 (B_det3333 (fun _ => u)) hleach3333).toChain.C 0
        * (chainOfMt u M3333 tach3333 (B_det3333 (fun _ => u)) hleach3333).toChain.suffix 0
            (Nat.zero_le 3)
      = (chainOfMt u M3333 tach3333 (B_det3333 (fun _ => u)) hleach3333).toChain.suffix 0
          (Nat.zero_le 3) := by
  rw [C0_eq_one_3333 u]; exact Matrix.one_mul _

/-- **The `(3,3,3,3)` structured flat chart** `phiDet3333 u := phiGen u M3333 tach3333 (B_det3333 …)`. -/
noncomputable def phiDet3333 (u : ℝ) : Fin (routeMAmbient M3333) → ℝ :=
  phiGen u M3333 tach3333 (B_det3333 (fun _ => u)) hleach3333

/-- **The RATE leg (one-line, banked).** `routeMCore M3333 (phiDet3333 u) = u²·V` via the banked
decoder-agnostic `routeMCore_phiGen` at the full-rank `B_det3333`, re-checking only `hC0_3333`. The
validated Route-2a rate on the genuine 3-boundary node (drops at all 3 boundaries telescope to ONE `u`). -/
theorem routeMCore_phiDet3333 (u : ℝ) :
    routeMCore M3333 (phiDet3333 u)
      = u ^ 2 * VvalGen u M3333 tach3333 (B_det3333 (fun _ => u)) hleach3333 :=
  routeMCore_phiGen u M3333 tach3333 (B_det3333 (fun _ => u)) hleach3333 (hC0_3333 u)

/-! ## The bridge `chartParamsGen(B_det3333 x) = chartParams3333 x` — the parametric-bridge VALIDATE-SMALL

The three chain layers `A_0/A_1/A_2` (reindexed to the `M`-widths) ARE the banked explicit
`chartA3333`/`chartB3333`/`chartC3333` (sympy-verified EXACT). Each layer by the `chainA_apply_castAdd`
(kept row = `C_{k+1} − N_k·W_k`) / `chainA_apply_natAdd` (lift row = `W_k`) entry laws + the banked cast
pattern (entry `have`s at explicit `⟨_, by decide⟩` indices, `exact`ed into the `fin_cases` goal). The
recursive transitions `C_3 = u·Rfin 3`, `C_2 = Bmat 2·chainQ(N_2) + u·Rmat 2`, `C_1 = Bmat 1·chainQ(N_1)
+ u·Rmat 1` unfold by `Cgen` `dif`. -/

/-- Block values of `B_det3333` (all `rfl`). -/
theorem N1_3333 (x : Fin 27 → ℝ) :
    (B_det3333 x).Nblk 1 = (!![x 7; x 8] : Matrix (Fin (Text M3333 tach3333 2))
      (Fin (Wext M3333 1 - Text M3333 tach3333 2)) ℝ) := rfl
theorem N2_3333 (x : Fin 27 → ℝ) :
    (B_det3333 x).Nblk 2 = (!![x 11, x 12] : Matrix (Fin (Text M3333 tach3333 3))
      (Fin (Wext M3333 2 - Text M3333 tach3333 3)) ℝ) := rfl
theorem W1_3333 (x : Fin 27 → ℝ) :
    (B_det3333 x).Wblk 1 = (!![x 15, x 16, x 17] : Matrix (Fin (Wext M3333 1 - Text M3333 tach3333 2))
      (Fin (Wext M3333 2)) ℝ) := rfl
theorem W2_3333 (x : Fin 27 → ℝ) :
    (B_det3333 x).Wblk 2 = (!![x 18, x 19, x 20; x 21, x 22, x 23]
      : Matrix (Fin (Wext M3333 2 - Text M3333 tach3333 3)) (Fin (Wext M3333 3)) ℝ) := rfl
theorem B1_3333 (x : Fin 27 → ℝ) :
    (B_det3333 x).Bmat 1 = (!![x 1, x 1 * x 2; x 1 * x 3, x 1 * x 2 * x 3 + x 4;
        x 1 * x 3 * x 6 + x 1 * x 5, x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4)]
      : Matrix (Fin (Text M3333 tach3333 1)) (Fin (Text M3333 tach3333 2)) ℝ) := rfl
theorem B2_3333 (x : Fin 27 → ℝ) :
    (B_det3333 x).Bmat 2 = (!![x 9; x 10 * x 9]
      : Matrix (Fin (Text M3333 tach3333 2)) (Fin (Text M3333 tach3333 3)) ℝ) := rfl
theorem R1_3333 (x : Fin 27 → ℝ) :
    (B_det3333 x).Rmat 1 = (!![0, 0, 0; 0, 0, 0; 0, 0, 1]
      : Matrix (Fin (Text M3333 tach3333 1)) (Fin (Wext M3333 1)) ℝ) := rfl
theorem R2_3333 (x : Fin 27 → ℝ) :
    (B_det3333 x).Rmat 2 = (!![0, 0, 0; 0, x 13, x 14]
      : Matrix (Fin (Text M3333 tach3333 2)) (Fin (Wext M3333 2)) ℝ) := rfl

/-- The leaf transition `C 3 = u·Rfin 3 = u • !![x24, x25, x26]`. -/
theorem Cgen3333_leaf (x : Fin 27 → ℝ) :
    Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 3
      = (x 0) • (!![x 24, x 25, x 26]
          : Matrix (Fin (Text M3333 tach3333 3)) (Fin (Wext M3333 3)) ℝ) := by
  show Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 3 = _
  unfold Cgen; rw [dif_neg (by norm_num)]; rfl

/-- **Layer 2 of the chain equals the explicit `chartC3333`** (at the `Wext`-widths). Kept row 0 =
`C_3 − N_2·W_2`; lift rows 1,2 = `W_2`. -/
theorem Agen2_3333_eq (x : Fin 27 → ℝ) :
    Agen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 2
      = (!![x 0 * x 24 - x 11 * x 18 - x 12 * x 21, x 0 * x 25 - x 11 * x 19 - x 12 * x 22,
            x 0 * x 26 - x 11 * x 20 - x 12 * x 23;
          x 18, x 19, x 20; x 21, x 22, x 23]
          : Matrix (Fin (Wext M3333 2)) (Fin (Wext M3333 3)) ℝ) := by
  have hA : Agen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 2
      = chainA (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num))
          ((B_det3333 x).Nblk 2) ((B_det3333 x).Wblk 2)
          (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 3) := by
    unfold Agen; rw [dif_pos (by norm_num)]
  -- kept-row entry law (row 0 → castAdd block): chainA ... ⟨0,_⟩ j = (C_3 − N_2·W_2) ⟨0,_⟩ j
  have kept : ∀ j : Fin (Wext M3333 3),
      chainA (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num)) ((B_det3333 x).Nblk 2)
          ((B_det3333 x).Wblk 2) (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 3)
          (⟨0, by decide⟩ : Fin (Wext M3333 2)) j
        = (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 3
            - (B_det3333 x).Nblk 2 * (B_det3333 x).Wblk 2)
            (⟨0, by decide⟩ : Fin (Text M3333 tach3333 3)) j := by
    intro j
    conv_lhs => rw [show (⟨0, by decide⟩ : Fin (Wext M3333 2))
        = Fin.cast (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num))
            (Fin.castAdd (Wext M3333 2 - Text M3333 tach3333 3)
              (⟨0, by decide⟩ : Fin (Text M3333 tach3333 3))) from by apply Fin.ext; simp]
    rw [chainA_apply_castAdd]
  -- lift-row entry laws (rows 1,2 → natAdd block): chainA ... = W_2
  have lift : ∀ (rv : ℕ) (hr : rv < Wext M3333 2 - Text M3333 tach3333 3) (j : Fin (Wext M3333 3)),
      chainA (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num)) ((B_det3333 x).Nblk 2)
          ((B_det3333 x).Wblk 2) (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 3)
          (Fin.cast (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num))
            (Fin.natAdd (Text M3333 tach3333 3) (⟨rv, hr⟩ : Fin (Wext M3333 2 - Text M3333 tach3333 3)))) j
        = (B_det3333 x).Wblk 2 (⟨rv, hr⟩ : Fin (Wext M3333 2 - Text M3333 tach3333 3)) j := by
    intro rv hr j; rw [chainA_apply_natAdd]
  -- kept-row scalar entries (row 0, the C_3 − N_2·W_2 columns); the `show` re-types so the matrix-apply
  -- simp lemmas fire on the cast `⟨0,_⟩` index (the banked cast fix)
  have h00 : chainA (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num)) ((B_det3333 x).Nblk 2)
      ((B_det3333 x).Wblk 2) (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 3)
      (⟨0, by decide⟩ : Fin (Wext M3333 2)) (⟨0, by decide⟩ : Fin (Wext M3333 3))
        = x 0 * x 24 - x 11 * x 18 - x 12 * x 21 := by
    rw [kept, Cgen3333_leaf, N2_3333, W2_3333]
    show ((x 0 • (!![x 24, x 25, x 26] : Matrix (Fin (Text M3333 tach3333 3)) (Fin (Wext M3333 3)) ℝ))
        - (!![x 11, x 12] : Matrix (Fin (Text M3333 tach3333 3)) (Fin (Wext M3333 2 - Text M3333 tach3333 3)) ℝ)
          * (!![x 18, x 19, x 20; x 21, x 22, x 23] : Matrix (Fin (Wext M3333 2 - Text M3333 tach3333 3)) (Fin (Wext M3333 3)) ℝ))
        (⟨0, by decide⟩) (⟨0, by decide⟩) = x 0 * x 24 - x 11 * x 18 - x 12 * x 21
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
    show x 0 * x 24 - (x 11 * x 18 + x 12 * x 21) = x 0 * x 24 - x 11 * x 18 - x 12 * x 21; ring
  have h01 : chainA (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num)) ((B_det3333 x).Nblk 2)
      ((B_det3333 x).Wblk 2) (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 3)
      (⟨0, by decide⟩ : Fin (Wext M3333 2)) (⟨1, by decide⟩ : Fin (Wext M3333 3))
        = x 0 * x 25 - x 11 * x 19 - x 12 * x 22 := by
    rw [kept, Cgen3333_leaf, N2_3333, W2_3333]
    show ((x 0 • (!![x 24, x 25, x 26] : Matrix (Fin (Text M3333 tach3333 3)) (Fin (Wext M3333 3)) ℝ))
        - (!![x 11, x 12] : Matrix (Fin (Text M3333 tach3333 3)) (Fin (Wext M3333 2 - Text M3333 tach3333 3)) ℝ)
          * (!![x 18, x 19, x 20; x 21, x 22, x 23] : Matrix (Fin (Wext M3333 2 - Text M3333 tach3333 3)) (Fin (Wext M3333 3)) ℝ))
        (⟨0, by decide⟩) (⟨1, by decide⟩) = x 0 * x 25 - x 11 * x 19 - x 12 * x 22
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
    show x 0 * x 25 - (x 11 * x 19 + x 12 * x 22) = x 0 * x 25 - x 11 * x 19 - x 12 * x 22; ring
  have h02 : chainA (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num)) ((B_det3333 x).Nblk 2)
      ((B_det3333 x).Wblk 2) (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 3)
      (⟨0, by decide⟩ : Fin (Wext M3333 2)) (⟨2, by decide⟩ : Fin (Wext M3333 3))
        = x 0 * x 26 - x 11 * x 20 - x 12 * x 23 := by
    rw [kept, Cgen3333_leaf, N2_3333, W2_3333]
    show ((x 0 • (!![x 24, x 25, x 26] : Matrix (Fin (Text M3333 tach3333 3)) (Fin (Wext M3333 3)) ℝ))
        - (!![x 11, x 12] : Matrix (Fin (Text M3333 tach3333 3)) (Fin (Wext M3333 2 - Text M3333 tach3333 3)) ℝ)
          * (!![x 18, x 19, x 20; x 21, x 22, x 23] : Matrix (Fin (Wext M3333 2 - Text M3333 tach3333 3)) (Fin (Wext M3333 3)) ℝ))
        (⟨0, by decide⟩) (⟨2, by decide⟩) = x 0 * x 26 - x 11 * x 20 - x 12 * x 23
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
    show x 0 * x 26 - (x 11 * x 20 + x 12 * x 23) = x 0 * x 26 - x 11 * x 20 - x 12 * x 23; ring
  -- lift-row entries (rows 1,2 = W_2 rows 0,1)
  have h10 := lift 0 (by decide) (⟨0, by decide⟩); have h11 := lift 0 (by decide) (⟨1, by decide⟩)
  have h12 := lift 0 (by decide) (⟨2, by decide⟩)
  have h20 := lift 1 (by decide) (⟨0, by decide⟩); have h21 := lift 1 (by decide) (⟨1, by decide⟩)
  have h22 := lift 1 (by decide) (⟨2, by decide⟩)
  rw [W2_3333] at h10 h11 h12 h20 h21 h22
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h02
  · exact h10
  · exact h11
  · exact h12
  · exact h20
  · exact h21
  · exact h22

/-- The chaining row `chainQ(N_2) = !![1, x11, x12]` (1×3): kept col `[1]` then residual `[x11,x12]`. -/
theorem chainQ2_eq3333 (x : Fin 27 → ℝ) :
    chainQ (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num)) ((B_det3333 x).Nblk 2)
      = (!![1, x 11, x 12] : Matrix (Fin (Text M3333 tach3333 3)) (Fin (Wext M3333 2)) ℝ) := by
  have c0 : chainQ (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num)) ((B_det3333 x).Nblk 2)
      (⟨0, by decide⟩ : Fin (Text M3333 tach3333 3)) (⟨0, by decide⟩ : Fin (Wext M3333 2)) = 1 := by
    conv_lhs => rw [show (⟨0, by decide⟩ : Fin (Wext M3333 2))
        = Fin.cast (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num))
            (Fin.castAdd (Wext M3333 2 - Text M3333 tach3333 3) (⟨0, by decide⟩ : Fin (Text M3333 tach3333 3))) from by apply Fin.ext; simp]
    rw [chainQ_apply_castAdd]; rfl
  have c1 : chainQ (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num)) ((B_det3333 x).Nblk 2)
      (⟨0, by decide⟩ : Fin (Text M3333 tach3333 3)) (⟨1, by decide⟩ : Fin (Wext M3333 2)) = x 11 := by
    conv_lhs => rw [show (⟨1, by decide⟩ : Fin (Wext M3333 2))
        = Fin.cast (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num))
            (Fin.natAdd (Text M3333 tach3333 3) (⟨0, by decide⟩ : Fin (Wext M3333 2 - Text M3333 tach3333 3))) from by apply Fin.ext; simp]
    rw [chainQ_apply_natAdd, N2_3333]; rfl
  have c2 : chainQ (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num)) ((B_det3333 x).Nblk 2)
      (⟨0, by decide⟩ : Fin (Text M3333 tach3333 3)) (⟨2, by decide⟩ : Fin (Wext M3333 2)) = x 12 := by
    conv_lhs => rw [show (⟨2, by decide⟩ : Fin (Wext M3333 2))
        = Fin.cast (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num))
            (Fin.natAdd (Text M3333 tach3333 3) (⟨1, by decide⟩ : Fin (Wext M3333 2 - Text M3333 tach3333 3))) from by apply Fin.ext; simp]
    rw [chainQ_apply_natAdd, N2_3333]; rfl
  ext i j; fin_cases i <;> fin_cases j
  · exact c0
  · exact c1
  · exact c2

/-- The literal-`Fin` Schur product `C_2 = Bmat 2·!![1,x11,x12] + u·Rmat 2 = explicit` (2×3). -/
theorem C2_lit3333 (x : Fin 27 → ℝ) :
    (!![x 9; x 10 * x 9] : Matrix (Fin 2) (Fin 1) ℝ) * (!![1, x 11, x 12] : Matrix (Fin 1) (Fin 3) ℝ)
        + (x 0) • (!![0, 0, 0; 0, x 13, x 14] : Matrix (Fin 2) (Fin 3) ℝ)
      = (!![x 9, x 11 * x 9, x 12 * x 9;
            x 10 * x 9, x 0 * x 13 + x 10 * x 11 * x 9, x 0 * x 14 + x 10 * x 12 * x 9]
          : Matrix (Fin 2) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_one, smul_eq_mul] <;> ring

/-- **The transition `C 2 = explicit`** (`C_2 = Bmat 2·chainQ(N_2) + u·Rmat 2`). -/
theorem C2_eq3333 (x : Fin 27 → ℝ) :
    Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 2
      = (!![x 9, x 11 * x 9, x 12 * x 9;
            x 10 * x 9, x 0 * x 13 + x 10 * x 11 * x 9, x 0 * x 14 + x 10 * x 12 * x 9]
          : Matrix (Fin (Text M3333 tach3333 2)) (Fin (Wext M3333 2)) ℝ) := by
  have hC : Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 2
      = (B_det3333 x).Bmat 2 * chainQ (genWidthEq M3333 tach3333 hleach3333 2 (by norm_num))
            ((B_det3333 x).Nblk 2) + (x 0) • (B_det3333 x).Rmat 2 := by
    show Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 2 = _
    unfold Cgen; rw [dif_pos (by norm_num)]
  rw [hC, chainQ2_eq3333, B2_3333, R2_3333]
  have h2 : Text M3333 tach3333 2 = 2 := rfl
  have h3 : Text M3333 tach3333 3 = 1 := rfl
  have hw2 : Wext M3333 2 = 3 := rfl
  simpa only [h2, h3, hw2] using C2_lit3333 x

/-- **Layer 1 of the chain equals the explicit `chartB3333`** (kept rows 0,1 = `C_2 − N_1·W_1`; lift
row 2 = `W_1`). -/
theorem Agen1_3333_eq (x : Fin 27 → ℝ) :
    Agen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 1
      = (!![x 9 - x 15 * x 7, x 11 * x 9 - x 16 * x 7, x 12 * x 9 - x 17 * x 7;
            x 10 * x 9 - x 15 * x 8, x 0 * x 13 + x 10 * x 11 * x 9 - x 16 * x 8,
              x 0 * x 14 + x 10 * x 12 * x 9 - x 17 * x 8;
            x 15, x 16, x 17]
          : Matrix (Fin (Wext M3333 1)) (Fin (Wext M3333 2)) ℝ) := by
  have hA : Agen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 1
      = chainA (genWidthEq M3333 tach3333 hleach3333 1 (by norm_num))
          ((B_det3333 x).Nblk 1) ((B_det3333 x).Wblk 1)
          (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 2) := by
    unfold Agen; rw [dif_pos (by norm_num)]
  -- kept-row entry law: chainA ... ⟨rv,_⟩ j = (C_2 − N_1·W_1) ⟨rv,_⟩ j  (rows 0,1, plain Wext index)
  have ke : ∀ (rv : ℕ) (hr : rv < Text M3333 tach3333 2) (hrw : rv < Wext M3333 1)
      (jv : ℕ) (hj : jv < Wext M3333 2) (val : ℝ),
      (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 2
        - (B_det3333 x).Nblk 1 * (B_det3333 x).Wblk 1)
        (⟨rv, hr⟩ : Fin (Text M3333 tach3333 2)) (⟨jv, hj⟩ : Fin (Wext M3333 2)) = val →
      chainA (genWidthEq M3333 tach3333 hleach3333 1 (by norm_num)) ((B_det3333 x).Nblk 1)
          ((B_det3333 x).Wblk 1) (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 2)
          (⟨rv, hrw⟩ : Fin (Wext M3333 1)) (⟨jv, hj⟩ : Fin (Wext M3333 2)) = val := by
    intro rv hr hrw jv hj val hval
    conv_lhs => rw [show (⟨rv, hrw⟩ : Fin (Wext M3333 1))
        = Fin.cast (genWidthEq M3333 tach3333 hleach3333 1 (by norm_num))
            (Fin.castAdd (Wext M3333 1 - Text M3333 tach3333 2) (⟨rv, hr⟩ : Fin (Text M3333 tach3333 2)))
              from by apply Fin.ext; simp]
    rw [chainA_apply_castAdd]; exact hval
  -- lift-row entry law (row 2 = W_1 row 0)
  have lift : ∀ (rv : ℕ) (hr : rv < Wext M3333 1 - Text M3333 tach3333 2) (hrw : rv + Text M3333 tach3333 2 < Wext M3333 1)
      (j : Fin (Wext M3333 2)),
      chainA (genWidthEq M3333 tach3333 hleach3333 1 (by norm_num)) ((B_det3333 x).Nblk 1)
          ((B_det3333 x).Wblk 1) (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 2)
          (⟨rv + Text M3333 tach3333 2, hrw⟩ : Fin (Wext M3333 1)) j
        = (B_det3333 x).Wblk 1 (⟨rv, hr⟩ : Fin (Wext M3333 1 - Text M3333 tach3333 2)) j := by
    intro rv hr hrw j
    conv_lhs => rw [show (⟨rv + Text M3333 tach3333 2, hrw⟩ : Fin (Wext M3333 1))
        = Fin.cast (genWidthEq M3333 tach3333 hleach3333 1 (by norm_num))
            (Fin.natAdd (Text M3333 tach3333 2) (⟨rv, hr⟩ : Fin (Wext M3333 1 - Text M3333 tach3333 2)))
              from by apply Fin.ext; simp [Nat.add_comm]]
    rw [chainA_apply_natAdd]
  -- the kept-entry scalar closer (`show`-ground the C_2 − N_1·W_1 subtraction so apply lemmas fire)
  have keptVal : ∀ (rv : ℕ) (hr : rv < Text M3333 tach3333 2) (jv : ℕ) (hj : jv < Wext M3333 2)
      (val : ℝ),
      ((!![x 9, x 11 * x 9, x 12 * x 9;
            x 10 * x 9, x 0 * x 13 + x 10 * x 11 * x 9, x 0 * x 14 + x 10 * x 12 * x 9]
          : Matrix (Fin (Text M3333 tach3333 2)) (Fin (Wext M3333 2)) ℝ)
        - (!![x 7; x 8] : Matrix (Fin (Text M3333 tach3333 2)) (Fin (Wext M3333 1 - Text M3333 tach3333 2)) ℝ)
          * (!![x 15, x 16, x 17] : Matrix (Fin (Wext M3333 1 - Text M3333 tach3333 2)) (Fin (Wext M3333 2)) ℝ))
        (⟨rv, hr⟩) (⟨jv, hj⟩) = val →
      (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 2
        - (B_det3333 x).Nblk 1 * (B_det3333 x).Wblk 1)
        (⟨rv, hr⟩ : Fin (Text M3333 tach3333 2)) (⟨jv, hj⟩ : Fin (Wext M3333 2)) = val := by
    intro rv hr jv hj val hval; rw [C2_eq3333, N1_3333, W1_3333]; exact hval
  have e00 := ke 0 (by decide) (by decide) 0 (by decide) _ (keptVal 0 (by decide) 0 (by decide) (x 9 - x 15 * x 7)
    (by rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one]; show x 9 - x 7 * x 15 = _; ring))
  have e01 := ke 0 (by decide) (by decide) 1 (by decide) _ (keptVal 0 (by decide) 1 (by decide) (x 11 * x 9 - x 16 * x 7)
    (by rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one]; show x 11 * x 9 - x 7 * x 16 = _; ring))
  have e02 := ke 0 (by decide) (by decide) 2 (by decide) _ (keptVal 0 (by decide) 2 (by decide) (x 12 * x 9 - x 17 * x 7)
    (by rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one]; show x 12 * x 9 - x 7 * x 17 = _; ring))
  have e10 := ke 1 (by decide) (by decide) 0 (by decide) _ (keptVal 1 (by decide) 0 (by decide) (x 10 * x 9 - x 15 * x 8)
    (by rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one]; show x 10 * x 9 - x 8 * x 15 = _; ring))
  have e11 := ke 1 (by decide) (by decide) 1 (by decide) _ (keptVal 1 (by decide) 1 (by decide)
    (x 0 * x 13 + x 10 * x 11 * x 9 - x 16 * x 8)
    (by rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one];
        show x 0 * x 13 + x 10 * x 11 * x 9 - x 8 * x 16 = _; ring))
  have e12 := ke 1 (by decide) (by decide) 2 (by decide) _ (keptVal 1 (by decide) 2 (by decide)
    (x 0 * x 14 + x 10 * x 12 * x 9 - x 17 * x 8)
    (by rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one];
        show x 0 * x 14 + x 10 * x 12 * x 9 - x 8 * x 17 = _; ring))
  -- lift entries (row 2 = ⟨0 + Text2,_⟩ = W_1 row 0)
  have e20 := lift 0 (by decide) (by decide) (⟨0, by decide⟩)
  have e21 := lift 0 (by decide) (by decide) (⟨1, by decide⟩)
  have e22 := lift 0 (by decide) (by decide) (⟨2, by decide⟩)
  rw [W1_3333] at e20 e21 e22
  ext i j
  fin_cases i <;> fin_cases j
  · rw [hA]; exact e00
  · rw [hA]; exact e01
  · rw [hA]; exact e02
  · rw [hA]; exact e10
  · rw [hA]; exact e11
  · rw [hA]; exact e12
  · rw [hA]; exact e20
  · rw [hA]; exact e21
  · rw [hA]; exact e22

/-- The chaining row `chainQ(N_1) = !![1,0,x7; 0,1,x8]` (2×3): kept cols `[I_2]` then residual `[N_1]`. -/
theorem chainQ1_eq3333 (x : Fin 27 → ℝ) :
    chainQ (genWidthEq M3333 tach3333 hleach3333 1 (by norm_num)) ((B_det3333 x).Nblk 1)
      = (!![1, 0, x 7; 0, 1, x 8] : Matrix (Fin (Text M3333 tach3333 2)) (Fin (Wext M3333 1)) ℝ) := by
  have hk : ∀ (iv : ℕ) (hi : iv < Text M3333 tach3333 2) (jv : ℕ) (hj : jv < Text M3333 tach3333 2),
      chainQ (genWidthEq M3333 tach3333 hleach3333 1 (by norm_num)) ((B_det3333 x).Nblk 1)
        (⟨iv, hi⟩ : Fin (Text M3333 tach3333 2)) (⟨jv, Nat.lt_of_lt_of_le hj (by decide)⟩ : Fin (Wext M3333 1))
      = (1 : Matrix (Fin (Text M3333 tach3333 2)) (Fin (Text M3333 tach3333 2)) ℝ) ⟨iv, hi⟩ ⟨jv, hj⟩ := by
    intro iv hi jv hj
    conv_lhs => rw [show (⟨jv, Nat.lt_of_lt_of_le hj (by decide)⟩ : Fin (Wext M3333 1))
        = Fin.cast (genWidthEq M3333 tach3333 hleach3333 1 (by norm_num))
            (Fin.castAdd (Wext M3333 1 - Text M3333 tach3333 2) (⟨jv, hj⟩ : Fin (Text M3333 tach3333 2)))
              from by apply Fin.ext; simp]
    rw [chainQ_apply_castAdd]
  have hr : ∀ (iv : ℕ) (hi : iv < Text M3333 tach3333 2) (val : ℝ),
      (B_det3333 x).Nblk 1 (⟨iv, hi⟩ : Fin (Text M3333 tach3333 2)) (⟨0, by decide⟩ : Fin (Wext M3333 1 - Text M3333 tach3333 2)) = val →
      chainQ (genWidthEq M3333 tach3333 hleach3333 1 (by norm_num)) ((B_det3333 x).Nblk 1)
        (⟨iv, hi⟩ : Fin (Text M3333 tach3333 2)) (⟨2, by decide⟩ : Fin (Wext M3333 1)) = val := by
    intro iv hi val hval
    conv_lhs => rw [show (⟨2, by decide⟩ : Fin (Wext M3333 1))
        = Fin.cast (genWidthEq M3333 tach3333 hleach3333 1 (by norm_num))
            (Fin.natAdd (Text M3333 tach3333 2) (⟨0, by decide⟩ : Fin (Wext M3333 1 - Text M3333 tach3333 2)))
              from by apply Fin.ext; simp]
    rw [chainQ_apply_natAdd]; exact hval
  ext i j
  fin_cases i <;> fin_cases j
  · have := hk 0 (by decide) 0 (by decide); simpa using this
  · have := hk 0 (by decide) 1 (by decide); simpa using this
  · have := hr 0 (by decide) (x 7) (by rw [N1_3333]; rfl); simpa using this
  · have := hk 1 (by decide) 0 (by decide); simpa using this
  · have := hk 1 (by decide) 1 (by decide); simpa using this
  · have := hr 1 (by decide) (x 8) (by rw [N1_3333]; rfl); simpa using this

/-- The literal-`Fin` Schur product `C_1 = Bmat 1·!![1,0,x7;0,1,x8] + u·Rmat 1 = chartA3333` (3×3). -/
theorem C1_lit3333 (x : Fin 27 → ℝ) :
    (!![x 1, x 1 * x 2; x 1 * x 3, x 1 * x 2 * x 3 + x 4;
        x 1 * x 3 * x 6 + x 1 * x 5, x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4)]
      : Matrix (Fin 3) (Fin 2) ℝ) * (!![1, 0, x 7; 0, 1, x 8] : Matrix (Fin 2) (Fin 3) ℝ)
        + (x 0) • (!![0, 0, 0; 0, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ)
      = (!![x 1, x 1 * x 2, x 1 * x 2 * x 8 + x 1 * x 7;
            x 1 * x 3, x 1 * x 2 * x 3 + x 4, x 1 * x 3 * x 7 + x 8 * (x 1 * x 2 * x 3 + x 4);
            x 1 * x 3 * x 6 + x 1 * x 5, x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4),
              x 0 + x 7 * (x 1 * x 3 * x 6 + x 1 * x 5)
                + x 8 * (x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4))]
          : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two, smul_eq_mul] <;> ring

/-- **The transition `C 1 = chartA3333`** (`C_1 = Bmat 1·chainQ(N_1) + u·Rmat 1`). -/
theorem C1_eq3333 (x : Fin 27 → ℝ) :
    Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 1
      = (!![x 1, x 1 * x 2, x 1 * x 2 * x 8 + x 1 * x 7;
            x 1 * x 3, x 1 * x 2 * x 3 + x 4, x 1 * x 3 * x 7 + x 8 * (x 1 * x 2 * x 3 + x 4);
            x 1 * x 3 * x 6 + x 1 * x 5, x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4),
              x 0 + x 7 * (x 1 * x 3 * x 6 + x 1 * x 5)
                + x 8 * (x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4))]
          : Matrix (Fin (Text M3333 tach3333 1)) (Fin (Wext M3333 1)) ℝ) := by
  have hC : Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 1
      = (B_det3333 x).Bmat 1 * chainQ (genWidthEq M3333 tach3333 hleach3333 1 (by norm_num))
            ((B_det3333 x).Nblk 1) + (x 0) • (B_det3333 x).Rmat 1 := by
    show Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 1 = _
    unfold Cgen; rw [dif_pos (by norm_num)]
  rw [hC, chainQ1_eq3333, B1_3333, R1_3333]
  have h1 : Text M3333 tach3333 1 = 3 := rfl
  have h2 : Text M3333 tach3333 2 = 2 := rfl
  have hw1 : Wext M3333 1 = 3 := rfl
  simpa only [h1, h2, hw1] using C1_lit3333 x

/-- **Layer 0 of the chain equals the explicit `chartA3333`** (`c_0 = 0`, all rows `castAdd`, so
`Agen 0 = C 1 − N_0·W_0 = C 1` = `chartA3333`). -/
theorem Agen0_3333_eq (x : Fin 27 → ℝ) :
    Agen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 0
      = (!![x 1, x 1 * x 2, x 1 * x 2 * x 8 + x 1 * x 7;
            x 1 * x 3, x 1 * x 2 * x 3 + x 4, x 1 * x 3 * x 7 + x 8 * (x 1 * x 2 * x 3 + x 4);
            x 1 * x 3 * x 6 + x 1 * x 5, x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4),
              x 0 + x 7 * (x 1 * x 3 * x 6 + x 1 * x 5)
                + x 8 * (x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4))]
          : Matrix (Fin (Wext M3333 0)) (Fin (Wext M3333 1)) ℝ) := by
  have hA : Agen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 0
      = chainA (genWidthEq M3333 tach3333 hleach3333 0 (by norm_num))
          ((B_det3333 x).Nblk 0) ((B_det3333 x).Wblk 0)
          (Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 1) := by
    unfold Agen; rw [dif_pos (by norm_num)]
  have hN0W0 : (B_det3333 x).Nblk 0 * (B_det3333 x).Wblk 0 = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    exact (k.cast (show Wext M3333 0 - Text M3333 tach3333 1 = 0 from rfl)).elim0
  -- every row is castAdd (c_0 = 0): Agen 0 ⟨rv,_⟩ j = C_1 ⟨rv,_⟩ j
  have e : ∀ (rv : ℕ) (hrt : rv < Text M3333 tach3333 1) (hrw : rv < Wext M3333 0) (j : Fin (Wext M3333 1)),
      Agen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 0 (⟨rv, hrw⟩ : Fin (Wext M3333 0)) j
        = Cgen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 1 (⟨rv, hrt⟩ : Fin (Text M3333 tach3333 1)) j := by
    intro rv hrt hrw j
    rw [hA]
    conv_lhs => rw [show (⟨rv, hrw⟩ : Fin (Wext M3333 0))
        = Fin.cast (genWidthEq M3333 tach3333 hleach3333 0 (by norm_num))
            (Fin.castAdd (Wext M3333 0 - Text M3333 tach3333 1) (⟨rv, hrt⟩ : Fin (Text M3333 tach3333 1)))
              from by apply Fin.ext; simp]
    rw [chainA_apply_castAdd, hN0W0, Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  ext i j
  fin_cases i <;>
    (rw [e _ (by decide) (by decide), C1_eq3333]; rfl)


/-! ## The bridge `chartParamsGen(B_det3333 x) = chartParams3333 x` — the VALIDATE-SMALL headline -/

/-- **The bridge** `chartParamsGen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 = chartParams3333 x` —
the chain's three layers (`Agen 0/1/2`), reindexed to the `M`-widths, ARE the banked explicit chart
matrices `chartA3333`/`chartB3333`/`chartC3333`. The width-parametric funext template: per-layer
`Agen{0,1,2}_3333_eq` + the `finCongr` (`rfl`-width) reindex collapse (`Fin.cast_eq_self`). The genuine
3-boundary validate-small for the ∀M parametric bridge (`certificate-genM-det.md`, ROUTE (i)). -/
theorem chartParamsGen_eq_chartParams3333 (x : Fin 27 → ℝ) :
    chartParamsGen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 = chartParams3333 x := by
  funext s
  fin_cases s
  · show Matrix.reindex _ _ (Agen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 0) = chartA3333 x
    rw [Agen0_3333_eq]; ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply,
      Fin.cast_eq_self]
    rfl
  · show Matrix.reindex _ _ (Agen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 1) = chartB3333 x
    rw [Agen1_3333_eq]; ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply,
      Fin.cast_eq_self]
    rfl
  · show Matrix.reindex _ _ (Agen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 2) = chartC3333 x
    rw [Agen2_3333_eq]; ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply,
      Fin.cast_eq_self]
    rfl


/-! ## ROUTE-2a ↔ the banked `phi3333` chart: the bridge transfers the banked atom -/

open MeasureTheory in
/-- **The ROUTE-2a chart EQUALS the banked hand-built `phi3333`** — `phiGen (x 0) M3333 tach3333
(B_det3333 x) hleach3333 = phi3333 x`, via the bridge (`chartParamsGen = chartParams3333`) under
`paramsEquivFlat`. So the genuine engine chart and the explicit chart are the SAME map. -/
theorem phiGen_B_det3333_eq_phi3333 (x : Fin 27 → ℝ) :
    phiGen (x 0) M3333 tach3333 (B_det3333 x) hleach3333 = phi3333 x := by
  rw [phiGen, chartParamsGen_eq_chartParams3333, phi3333]

open MeasureTheory in
/-- **`routeMCore_box_diverges_achiever` for `M = (3,3,3,3)` via ROUTE 2a** — the achiever box-divergence
atom at the genuine 3-boundary node, reached through the general `chainOfMt`/`GenBlk` engine (the
full-rank `B_det3333` + the parametric bridge to the explicit chart). Since the ROUTE-2a chart equals
the banked `phi3333` (`phiGen_B_det3333_eq_phi3333`), this IS the banked
`routeMCore_box_diverges_achiever_3333` — restated as the ROUTE-2a deliverable (det `|u0|⁵·|u1|⁴·|u4|²·
|u9|³` matches the banked `RouteM3333` values, the regression gate). -/
theorem routeMCore_box_diverges_achiever_3333_route2a (c' : NNReal)
    (hc' : (minAdm M3333 : ENNReal) / 2 ≤ (c' : ENNReal)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ y in cubeBox (routeMAmbient M3333) ε,
      ENNReal.ofReal (|routeMCore M3333 y| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_achiever_3333 c' hc' ε hε

end DLNFibre.DLN.RLCT
