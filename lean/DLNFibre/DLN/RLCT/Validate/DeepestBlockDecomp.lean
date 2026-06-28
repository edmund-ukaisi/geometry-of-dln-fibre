import DLNFibre.DLN.RLCT.Validate.DeepestSchurComparability
import DLNFibre.DLN.RLCT.Validate.DeepestTelescoping

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestBlockDecomp` — the h1 block decomposition (network-free)

The producer's folded germ charge (`DeepestGaugeConstruction`, `framedParams_split_eq_frame_raw`) uses
the Schur factorization `hR : Rcore = S0·(1 − K)·S1` (h1) of the global Schur complement. This module
supplies that `hR`; it feeds the intermediate `(★)` (`schur_gap_le_coreRelative`) toward the folded
charge `(♦)` (`DeepestGermCharge`).

This module supplies the **network-free matrix-algebra core of h1**: a product of two matrices, each
reindexed into `r ⊕ (· − r)` block shape by a chosen equiv, has its reindexed product equal to the
`fromBlocks` product of the two factors' blocks — the **shared-middle cancel** (`submatrix_mul_equiv`)
plus `fromBlocks_multiply`. Composed with the banked two-layer LDU `schur_product_ldu`
(`DeepestSchurComparability`), this gives the Schur-complement factorization `hR` for the reindexed
two-grouped product.

**Scope note (general L vs L = 2).** `schur_product_ldu` is a TWO-factor identity. For a general-L
network the layer product `prod H A` has `L` factors; one groups them as `(first L−1)·(last)` via the
banked `prodAux_succ`, so this block-decomposition lemma applies with `G0 = first L−1 grouped product`,
`G1 = last layer`. The h1 obligation `hR` then holds for any L. (The companion h2 obligation
`coreΦ = frobSq (S0·S1)` does NOT reduce so cleanly: it needs the grouped Schur core of the first L−1
layers to equal the per-layer-core product — a recursive Schur-core identity, trivial only at L = 2.
That recursion is the genuine general-L residual; this module is unaffected by it.)

Design cert: `expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/h1-blockdecomp-cert.md`.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

/-- **The reindexed-product split** (the shared-middle cancel). For `G0 : Matrix (Fin a) (Fin c) ℝ` and
`G1 : Matrix (Fin c) (Fin b) ℝ`, with the row/middle/column splits `eR`, `eMid`, `eC` into `r ⊕ (· − r)`
shape, the reindexed product `reindex eR eC (G0·G1)` equals the block product `(reindex eR eMid G0)·
(reindex eMid eC G1)`. Pure `submatrix_mul_equiv` (the middle equiv cancels). -/
theorem reindex_mul_split {a b c r : ℕ}
    (eR : Fin a ≃ Fin r ⊕ Fin (a - r)) (eMid : Fin c ≃ Fin r ⊕ Fin (c - r))
    (eC : Fin b ≃ Fin r ⊕ Fin (b - r))
    (G0 : Matrix (Fin a) (Fin c) ℝ) (G1 : Matrix (Fin c) (Fin b) ℝ) :
    Matrix.reindex eR eC (G0 * G1)
      = Matrix.reindex eR eMid G0 * Matrix.reindex eMid eC G1 := by
  -- `reindex e₁ e₂ M = M.submatrix e₁.symm e₂.symm`; the middle `eMid.symm` cancels via
  -- `submatrix_mul_equiv` (its `e₂ : o ≃ n` argument).
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv G0 G1 eR.symm eMid.symm eC.symm]

/-- **The reindexed product as a `fromBlocks` product** (the per-grouping block reads). With the split
`reindex eR eC (G0·G1) = (reindex eR eMid G0)·(reindex eMid eC G1)` and each factor written as
`fromBlocks` of its own four blocks, the reindexed product is the `fromBlocks_multiply` of the two block
matrices. -/
theorem reindex_mul_fromBlocks {a b c r : ℕ}
    (eR : Fin a ≃ Fin r ⊕ Fin (a - r)) (eMid : Fin c ≃ Fin r ⊕ Fin (c - r))
    (eC : Fin b ≃ Fin r ⊕ Fin (b - r))
    (G0 : Matrix (Fin a) (Fin c) ℝ) (G1 : Matrix (Fin c) (Fin b) ℝ) :
    Matrix.reindex eR eC (G0 * G1)
      = Matrix.fromBlocks
          ((Matrix.reindex eR eMid G0).toBlocks₁₁ * (Matrix.reindex eMid eC G1).toBlocks₁₁
            + (Matrix.reindex eR eMid G0).toBlocks₁₂ * (Matrix.reindex eMid eC G1).toBlocks₂₁)
          ((Matrix.reindex eR eMid G0).toBlocks₁₁ * (Matrix.reindex eMid eC G1).toBlocks₁₂
            + (Matrix.reindex eR eMid G0).toBlocks₁₂ * (Matrix.reindex eMid eC G1).toBlocks₂₂)
          ((Matrix.reindex eR eMid G0).toBlocks₂₁ * (Matrix.reindex eMid eC G1).toBlocks₁₁
            + (Matrix.reindex eR eMid G0).toBlocks₂₂ * (Matrix.reindex eMid eC G1).toBlocks₂₁)
          ((Matrix.reindex eR eMid G0).toBlocks₂₁ * (Matrix.reindex eMid eC G1).toBlocks₁₂
            + (Matrix.reindex eR eMid G0).toBlocks₂₂ * (Matrix.reindex eMid eC G1).toBlocks₂₂) := by
  rw [reindex_mul_split eR eMid eC G0 G1]
  -- Each factor `= fromBlocks of its toBlocks` (`fromBlocks_toBlocks`), then `fromBlocks_multiply`.
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex eR eMid G0),
    ← Matrix.fromBlocks_toBlocks (Matrix.reindex eMid eC G1)]
  rw [Matrix.fromBlocks_multiply]

/-- **h1 — the Schur factorization of a reindexed two-factor product** (the `hR` the germ-charge bridge
consumes). Writing the `r ⊕ (· − r)` blocks of the two reindexed factors as `A_s Y_s Z_s T_s`, the
`(1,1)`-Schur complement of the reindexed product `reindex eR eC (G0·G1)` over its `(1,1)`-block
`A0·A1 + Y0·Z1` equals `(T0 − Z0·A0⁻¹·Y0)·(1 − Z1·P⁻¹·Y0)·(T1 − Z1·A1⁻¹·Y1)` — the middle-factor LDU
form of the per-factor Schur cores. Stated with the nonsingular inverse `(·)⁻¹` (instance-free, matching
the producer's `(Mw.toBlocks₁₁ + 1)⁻¹` spelling); the pivots `A0`, `A1` and the product pivot
`P = A0·A1 + Y0·Z1 = (reindex (G0·G1)).toBlocks₁₁` are invertible. This is `reindex_mul_fromBlocks` to
read the product's blocks, `Matrix.toBlocks_fromBlocks*` to extract them, then the banked
`schur_product_ldu` with `⅟` converted to `(·)⁻¹` (`invOf_eq_nonsing_inv`). -/
theorem reindex_mul_schur_factor {a b c r : ℕ}
    (eR : Fin a ≃ Fin r ⊕ Fin (a - r)) (eMid : Fin c ≃ Fin r ⊕ Fin (c - r))
    (eC : Fin b ≃ Fin r ⊕ Fin (b - r))
    (G0 : Matrix (Fin a) (Fin c) ℝ) (G1 : Matrix (Fin c) (Fin b) ℝ)
    [Invertible (Matrix.reindex eR eMid G0).toBlocks₁₁]
    [Invertible (Matrix.reindex eMid eC G1).toBlocks₁₁]
    [Invertible ((Matrix.reindex eR eC (G0 * G1)).toBlocks₁₁)] :
    (Matrix.reindex eR eC (G0 * G1)).toBlocks₂₂
        - (Matrix.reindex eR eC (G0 * G1)).toBlocks₂₁
          * ((Matrix.reindex eR eC (G0 * G1)).toBlocks₁₁)⁻¹
          * (Matrix.reindex eR eC (G0 * G1)).toBlocks₁₂
      = ((Matrix.reindex eR eMid G0).toBlocks₂₂
            - (Matrix.reindex eR eMid G0).toBlocks₂₁ * ((Matrix.reindex eR eMid G0).toBlocks₁₁)⁻¹
              * (Matrix.reindex eR eMid G0).toBlocks₁₂)
          * (1 - (Matrix.reindex eMid eC G1).toBlocks₂₁
              * ((Matrix.reindex eR eC (G0 * G1)).toBlocks₁₁)⁻¹
              * (Matrix.reindex eR eMid G0).toBlocks₁₂)
          * ((Matrix.reindex eMid eC G1).toBlocks₂₂
            - (Matrix.reindex eMid eC G1).toBlocks₂₁ * ((Matrix.reindex eMid eC G1).toBlocks₁₁)⁻¹
              * (Matrix.reindex eMid eC G1).toBlocks₁₂) := by
  -- Abbreviate the eight per-factor blocks.
  set A0 := (Matrix.reindex eR eMid G0).toBlocks₁₁ with hA0
  set Y0 := (Matrix.reindex eR eMid G0).toBlocks₁₂ with hY0
  set Z0 := (Matrix.reindex eR eMid G0).toBlocks₂₁ with hZ0
  set T0 := (Matrix.reindex eR eMid G0).toBlocks₂₂ with hT0
  set A1 := (Matrix.reindex eMid eC G1).toBlocks₁₁ with hA1
  set Y1 := (Matrix.reindex eMid eC G1).toBlocks₁₂ with hY1
  set Z1 := (Matrix.reindex eMid eC G1).toBlocks₂₁ with hZ1
  set T1 := (Matrix.reindex eMid eC G1).toBlocks₂₂ with hT1
  -- The product's blocks via `reindex_mul_fromBlocks`; extract them with `toBlocks_fromBlocks*`.
  have hprod := reindex_mul_fromBlocks eR eMid eC G0 G1
  rw [← hA0, ← hY0, ← hZ0, ← hT0, ← hA1, ← hY1, ← hZ1, ← hT1] at hprod
  have h11 : (Matrix.reindex eR eC (G0 * G1)).toBlocks₁₁ = A0 * A1 + Y0 * Z1 := by
    rw [hprod, Matrix.toBlocks_fromBlocks₁₁]
  have h12 : (Matrix.reindex eR eC (G0 * G1)).toBlocks₁₂ = A0 * Y1 + Y0 * T1 := by
    rw [hprod, Matrix.toBlocks_fromBlocks₁₂]
  have h21 : (Matrix.reindex eR eC (G0 * G1)).toBlocks₂₁ = Z0 * A1 + T0 * Z1 := by
    rw [hprod, Matrix.toBlocks_fromBlocks₂₁]
  have h22 : (Matrix.reindex eR eC (G0 * G1)).toBlocks₂₂ = Z0 * Y1 + T0 * T1 := by
    rw [hprod, Matrix.toBlocks_fromBlocks₂₂]
  -- Rewrite the product blocks (`(·)⁻¹` is instance-free, so no motive obstruction).
  rw [h11, h12, h21, h22]
  -- The product-pivot `Invertible` instance, transported to `A0·A1+Y0·Z1` (same matrix).
  letI hPinst : Invertible (A0 * A1 + Y0 * Z1) := h11 ▸ ‹Invertible _›
  -- Convert every `(·)⁻¹` to `⅟(·)` (instance-clean: `invOf_eq_nonsing_inv`) to land on the banked LDU.
  rw [← invOf_eq_nonsing_inv (A := A0), ← invOf_eq_nonsing_inv (A := A1),
    ← invOf_eq_nonsing_inv (A := A0 * A1 + Y0 * Z1)]
  exact schur_product_ldu A0 A1 Y0 Y1 Z0 Z1 T0 T1

/-- **The two-grouping of a layer product** (the h1 reduction to two block factors, ANY `L = m+1`). The
full layer product `prod H A` factors as `(prodAux H A m) · (last layer, recast)` — the running product
of the first `m` layers times the last layer — via a single `prodAux_succ` fold. This is the `G0·G1`
form `reindex_mul_schur_factor` consumes (`G0 = prodAux m` the first-`m` grouped product, `G1 = A_m` the
last layer); it holds for every `L ≥ 1`, so the h1 Schur factorization is general-`L` (only the h2
core-match specializes to `L = 2`). -/
theorem prod_eq_prodAux_mul_last {m : ℕ} (H : Fin (m + 1 + 1) → ℕ) (A : Params (L := m + 1) H)
    (e1 : H (⟨m, Nat.lt_of_succ_lt (Nat.lt_succ_self (m + 1))⟩ : Fin (m + 1 + 1))
        = H ((⟨m, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (m + 1))⟩ : Fin (m + 1)).castSucc))
    (e2 : H (⟨m + 1, Nat.lt_succ_self (m + 1)⟩ : Fin (m + 1 + 1))
        = H ((⟨m, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (m + 1))⟩ : Fin (m + 1)).succ)) :
    prod H A
      = (prodAux H A m (Nat.lt_of_succ_lt (Nat.lt_succ_self (m + 1))))
        * (Matrix.reindex (finCongr e1.symm) (finCongr e2.symm)
            (A (⟨m, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (m + 1))⟩ : Fin (m + 1)))) :=
  prodAux_succ H A m (Nat.lt_succ_self (m + 1)) e1 e2

/-- **The corner-split Schur bridge** (the producer's `Rcore`-shape ↔ the framed-product Schur). The
producer's global Schur complement is taken over `Mw := reindex(P0·(prod − B)·QL)` with the pivot
`(Mw.toBlocks₁₁ + 1)⁻¹` (the `+1` from the corner). When the framed reindexed product splits as
`M̂ = fromBlocks 1 0 0 0 + Mw` (the banked `hRegBlocks`), the corner adds `1` to ONLY the `(1,1)` block,
so the producer's `Rcore` over `Mw` is exactly the Schur complement of `M̂` over its own `(1,1)` block:
`Mw₂₂ − Mw₂₁·(Mw₁₁+1)⁻¹·Mw₁₂ = M̂₂₂ − M̂₂₁·(M̂₁₁)⁻¹·M̂₁₂`. Pure `toBlocks`-of-`fromBlocks`-sum
bookkeeping (the same reads the `hbexact` energy identity uses), so the h1 Schur factorization on `M̂`
(`reindex_mul_schur_factor`) transfers to the producer's `Rcore`. -/
theorem rcore_eq_schur_of_corner_split {a b r : ℕ}
    (Mw Mhat : Matrix (Fin a) (Fin b) ℝ)
    (eR : Fin a ≃ Fin r ⊕ Fin (a - r)) (eC : Fin b ≃ Fin r ⊕ Fin (b - r))
    (hsplit : Matrix.reindex eR eC Mhat
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + Matrix.reindex eR eC Mw) :
    (Matrix.reindex eR eC Mw).toBlocks₂₂
        - (Matrix.reindex eR eC Mw).toBlocks₂₁
          * ((Matrix.reindex eR eC Mw).toBlocks₁₁ + 1)⁻¹
          * (Matrix.reindex eR eC Mw).toBlocks₁₂
      = (Matrix.reindex eR eC Mhat).toBlocks₂₂
        - (Matrix.reindex eR eC Mhat).toBlocks₂₁
          * ((Matrix.reindex eR eC Mhat).toBlocks₁₁)⁻¹
          * (Matrix.reindex eR eC Mhat).toBlocks₁₂ := by
  -- Each `M̂` block reads off the corner-sum: `M̂₁₁ = Mw₁₁ + 1`, the off/`(2,2)` blocks = `Mw`'s.
  rw [hsplit]
  have h11 : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
        + Matrix.reindex eR eC Mw).toBlocks₁₁
      = (Matrix.reindex eR eC Mw).toBlocks₁₁ + 1 := by
    funext i j
    simp only [Matrix.toBlocks₁₁, Matrix.add_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
    split <;> ring
  have h12 : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
        + Matrix.reindex eR eC Mw).toBlocks₁₂
      = (Matrix.reindex eR eC Mw).toBlocks₁₂ := by
    funext i j
    simp only [Matrix.toBlocks₁₂, Matrix.add_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_add]
  have h21 : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
        + Matrix.reindex eR eC Mw).toBlocks₂₁
      = (Matrix.reindex eR eC Mw).toBlocks₂₁ := by
    funext i j
    simp only [Matrix.toBlocks₂₁, Matrix.add_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_add]
  have h22 : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
        + Matrix.reindex eR eC Mw).toBlocks₂₂
      = (Matrix.reindex eR eC Mw).toBlocks₂₂ := by
    funext i j
    simp only [Matrix.toBlocks₂₂, Matrix.add_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_add]
  rw [h11, h12, h21, h22]

/-- **h1's `hR`, producer-spelling** (the corner-split + two-factor Schur factorization, combined). The
producer's global Schur complement over `Mw := P0·(prod − B)·QL` with pivot `(Mw₁₁ + 1)⁻¹` equals the
two-layer LDU form `Ŝ0·(1 − K̂)·Ŝ1` of the per-factor Schur cores, GIVEN:
* the corner split `reindex eR eC (Mhat) = fromBlocks 1 0 0 0 + reindex eR eC Mw` (the banked
  `hRegBlocks`, with `Mhat := prod (F w)` the framed reindexed product);
* the two-factor grouping `Mhat = G0 * G1` (the banked `prod_eq_prodAux_mul_last` at `L = 2`);
* the three pivot `Invertible` instances (`G0`/`G1` per-factor `(1,1)` blocks and the product pivot
  `(reindex eR eC (G0*G1)).toBlocks₁₁ = M̂₁₁ = Mw₁₁ + 1`, the producer's S5a unit).
`rcore_eq_schur_of_corner_split` (corner ⟹ `Rcore = Schur M̂`) then `reindex_mul_schur_factor`
(`Schur (reindex (G0*G1)) = Ŝ0·(1 − K̂)·Ŝ1`). Frame-agnostic: the cores `Ŝ_s` are whatever the LDU
reads off `G0, G1`'s blocks (framed in the producer). -/
theorem rcore_schur_factor_of_corner_split {a b c r : ℕ}
    (Mw Mhat : Matrix (Fin a) (Fin b) ℝ)
    (eR : Fin a ≃ Fin r ⊕ Fin (a - r)) (eMid : Fin c ≃ Fin r ⊕ Fin (c - r))
    (eC : Fin b ≃ Fin r ⊕ Fin (b - r))
    (G0 : Matrix (Fin a) (Fin c) ℝ) (G1 : Matrix (Fin c) (Fin b) ℝ)
    (hGG : Mhat = G0 * G1)
    (hsplit : Matrix.reindex eR eC Mhat
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + Matrix.reindex eR eC Mw)
    [Invertible (Matrix.reindex eR eMid G0).toBlocks₁₁]
    [Invertible (Matrix.reindex eMid eC G1).toBlocks₁₁]
    [Invertible ((Matrix.reindex eR eC (G0 * G1)).toBlocks₁₁)] :
    (Matrix.reindex eR eC Mw).toBlocks₂₂
        - (Matrix.reindex eR eC Mw).toBlocks₂₁
          * ((Matrix.reindex eR eC Mw).toBlocks₁₁ + 1)⁻¹
          * (Matrix.reindex eR eC Mw).toBlocks₁₂
      = ((Matrix.reindex eR eMid G0).toBlocks₂₂
            - (Matrix.reindex eR eMid G0).toBlocks₂₁ * ((Matrix.reindex eR eMid G0).toBlocks₁₁)⁻¹
              * (Matrix.reindex eR eMid G0).toBlocks₁₂)
          * (1 - (Matrix.reindex eMid eC G1).toBlocks₂₁
              * ((Matrix.reindex eR eC (G0 * G1)).toBlocks₁₁)⁻¹
              * (Matrix.reindex eR eMid G0).toBlocks₁₂)
          * ((Matrix.reindex eMid eC G1).toBlocks₂₂
            - (Matrix.reindex eMid eC G1).toBlocks₂₁ * ((Matrix.reindex eMid eC G1).toBlocks₁₁)⁻¹
              * (Matrix.reindex eMid eC G1).toBlocks₁₂) := by
  -- Step 1: producer's `Rcore` over `Mw` = Schur of `M̂` over its own `(1,1)` block.
  rw [rcore_eq_schur_of_corner_split Mw Mhat eR eC hsplit, hGG]
  -- Step 2: Schur of `reindex (G0*G1)` = the two-layer LDU form (`reindex_mul_schur_factor`).
  exact reindex_mul_schur_factor eR eMid eC G0 G1

/-- **Frame-transform of the `(1,1)`-Schur complement** (the network-free L = 2 endpoint-frame piece).
For a block-LOWER left frame `P = fromBlocks a 0 c D_P`, an arbitrary middle `M = fromBlocks A B C D`,
and a block-UPPER right frame `Q = fromBlocks e f 0 D_Q` (all on the `r ⊕ rest` split, with `a, A, e`
the `r×r` corners), the `(2,2)`-Schur complement of the framed product `P·M·Q` over its `(1,1)` block
is `D_P · Schur₂₂(M) · D_Q`: the off-diagonal/top-left frame blocks `a, e, c, f` fully cancel through
the inverse `(a·A·e)⁻¹ = ⅟e·⅟A·⅟a`, leaving only the bottom-right `D_P, D_Q`. Stated with `⅟` (the
caller instantiates `Invertible` from the units); `a, A, e` invertible are the only conditions. -/
theorem schur_frame_transform {r s t : Type*}
    [Fintype r] [DecidableEq r] [Fintype s] [Fintype t]
    (a : Matrix r r ℝ) (c : Matrix s r ℝ) (DP : Matrix s s ℝ)
    (A : Matrix r r ℝ) (B : Matrix r t ℝ) (C : Matrix s r ℝ) (D : Matrix s t ℝ)
    (e : Matrix r r ℝ) (f : Matrix r t ℝ) (DQ : Matrix t t ℝ)
    [Invertible a] [Invertible A] [Invertible e] :
    (Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A B C D * Matrix.fromBlocks e f 0 DQ).toBlocks₂₂
        - (Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A B C D
              * Matrix.fromBlocks e f 0 DQ).toBlocks₂₁
          * ((Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A B C D
              * Matrix.fromBlocks e f 0 DQ).toBlocks₁₁)⁻¹
          * (Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A B C D
              * Matrix.fromBlocks e f 0 DQ).toBlocks₁₂
      = DP * (D - C * A⁻¹ * B) * DQ := by
  -- Compute the framed product's blocks. `P·M = fromBlocks (aA) (aB) (cA+DP·C) (cB+DP·D)`.
  have hPM : Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A B C D
      = Matrix.fromBlocks (a * A) (a * B) (c * A + DP * C) (c * B + DP * D) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, add_zero]
  -- `(P·M)·Q = fromBlocks (aAe) (aAf+aB·DQ) ((cA+DP·C)e) ((cA+DP·C)f+(cB+DP·D)DQ)`.
  have hN : Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A B C D * Matrix.fromBlocks e f 0 DQ
      = Matrix.fromBlocks (a * A * e) (a * A * f + a * B * DQ)
          ((c * A + DP * C) * e) ((c * A + DP * C) * f + (c * B + DP * D) * DQ) := by
    rw [hPM, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, Matrix.mul_add]
  rw [hN, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  -- The `(1,1)` inverse `(a·A·e)⁻¹ = ⅟e·⅟A·⅟a`; pull `⅟`-forms in for the cancel.
  haveI : Invertible (a * A) := invertibleMul a A
  haveI : Invertible (a * A * e) := invertibleMul (a * A) e
  rw [← invOf_eq_nonsing_inv (a * A * e), ← invOf_eq_nonsing_inv A]
  rw [show ⅟(a * A * e) = ⅟e * ⅟A * ⅟a by rw [invOf_mul (a * A) e, invOf_mul a A,
    Matrix.mul_assoc]]
  -- Fully right-associate, distribute, then run the two-sided RECTANGULAR `⅟`-cancels to fixpoint
  -- (`Matrix.{invOf,mul}_invOf_cancel_left` are the heterogeneous `r×r · r×t` forms).
  simp only [Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_invOf_cancel_left, Matrix.invOf_mul_cancel_left]
  abel

end DLNFibre.DLN.RLCT
