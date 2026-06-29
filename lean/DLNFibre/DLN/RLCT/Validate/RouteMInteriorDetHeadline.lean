import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDet
import DLNFibre.DLN.RLCT.Validate.RouteMSchurFrameDet

/-!
# `RouteMInteriorDetHeadline` — the R1-LOWER interior-det HEADLINE (uniform per-boundary factorization)

The interior Jacobian determinant of the achiever chart factorizes uniformly in the width tuple `M` as

  `|det Dφ_M| = |u_p|^{minAdm−1} · ∏_s ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)} )`

(tasks #77/#90). This module banks the **det-assembly step (b-3)** of the verdict-green-lit
det_comp / block-triangular route (`item3-route-b-buildspec.md`, the
`perpiece-factorization-answer.md` witness): the global Jacobian `DFrame_M`, graded by the layer
`bLayer` (b-0 banked: `Agen_genBlkFlatStruct_reads_le` ⟹ one-sided dependency ⟹
`DFrame_M.BlockTriangular`), has its determinant equal to the product of its diagonal-block
determinants (`Matrix.BlockTriangular.det`), the nearest-neighbor shear coupling landing strictly
off-diagonal (det-1, det-irrelevant). The diagonal block at the radial grade contributes
`|u_p|^{minAdm−1}` (`radial_abs_det_minAdm`); the diagonal block at boundary `s` contributes the
Schur-frame × LDU-core value `|det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)}`
(`schurFrame_abs_det` × `lduCoreDeriv_abs_det`).

**This is the b-3 ASSEMBLY, stated network-free over the grading.** The genuinely-new content proved
here, sorry-free, is (i) the abs-form of `Matrix.BlockTriangular.det` and (ii) the **regrouping** of
the per-grade block-det product `∏_{a ∈ image g}` into the per-boundary headline form
`radial · ∏_{s : Fin L}`. The hypotheses fenced as the (separately-gated, NON-refuted) Frame_M
obligations are: the block-triangularity `hbt` (= the b-0 off-block-vanishing transported to the fused
frame `DFrame_M` — the long-pole construction) and the per-block-det identifications (= the Schur/LDU
engine values at each diagonal block). It does NOT route through the Codex-REFUTED
`composeFold fs = φ` prefix-threading (genm-mapeq @d7e75c8d); the det is taken DIRECTLY off the fused
frame via `BlockTriangular.det`.

* `blockTri_abs_det` — `|DFrame.det| = ∏_{a ∈ image g} |（toSquareBlock g a).det|`
  (the abs form of `Matrix.BlockTriangular.det`).
* `blockTri_headline_regroup` — the regrouping into `R · ∏_{s : Fin L} B s` for a `{0} ∪ {s+1}`-graded
  frame (the radial-grade-0 + boundary-grades layout).
* `interiorDet_headline_of_blockTri` — the HEADLINE: `|DFrame.det| = |u_p|^{minAdm−1} · ∏_s
  (|det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)})`, given the block-triangularity + the
  radial/per-boundary block-det identifications (each discharged by `radial_abs_det_minAdm` /
  `schurFrame_abs_det` × `lduCoreDeriv_abs_det`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (determinant + finite products; no analysis, no S2).
-/

open scoped BigOperators
open Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The abs-form block-triangular determinant (the b-3 spine) -/

/-- **Abs `BlockTriangular.det`**: for a frame `DFrame` block-triangular under a grading `g`, its
determinant's absolute value is the product of the diagonal-block determinants' absolute values. The
det-assembly spine: the off-diagonal coupling (the det-1 nearest-neighbor shear) is discarded by
`Matrix.BlockTriangular.det`. -/
theorem blockTri_abs_det {N : ℕ} (DFrame : Matrix (Fin N) (Fin N) ℝ) (g : Fin N → ℕ)
    (hbt : DFrame.BlockTriangular g) :
    |DFrame.det| = ∏ a ∈ Finset.univ.image g, |(DFrame.toSquareBlock g a).det| := by
  rw [hbt.det, Finset.abs_prod]

/-- **Singleton-block determinant.** When the grade `a` is hit by exactly one index `i0`, the diagonal
block `toSquareBlock g a` is `1×1` and its determinant is the single diagonal entry `DFrame i0 i0`.
The reusable bridge from a per-layer diagonal block to its scalar det (the b-2/b-3 per-block read for a
layer carrying one coordinate; the multi-coordinate layers use `det_submatrix_equiv_self` instead, as in
`Frame3333Deriv_det`). -/
theorem det_toSquareBlock_singleton {N : ℕ} (DFrame : Matrix (Fin N) (Fin N) ℝ) (g : Fin N → ℕ)
    (a : ℕ) (i0 : Fin N) (hi0 : g i0 = a) (huniq : ∀ j, g j = a → j = i0) :
    (DFrame.toSquareBlock g a).det = DFrame i0 i0 := by
  haveI hu : Unique {i : Fin N // g i = a} :=
    ⟨⟨i0, hi0⟩, fun ⟨j, hj⟩ => Subtype.ext (huniq j hj)⟩
  rw [Matrix.det_unique]
  have hdef : (default : {i : Fin N // g i = a}) = ⟨i0, hi0⟩ := Subsingleton.elim _ _
  rw [hdef]; rfl

/-! ## The headline regrouping (`{radial-grade 0} ∪ {boundary-grades s+1}`) -/

/-- **The headline regrouping.** For a frame block-triangular under a grading `g` whose image is exactly
`{0} ∪ {s+1 : s : Fin L}` (the radial grade `0` plus one grade per boundary `s`), with the radial block's
abs-det `= R` and boundary `s`'s block abs-det `= B s`, the determinant regroups as `R · ∏_{s : Fin L} B s`.
The combinatorial core: split the grade-`0` (radial) factor off the product over `image g`, then reindex
the boundary grades `s+1 ↦ s` (the `+1` shift is injective). -/
theorem blockTri_headline_regroup {N : ℕ} (DFrame : Matrix (Fin N) (Fin N) ℝ) (g : Fin N → ℕ)
    (hbt : DFrame.BlockTriangular g) (R : ℝ) (B : Fin L → ℝ)
    (himg : Finset.univ.image g = insert 0 (Finset.univ.image (fun s : Fin L => s.val + 1)))
    (hR : |(DFrame.toSquareBlock g 0).det| = R)
    (hB : ∀ s : Fin L, |(DFrame.toSquareBlock g (s.val + 1)).det| = B s) :
    |DFrame.det| = R * ∏ s : Fin L, B s := by
  rw [blockTri_abs_det DFrame g hbt, himg]
  have h0notin : (0 : ℕ) ∉ Finset.univ.image (fun s : Fin L => s.val + 1) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro s; omega
  rw [Finset.prod_insert h0notin, hR]
  congr 1
  rw [Finset.prod_image (by intro a _ b _ hab; exact Fin.ext (Nat.succ_injective hab))]
  exact Finset.prod_congr rfl (fun s _ => hB s)

/-! ## The interior-det HEADLINE (the uniform per-boundary factorization)

The full target. The per-boundary value is the Schur-frame × LDU-core engine product
`|det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)}` (the `schurFrame_abs_det` × `lduCoreDeriv_abs_det`
content); the radial value is `|u_p|^{minAdm−1}` (the `radial_abs_det_minAdm` content). The hypotheses
`hbt`/`hR`/`hB` are the fenced Frame_M obligations (block-triangularity from the b-0 off-block-vanishing;
the per-block-det identifications from the engine). -/

/-- **The interior-det HEADLINE.** Given the fused-frame Jacobian `DFrame` block-triangular under the
layer grading `g` (the b-0 off-block-vanishing transported to `DFrame`), with the radial-grade block's
abs-det `= |u_p|^{minAdm−1}` and boundary-`s`'s block abs-det
`= |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)}`,
the interior Jacobian determinant factorizes uniformly:

  `|DFrame.det| = |u_p|^{minAdm−1} · ∏_s ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)} )`.

The radial/boundary block-det hypotheses are exactly the engine values (`radial_abs_det_minAdm`,
`schurFrame_abs_det` × `lduCoreDeriv_abs_det`); the block-triangularity is the b-0 fact on `DFrame`. -/
theorem interiorDet_headline_of_blockTri {N : ℕ} (M : Fin (L + 1) → ℕ)
    (DFrame : Matrix (Fin N) (Fin N) ℝ) (g : Fin N → ℕ) (hbt : DFrame.BlockTriangular g)
    (up : ℝ)
    -- per-boundary data: K-core size `t s`, spectator exponent `rc s = r s + c s`, `|det K_s|`, LDU pivots
    (t : Fin L → ℕ) (rc : Fin L → ℕ)
    (Kdet : Fin L → ℝ) (q : (s : Fin L) → Fin (t s) → ℝ)
    (himg : Finset.univ.image g = insert 0 (Finset.univ.image (fun s : Fin L => s.val + 1)))
    (hR : |(DFrame.toSquareBlock g 0).det| = |up| ^ (minAdm M - 1))
    (hB : ∀ s : Fin L, |(DFrame.toSquareBlock g (s.val + 1)).det|
      = |Kdet s| ^ (rc s) * ∏ i : Fin (t s), |q s i| ^ (2 * ((t s : ℕ) - 1 - (i : ℕ)))) :
    |DFrame.det|
      = |up| ^ (minAdm M - 1)
        * ∏ s : Fin L,
            (|Kdet s| ^ (rc s) * ∏ i : Fin (t s), |q s i| ^ (2 * ((t s : ℕ) - 1 - (i : ℕ)))) :=
  blockTri_headline_regroup DFrame g hbt (|up| ^ (minAdm M - 1))
    (fun s => |Kdet s| ^ (rc s) * ∏ i : Fin (t s), |q s i| ^ (2 * ((t s : ℕ) - 1 - (i : ℕ))))
    himg hR hB

/-! ## Non-vacuity: the headline's hypotheses are the engine values, and it fires on a real frame

The headline is a genuine conditional, not a hollow one: its per-boundary block-det hypothesis is
EXACTLY the Schur-frame × LDU-core engine product (`hB_eq_engine`), and the full assembly fires on a
concrete block-triangular frame with both block-det hypotheses discharged (`headline_witness`). -/

/-- **The headline's per-boundary value IS the engine product.** For any boundary data
`(X, K, N, l, q, u)`, the Schur-frame Jacobian abs-det `|det DS|` times the LDU-core Jacobian abs-det
`|det D(LDU)|` equals `|K.det|^{r+c} · ∏_i |q_i|^{2(t−1−i)}` — the exact RHS shape the headline's `hB`
consumes. Confirms `hB` is discharged by the banked engine (`schurFrame_abs_det` × `lduCoreDeriv_abs_det`),
not assumed away. -/
theorem hB_eq_engine {t r c : ℕ} (X : Matrix (Fin r) (Fin t) ℝ) (K : Matrix (Fin t) (Fin t) ℝ)
    (Nm : Matrix (Fin t) (Fin c) ℝ) (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ) :
    |LinearMap.det (schurFrameDeriv X K Nm)| * |LinearMap.det (lduCoreDeriv l q u)|
      = |K.det| ^ (r + c) * ∏ i : Fin t, |q i| ^ (2 * ((t : ℕ) - 1 - (i : ℕ))) := by
  rw [schurFrame_abs_det, lduCoreDeriv_abs_det]

/-- **Non-vacuity of the full assembly.** On a concrete `L = 1` diagonal frame `diag ![up, k]` graded by
the coordinate index (radial coord ↦ grade `0`, boundary coord ↦ grade `1`), the headline fires: the
block-triangularity is `blockTriangular_diagonal`, the radial block-det is `|up|^{minAdm−1}` and the
single boundary block-det is the `t = 1` engine value `|k|^{r+c} · ∏_i |q_i|^{…} = |k|` (here `K = [k]`,
`rc = 1`, the `q`-product empty), discharged by `det_toSquareBlock_singleton`. So the headline's
hypotheses are simultaneously satisfiable at a real frame. -/
example (up k : ℝ) (M : Fin 2 → ℕ) (hM : minAdm M = 2) :
    |(Matrix.diagonal ![up, k]).det|
      = |up| ^ (minAdm M - 1)
        * ∏ _s : Fin 1, (|k| ^ (1 : ℕ)
            * ∏ i : Fin 0, |(0 : Fin 0 → ℝ) i| ^ (2 * ((0 : ℕ) - 1 - (i : ℕ)))) := by
  refine interiorDet_headline_of_blockTri (L := 1) M (Matrix.diagonal ![up, k])
    (fun i : Fin 2 => i.val) (blockTriangular_diagonal _) up
    (fun _ => 0) (fun _ => 1) (fun _ => k) (fun _ => (0 : Fin 0 → ℝ)) ?_ ?_ ?_
  · decide
  · rw [det_toSquareBlock_singleton _ _ _ 0 (by decide) (by intro j hj; fin_cases j <;> simp_all),
      Matrix.diagonal_apply_eq, hM]
    norm_num
  · intro s
    rw [det_toSquareBlock_singleton _ _ _ 1 (by fin_cases s; decide)
      (by intro j hj; fin_cases j <;> simp_all), Matrix.diagonal_apply_eq]
    fin_cases s; simp

/-- The `Fin 2 ≃ {i : Fin 3 // (the `{0,1}` grading) i = 1}` reindex for the grade-1 (2×2) boundary
block of the `t = 2` non-vacuity witness below — the small-case analogue of the `card_equiv`/`e9`-style
`toSquareBlock` reindex the opaque-width b-1 will need. -/
def e2blkWitness :
    Fin 2 ≃ {i : Fin 3 // (fun i : Fin 3 => if i.val = 0 then 0 else 1) i = 1} where
  toFun := fun k => match k with | 0 => ⟨1, by decide⟩ | 1 => ⟨2, by decide⟩
  invFun := fun a => if a.1.val = 1 then 0 else 1
  left_inv := by decide
  right_inv := by rintro ⟨a, ha⟩; fin_cases a <;> first | (exfalso; revert ha; decide) | rfl

/-- **Non-vacuity with a non-empty `q`-product (`t = 2`).** On `diag ![up, q0², m]` (grade `0` radial,
grades `1` the 2×2 boundary block), the headline fires with the `t = 2` boundary value `|m|^1 ·
|q0|^{2·1} · |1|^{2·0} = |m|·|q0|²`, exercising the LDU pivot `q0` at exponent `2` END-TO-END (the
2×2 block det `q0²·m`, read via the `e2blkWitness` reindex + `det_fin_two`). Complements the `t = 0`
witness above (which exercises `|K|^{rc}` but not the `q`-product) — together they fire both halves of
the per-boundary value through the assembly. -/
example (up q0 m : ℝ) (M : Fin 2 → ℕ) (hM : minAdm M = 2) :
    |(Matrix.diagonal ![up, q0 ^ 2, m]).det|
      = |up| ^ (minAdm M - 1)
        * ∏ _s : Fin 1, (|m| ^ (1 : ℕ)
            * ∏ i : Fin 2, |(![q0, (1 : ℝ)] : Fin 2 → ℝ) i| ^ (2 * ((2 : ℕ) - 1 - (i : ℕ)))) := by
  refine interiorDet_headline_of_blockTri (L := 1) M (Matrix.diagonal ![up, q0 ^ 2, m])
    (fun i : Fin 3 => if i.val = 0 then 0 else 1) ?_ up
    (fun _ => 2) (fun _ => 1) (fun _ => m) (fun _ => ![q0, (1 : ℝ)]) ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.diagonal]
  · decide
  · rw [det_toSquareBlock_singleton _ _ _ 0 (by decide)
      (by intro j hj; fin_cases j <;> simp_all), Matrix.diagonal_apply_eq, hM]
    norm_num
  · intro s
    fin_cases s
    change |((Matrix.diagonal ![up, q0 ^ 2, m]).toSquareBlock
        (fun i : Fin 3 => if i.val = 0 then 0 else 1) 1).det| = _
    rw [← Matrix.det_submatrix_equiv_self e2blkWitness, Matrix.det_fin_two]
    have d0 : (((Matrix.diagonal ![up, q0 ^ 2, m]).toSquareBlock
        (fun i : Fin 3 => if i.val = 0 then 0 else 1) 1).submatrix e2blkWitness e2blkWitness) 0 0
        = q0 ^ 2 := rfl
    have d1 : (((Matrix.diagonal ![up, q0 ^ 2, m]).toSquareBlock
        (fun i : Fin 3 => if i.val = 0 then 0 else 1) 1).submatrix e2blkWitness e2blkWitness) 1 1
        = m := rfl
    have o01 : (((Matrix.diagonal ![up, q0 ^ 2, m]).toSquareBlock
        (fun i : Fin 3 => if i.val = 0 then 0 else 1) 1).submatrix e2blkWitness e2blkWitness) 0 1
        = 0 := by
      change (Matrix.diagonal ![up, q0 ^ 2, m]) 1 2 = 0
      rw [Matrix.diagonal_apply_ne]; decide
    rw [d0, d1, o01, zero_mul, sub_zero, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_one]
    rw [abs_mul, abs_pow]
    norm_num
    ring

end DLNFibre.DLN.RLCT
