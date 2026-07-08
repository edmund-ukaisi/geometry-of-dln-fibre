import DLNFibre.DLN.RLCT.Validate.D1GeBlockProd
import DLNFibre.DLN.RLCT.Validate.D1GeCommonPivot

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeSchurTelescope` — the asymmetric general-`L` Schur telescope

Piece (iii), algebraic core (rungs 1–3 of the corner-elimination chart ladder). The **asymmetric**
Schur-product telescope: the `(1,1)`-Schur complement of the `L`-layer block product factors as an
ordered product of per-layer reduced factors, using ONLY the partial-product (prefix) pivots — never
a per-layer pivot. This is what lets the general-`L` chart avoid the `hLayer` hypotheses of the
symmetric `schur_product_ldu_rec` (which piece (i) does not supply; those would need Cauchy–Binet).

The asymmetric two-factor brick is `Core.schur_product_factor`
(`Sch(A0·A1) = (W − Z⅟X Y)·(V − U⅟M11 M12)`, needing `[Invertible X]` + `[Invertible M11]` — left
pivot and the product pivot, NOT the right factor's own pivot).

* `prefixPivotDomGen` (rung 1) — the pivot domain: at an optimal `v`, a common pivot `ι` (piece (i))
  making EVERY partial-product block pivot `(partProd (genChain …) k).toBlocks₁₁` invertible; from
  `exists_common_pivot_gen` (piece i) with `genPartProd_toBlocks₁₁` (piece ii).
* `redFactorGen` (rung 2 support) — the per-layer reduced factor `R_k` (rel. to the product pivot).
* `blockSchur_partProd_succ_asym` (rung 2) — the asymmetric single-step:
  `blockSchur (partProd C (k+1)) = blockSchur (partProd C k) · R_k`, from the two prefix pivots.
* `blockSchur_partProd_asym_fold` (rung 3) — the telescope `blockSchur (partProd C L) = ∏ R_k`.

Pure `Matrix`/`Ring` algebra over `ℝ`. The chart map `schurChartRawGen` + inverse + `ContDiff` +
(rungs 4–8) are downstream.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Rung 1 — the partial-product pivot domain (from pieces (i) + (ii)) -/

/-- **Rung 1 — the prefix-pivot domain.** At an optimal `v` (`prod H v = B`, `B.rank = r`), the
pivot `ι` of `exists_common_pivot_gen` (piece i) makes EVERY partial-product block pivot invertible:
`((partProd (genChain …) k).toBlocks₁₁).det ≠ 0` for all `k ≤ L`. This is the `hPart` (partial-
pivot) gate the asymmetric telescope needs, obtained by composing piece (i)'s prefix-minor `det ≠ 0`
with piece (ii)'s `genPartProd_toBlocks₁₁` (block corner = prefix minor). -/
theorem prefixPivotDomGen (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (v : Params H) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (hopt : prod H v = B) (hB : B.rank = r) :
    ∃ (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s)),
      ∀ (k : ℕ) (_hk : k < L + 1),
        ((partProd (genChain H r hr ι hι v) k).toBlocks₁₁).det ≠ 0 := by
  obtain ⟨ι, hι, hdet⟩ := exists_common_pivot_gen H r v B hopt hB
  refine ⟨ι, hι, fun k hk => ?_⟩
  rw [genPartProd_toBlocks₁₁ H r hr ι hι v k hk]
  exact hdet ⟨k, hk⟩

/-! ## Rung 2 — the asymmetric single-step Schur factorisation -/

/-- **The per-layer reduced factor** `R_k = C_k₂₂ − C_k₂₁ · (P_{k+1})₁₁⁻¹ · (P_{k+1})₁₂`, reduced
against the PRODUCT pivot `(partProd C (k+1))₁₁` (not `C_k`'s own pivot). `Ring.inverse` (total). -/
noncomputable def redFactorGen {r₀ : ℕ} {n : ℕ → ℕ}
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (k : ℕ) :
    Matrix (Fin (n k)) (Fin (n (k + 1))) ℝ :=
  (C k).toBlocks₂₂ - (C k).toBlocks₂₁ * Ring.inverse (partProd C (k + 1)).toBlocks₁₁
      * (partProd C (k + 1)).toBlocks₁₂

/-- **The asymmetric two-factor Schur-complement factorisation** (`Fin`-core blocks). For blocked
`G0 : (r ⊕ q) × (r ⊕ p)`, `G1 : (r ⊕ p) × (r ⊕ p')` with `G0₁₁` and `(G0·G1)₁₁` invertible (the LEFT
pivot and the PRODUCT pivot — NOT `G1`'s own pivot), the Schur complement of the product factors as
`Sch(G0·G1) = Sch(G0) · (G1₂₂ − G1₂₁·(G0·G1)₁₁⁻¹·(G0·G1)₁₂)`. The `toBlocks`-native recast of
`Core.schur_product_factor`; the asymmetric analogue of `blockSchur_mul` without a `G1₁₁` hyp. -/
theorem blockSchur_mul_asym {r₀ q p p' : ℕ}
    (G0 : Matrix (Fin r₀ ⊕ Fin q) (Fin r₀ ⊕ Fin p) ℝ)
    (G1 : Matrix (Fin r₀ ⊕ Fin p) (Fin r₀ ⊕ Fin p') ℝ)
    (h0 : Invertible G0.toBlocks₁₁) (hP : Invertible (G0 * G1).toBlocks₁₁) :
    blockSchur (G0 * G1)
      = blockSchur G0
          * (G1.toBlocks₂₂ - G1.toBlocks₂₁ * Ring.inverse (G0 * G1).toBlocks₁₁
              * (G0 * G1).toBlocks₁₂) := by
  have hblocks : G0 * G1 = Matrix.fromBlocks
      (G0.toBlocks₁₁ * G1.toBlocks₁₁ + G0.toBlocks₁₂ * G1.toBlocks₂₁)
      (G0.toBlocks₁₁ * G1.toBlocks₁₂ + G0.toBlocks₁₂ * G1.toBlocks₂₂)
      (G0.toBlocks₂₁ * G1.toBlocks₁₁ + G0.toBlocks₂₂ * G1.toBlocks₂₁)
      (G0.toBlocks₂₁ * G1.toBlocks₁₂ + G0.toBlocks₂₂ * G1.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks G0, ← Matrix.fromBlocks_toBlocks G1]
    rw [Matrix.fromBlocks_multiply]
  have hpiv : (G0 * G1).toBlocks₁₁
      = G0.toBlocks₁₁ * G1.toBlocks₁₁ + G0.toBlocks₁₂ * G1.toBlocks₂₁ := by
    rw [hblocks, Matrix.toBlocks_fromBlocks₁₁]
  letI := h0
  letI hPblk : Invertible (G0.toBlocks₁₁ * G1.toBlocks₁₁ + G0.toBlocks₁₂ * G1.toBlocks₂₁) :=
    hpiv ▸ hP
  simp only [blockSchur, hblocks, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Ring.inverse_invertible]
  exact Core.schur_product_factor G0.toBlocks₁₁ G0.toBlocks₁₂ G0.toBlocks₂₁ G0.toBlocks₂₂
    G1.toBlocks₁₁ G1.toBlocks₁₂ G1.toBlocks₂₁ G1.toBlocks₂₂

/-- **Rung 2 — the asymmetric single-step.** Peeling the last layer with only the two prefix pivots
`(partProd C k)₁₁` and `(partProd C (k+1))₁₁` invertible: `blockSchur (partProd C (k+1))
= blockSchur (partProd C k) · redFactorGen C k`. Direct `blockSchur_mul_asym` at
`G0 = partProd C k`, `G1 = C k` (`partProd C (k+1) ≡ partProd C k · C k`). No `hLayer`. -/
theorem blockSchur_partProd_succ_asym {r₀ : ℕ} {n : ℕ → ℕ}
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (k : ℕ)
    (h0 : Invertible (partProd C k).toBlocks₁₁)
    (hP : Invertible (partProd C (k + 1)).toBlocks₁₁) :
    blockSchur (partProd C (k + 1)) = blockSchur (partProd C k) * redFactorGen C k :=
  blockSchur_mul_asym (partProd C k) (C k) h0 hP

/-! ## Rung 3 — the asymmetric telescope -/

/-- The ordered product of the per-layer reduced factors `R_0·R_1·…·R_{k−1}`, of shape
`(Fin (n 0)) × (Fin (n k))` (`redProd C 0 = 1`). The asymmetric analogue of `coreProd` (no
interspersed unipotent corrections). -/
noncomputable def redProd {r₀ : ℕ} {n : ℕ → ℕ}
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) :
    (k : ℕ) → Matrix (Fin (n 0)) (Fin (n k)) ℝ
  | 0 => 1
  | k + 1 => redProd C k * redFactorGen C k

/-- **Rung 3 — the asymmetric Schur telescope.** With every partial-product pivot `(partProd C k)₁₁`
(`k ≤ L`) invertible — and NO per-layer pivot hypothesis — the `(1,1)`-Schur complement of the
`L`-layer block product is the ordered product of the per-layer reduced factors:
`blockSchur (partProd C L) = redProd C L`. Induction on `L`, peeling with
`blockSchur_partProd_succ_asym`; base `blockSchur 1 = 1`. This is the reduced-core factorisation
the general-`L` corner-elimination chart reads — reached from prefix pivots alone. -/
theorem blockSchur_partProd_asym_fold {r₀ : ℕ} {n : ℕ → ℕ}
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (L : ℕ)
    (hPart : ∀ k, k ≤ L → Invertible (partProd C k).toBlocks₁₁) :
    blockSchur (partProd C L) = redProd C L := by
  induction L with
  | zero =>
      simp only [partProd, redProd, blockSchur]
      rw [show (1 : Matrix (Fin r₀ ⊕ Fin (n 0)) (Fin r₀ ⊕ Fin (n 0)) ℝ)
          = Matrix.fromBlocks 1 0 0 1 from Matrix.fromBlocks_one.symm]
      simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
        Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Ring.inverse_one,
        Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  | succ k ih =>
      rw [blockSchur_partProd_succ_asym C k (hPart k (by omega)) (hPart (k + 1) (by omega)),
        ih (fun j hj => hPart j (by omega))]
      rfl

end DLNFibre.DLN.RLCT
