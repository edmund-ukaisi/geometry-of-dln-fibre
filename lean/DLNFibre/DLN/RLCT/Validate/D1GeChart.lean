import DLNFibre.DLN.RLCT.Validate.D1GeSchurTelescope

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeChart` — the general-`L` corner-elimination chart (rungs 4+)

Piece (iii), the chart itself. The general-`L` analogue of `schurChartRaw`/`schurChartRawInv`
(`D1L2PhiExpl`), built on the asymmetric Schur telescope (`D1GeSchurTelescope`, rungs 1–3). Operates
on the `ℕ`-indexed `Fin`-core block chain `C` (the natural home of `partProd`/`redFactorGen`); the
`BlockParamsGen`/flat conjugation is a later bridge.

**Rung 4 — the packing** (Codex-settled, DOF-verified; artefact
`threads/genm-geleg1/codex/piece-iii-rung4-packing-{prompt,answer}.md`). `schurChartRawGen C L`
per layer slot `s`:

    slot s = fromBlocks (P_{s+1})₁₁  (P_{s+1})₁₂  Q_s.21  R_s
    Q_s.21 = (P_L)₂₁  (s = 0) | (C_s)₂₁  (s ≥ 1),   R_s = redFactorGen C s,   P_k = partProd C k.

The top row is the PREFIX-product top row `(P_{s+1})₁₁, (P_{s+1})₁₂` (regular); the `(2,2)`
corner is the reduced factor `R_s`; the lower-left holds `(C_s)₂₁` except slot `0`, which holds the
full product's `(P_L)₂₁` (last regular direction). Same type as `C s`, so again a chain. The
`nReg = r·(H₀+Hᴸ−r)` regular directions live in `(P_L)₁₁, (P_L)₁₂, (P_L)₂₁`.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

/-! ## Rung 4 — the packed corner-elimination chart map -/

/-- **The general-`L` corner-elimination chart** (raw, chain form). Per slot `s`, packs the prefix
product `(partProd C (s+1))` top row, the lower-left `(C_s)₂₁` (or `(partProd C L)₂₁` at `s=0`),
the reduced factor `redFactorGen C s`. Same type as `C`, so again a chain. The general-`L` analog of
`schurChartRaw`. -/
noncomputable def schurChartRawGen {r₀ : ℕ} {n : ℕ → ℕ}
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (L : ℕ) :
    (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ :=
  fun s => Matrix.fromBlocks
    (partProd C (s + 1)).toBlocks₁₁
    (partProd C (s + 1)).toBlocks₁₂
    (if h : s = 0 then h.symm ▸ (partProd C L).toBlocks₂₁ else (C s).toBlocks₂₁)
    (redFactorGen C s)

variable {r₀ : ℕ} {n : ℕ → ℕ}
  (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (L : ℕ)

/-- The `(1,1)` corner of slot `s`: the prefix-product pivot `(partProd C (s+1))₁₁`. -/
@[simp] theorem schurChartRawGen_toBlocks₁₁ (s : ℕ) :
    (schurChartRawGen C L s).toBlocks₁₁ = (partProd C (s + 1)).toBlocks₁₁ := rfl

/-- The `(1,2)` corner of slot `s`: the prefix-product `(partProd C (s+1))₁₂`. -/
@[simp] theorem schurChartRawGen_toBlocks₁₂ (s : ℕ) :
    (schurChartRawGen C L s).toBlocks₁₂ = (partProd C (s + 1)).toBlocks₁₂ := rfl

/-- The `(2,2)` corner of slot `s`: the reduced factor `R_s = redFactorGen C s`. -/
@[simp] theorem schurChartRawGen_toBlocks₂₂ (s : ℕ) :
    (schurChartRawGen C L s).toBlocks₂₂ = redFactorGen C s := rfl

/-- The lower-left of slot `s ≥ 1`: `(C_s)₂₁`. -/
@[simp] theorem schurChartRawGen_toBlocks₂₁_succ (s : ℕ) :
    (schurChartRawGen C L (s + 1)).toBlocks₂₁ = (C (s + 1)).toBlocks₂₁ := rfl

/-- The lower-left of slot `0`: the full product's `(P_L)₂₁ = (partProd C L)₂₁` (the last regular
direction). -/
@[simp] theorem schurChartRawGen_toBlocks₂₁_zero :
    (schurChartRawGen C L 0).toBlocks₂₁ = (partProd C L).toBlocks₂₁ := rfl

/-! ## Rung 5 — recovering the product from the chart output -/

/-- The ordered product of the `(2,2)` corners of a chain `Q`, `(Q 0)₂₂·…·(Q (k−1))₂₂`, of shape
`(Fin (n 0)) × (Fin (n k))` (`= 1` at `k = 0`). At `Q = schurChartRawGen C L` this is `redProd C`
(`blockDiagProd_schurChartRawGen`), i.e. the reduced core `blockSchur (partProd C L)`. -/
noncomputable def blockDiagProd {r₀ : ℕ} {n : ℕ → ℕ}
    (Q : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) :
    (k : ℕ) → Matrix (Fin (n 0)) (Fin (n k)) ℝ
  | 0 => 1
  | k + 1 => blockDiagProd Q k * (Q k).toBlocks₂₂

/-- **`recoverProductGen`** — rebuild the full product's block form from the chart output over
`last + 1` layers: top row `(P_L)₁₁, (P_L)₁₂` from the last slot, lower-left `(P_L)₂₁` from slot 0,
and the eliminated `(2,2)` corner as `(P_L)₂₁·(P_L)₁₁⁻¹·(P_L)₁₂ + ∏ R_s`. Parametrised by `last`,
last slot index `= L − 1`) so the output width `Fin (n (last+1))` needs no `L−1` cast. General-`L`
analogue of `recoverProduct`. -/
noncomputable def recoverProductGen {r₀ : ℕ} {n : ℕ → ℕ}
    (Q : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (last : ℕ) :
    Matrix (Fin r₀ ⊕ Fin (n 0)) (Fin r₀ ⊕ Fin (n (last + 1))) ℝ :=
  Matrix.fromBlocks (Q last).toBlocks₁₁ (Q last).toBlocks₁₂ (Q 0).toBlocks₂₁
    ((Q 0).toBlocks₂₁ * (Q last).toBlocks₁₁⁻¹ * (Q last).toBlocks₁₂ + blockDiagProd Q (last + 1))

/-- The `(2,2)`-corner fold of the chart output is the reduced-factor telescope `redProd C`. By
on `k`, reading `(schurChartRawGen C L s)₂₂ = redFactorGen C s`. -/
theorem blockDiagProd_schurChartRawGen {r₀ : ℕ} {n : ℕ → ℕ}
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (L : ℕ) (k : ℕ) :
    blockDiagProd (schurChartRawGen C L) k = redProd C k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [blockDiagProd, redProd, ih, schurChartRawGen_toBlocks₂₂]

/-- **Rung 5 — the chart output rebuilds the product.** `recoverProductGen (schurChartRawGen C
last = partProd C (last+1)` on the prefix-pivot domain: the three regular corners are the packed
`(P_L)₁₁/₁₂/₂₁`, and the eliminated `(2,2)` corner is rebuilt as `(P_L)₂₁·(P_L)₁₁⁻¹·(P_L)₁₂ +
blockSchur (partProd C L)` (the reduced core, `blockDiagProd_schurChartRawGen` + the asymmetric
telescope `blockSchur_partProd_asym_fold`). Validates the packing. General-`L` analogue of
`recoverProduct_schurChartRaw`. -/
theorem recoverProductGen_schurChartRawGen {r₀ : ℕ} {n : ℕ → ℕ}
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (last : ℕ)
    (hPart : ∀ k, k ≤ last + 1 → Invertible (partProd C k).toBlocks₁₁) :
    recoverProductGen (schurChartRawGen C (last + 1)) last = partProd C (last + 1) := by
  letI hpiv : Invertible (partProd C (last + 1)).toBlocks₁₁ := hPart (last + 1) le_rfl
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks (partProd C (last + 1))]
  rw [recoverProductGen, schurChartRawGen_toBlocks₁₁, schurChartRawGen_toBlocks₁₂,
    schurChartRawGen_toBlocks₂₁_zero, blockDiagProd_schurChartRawGen,
    ← blockSchur_partProd_asym_fold C (last + 1) hPart, blockSchur]
  congr 1
  -- `(P_L)₂₁·(P_L)₁₁⁻¹·(P_L)₁₂ + ((P_L)₂₂ − (P_L)₂₁·(Ring.inverse (P_L)₁₁)·(P_L)₁₂) = (P_L)₂₂`.
  rw [Ring.inverse_invertible, Matrix.invOf_eq_nonsing_inv (partProd C (last + 1)).toBlocks₁₁]
  abel

end DLNFibre.DLN.RLCT
