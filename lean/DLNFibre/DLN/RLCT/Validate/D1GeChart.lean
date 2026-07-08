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

end DLNFibre.DLN.RLCT
