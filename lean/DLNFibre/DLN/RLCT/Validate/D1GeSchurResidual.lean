import DLNFibre.DLN.RLCT.Validate.D1GeChart

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeSchurResidual` — the D1 ≥-leg residual strand (piece iv), general `L`

The general-`L` port of the L = 2 residual strand (`D1L2ExplChartClose`/`Close2`), feeding the banked
consumer `d1ge_hAtV_of_explicit_chart_genL`. Structured around the banked general-`L` chart + telescope
(`schurChartRawGen`, `blockSchur_partProd_asym_fold`, `recoverProductGen`, `blockFlatEquivGen`).

**The reg/core/spec role partition** (Codex-settled, `threads/genm-geleg-iv/codex/rolepart-*.md`),
per layer `s ∈ {0,…,L−1}`, of the block coordinates:

| layer `s`        | `₁₁`  | `₁₂`  | `₂₁`  | `₂₂`  |
|------------------|-------|-------|-------|-------|
| `s = 0`          | SPEC  | SPEC  | REG   | CORE  |
| `0 < s < L−1`    | SPEC  | SPEC  | SPEC  | CORE  |
| `s = L−1`        | REG   | REG   | SPEC  | CORE  |

- **REG** (the `∑ p²` regular block, `card = r(H₀+Hᴸ−r) = nRegGen`): first layer's `₂₁` + last layer's
  `₁₁,₁₂` — mapped by the chart to the full-product corners `(P_L)₂₁, (P_L)₁₁, (P_L)₁₂`.
- **CORE** (`= FlatIdx (H−r)`, the reduced Params): every layer's `₂₂`.
- **SPEC** (untouched by `F`): everything else (first `₁₁,₁₂`; last `₂₁`; all interior `₁₁,₁₂,₂₁`).

The slice value (`p = 0`) is the reduced-core product `∏_s R_s = blockSchur (partProd C L)` (via
`blockSchur_partProd_asym_fold`), i.e. `dlnLoss (H−r)` on the core. **Excluded** (geleg8's germ):
the seam `schurReadout_germ_eq_gen` / the readout `schurReadoutF_gen`.

This file (foundation): the role-index types + the regular cardinality. Downstream (build order):
`roleEquivGen` (the first/interior/last classifier), `splitMPGen`/`splitHomeoGen`, `qResidGen`, the
slice value, and `e`/`hfact`/`hRne`.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The role-index types (general-`L`) -/

/-- **The regular index type** (`∑ p²` block): first layer's `₂₁` (row nonpivot × col pivot) plus
last layer's `₁₁,₁₂` (row pivot × col arbitrary). Cardinality `r(H₀+Hᴸ−r)`. Shape-identical to L = 2
`RegIdx` (general last vertex). -/
abbrev RegIdxGen (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  (Fin (H 0 - r) × Fin r) ⊕ (Fin r × (Fin r ⊕ Fin (H (Fin.last L) - r)))

/-- **The core index type**: exactly `FlatIdx (H − r)` (every layer's `₂₂` — the reduced Params),
so it is `paramsEquivFlat (H − r)`-ordered. -/
abbrev CoreIdxGen (H : Fin (L + 1) → ℕ) (r : ℕ) : Type := FlatIdx (fun s => H s - r)

/-- The regular direction count `r(H₀+Hᴸ−r)` (the general-`L` `nRegL2`). -/
abbrev nRegGen (H : Fin (L + 1) → ℕ) (r : ℕ) : ℕ := r * (H 0 + H (Fin.last L) - r)

/-- `Fintype.card (RegIdxGen H r) = nRegGen H r` (needs `r ≤ H 0`, `r ≤ H (last L)`). Mirrors the
L = 2 `card_RegIdx`. -/
theorem card_RegIdxGen (H : Fin (L + 1) → ℕ) (r : ℕ) (hr0 : r ≤ H 0)
    (hrL : r ≤ H (Fin.last L)) : Fintype.card (RegIdxGen H r) = nRegGen H r := by
  simp only [RegIdxGen, nRegGen, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have h1 : r + (H (Fin.last L) - r) = H (Fin.last L) := Nat.add_sub_cancel' hrL
  have h2 : H 0 + H (Fin.last L) - r = (H 0 - r) + H (Fin.last L) := by omega
  rw [h1, h2]; ring

end DLNFibre.DLN.RLCT
