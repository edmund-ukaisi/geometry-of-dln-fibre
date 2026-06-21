**Q1**

Recommended Lean shape: do **not** put “polynomial-entry unimodular `Q^(s)`” in the main API. If you expose `Q`s at all, state them as chart-dependent analytic matrix units:

```lean
Q : X → Matrix (Fin n) (Fin n) ℝ
hQ_unit : ∀ x ∈ U, IsUnit (Q x)
hQ_reg  : ContDiffOn ℝ ⊤ Q U   -- or the repo's eventual analytic predicate
```

plus the corresponding regularity for `Q⁻¹`, or explicit inverse matrices. The pivot hypothesis should be chart-local:

```lean
hPivot : ∀ x ∈ U, IsUnit (pivotDet x)
```

Tradeoff: `IsUnit (Q x)` is fine algebraically, but by itself it is not enough for RLCT transport. RLCT use-sites need measurability, local boundedness, and nonvanishing. A localized ring statement is algebraically honest, but it is not the object consumed by the current real-analytic RLCT infrastructure.

Soundness trap: “polynomial-entry `Q`” is false for the Schur complement once `A⁻¹` appears. This is a wording/API issue, not a mathematical obstruction: say “regular/analytic on the pivot chart” or “over the localization at `det A`.”

**Q2**

Decisive recommendation: **do not require per-factor `Q^(s)` in the main G3.2 API.** The recursion does not consume them. The load-bearing output is a chart-level scalar normal form:

```lean
theorem matrixChain_schur_loss_normalForm
    (M : Fin (L+1) → ℕ) (S : ChainDimSplit M)
    ... :
    ∃ (nReg : ℕ) (Y : Type*) [/* topology, measure */]
      (chart : (Fin nReg → ℝ) × (Params S.red × Y) → Params M)
      (u : (Fin nReg → ℝ) × (Params S.red × Y) → ℝ),
      Measurable u ∧ UnitNear u (0, (0, y0)) ∧
      (∀ᶠ p in 𝓝 (0, (0, y0)),
        dlnLoss M 0 (chart p)
          = u p * ((∑ i, p.1 i ^ 2) + dlnLoss S.red 0 p.2.1))
```

If the construction gives exact equality, set `u = 1`. Keep product/end-unit block diagonalization as an auxiliary theorem if useful:

```lean
prod M (chart p)
  = U p * blockForm (reg p) (prod S.red p.2.1) * V p
```

Tradeoff: hiding per-layer `Q`s simplifies every downstream theorem. You still need `C' : Params S.red` explicitly, but not the internal row/column changes that produced it.

Soundness trap: end-units alone are **not** enough for the Frobenius loss, since `‖UAV‖²_F` is not equal to `‖A‖²_F` for arbitrary analytic units. Either prove the scalar loss normal form directly, or add a separate norm/ideal invariance theorem. Current S1.5 consumes a scalar sum-of-squares form, not matrix equivalence.

**Q3**

`product_reduction` should consume the scalar normal form, not the `Q`s. The chain is:

1. Use the Schur chart to rewrite the local loss as
   ```lean
   ∑ i, x i ^ 2 + dlnLoss Mred 0 Ared
   ```
   possibly times a scalar analytic unit.

2. If there is a scalar unit `u`, remove it with `rlct_unit_invariant`.

3. Apply `rlct_additive_smooth_block` with
   ```lean
   Y := Params Mred × Spectators
   G y := Real.sqrt (dlnLoss Mred 0 y.1)
   ```
   so `G y ^ 2 = dlnLoss Mred 0 y.1`.

4. Recurse or call `resolution_charts` on `Mred`.

Minimal consumable conclusion:

```lean
rlctAtOn
  (fun p : (Fin nReg → ℝ) × Y =>
    (∑ i, p.1 i ^ 2) + G p.2 ^ 2)
  (0, y0)
=
(nReg : ENNReal) / 2 + rlctAtOn (fun y => G y ^ 2) y0
```

Tradeoff: this keeps G3.2 algebraic/geometric and lets S1.5 do the analytic split.

Soundness trap: reusing `block_elimination` pointwise for variable pivots gives noncomputable existential bases, not analytic chart functions. It is fine for constant target normalization; it is not a substitute for explicit Schur formulas in G3.2.

**Q4**

Recommended dimension API: use a new reduced chain over new widths, but avoid raw subtraction in the primary structure. Carry an additive split:

```lean
structure ChainDimSplit (M : Fin (L+1) → ℕ) where
  drop : Fin (L+1) → ℕ
  red  : Fin (L+1) → ℕ
  hsum : ∀ s, drop s + red s = M s
  drops : 0 < ∑ s, drop s   -- or the exact termination condition
```

Then define one split equivalence per vertex:

```lean
def splitEquiv (S : ChainDimSplit M) (s : Fin (L+1)) :
    Fin (S.drop s) ⊕ Fin (S.red s) ≃ Fin (M s)
```

Expose the reduced chain as:

```lean
C' : Params S.red
```

Use `Matrix.fromBlocks` / `toBlocks₂₂` after one `reindex` by `splitEquiv`; do not make downstream recursion manipulate `Fin.castLE` submatrices of the original chain.

Tradeoff: the new-chain representation loses definitional “it is literally a submatrix” transparency, but the normal-form theorem records the relationship once. The recursion and RLCT statements become much cleaner.

Soundness trap: `M s - δ s` in types is fragile and can underflow unless every `δ ≤ M` proof is carried everywhere. The additive split `drop + red = M` localizes all casts to `splitEquiv` lemmas and is much safer for Lean.