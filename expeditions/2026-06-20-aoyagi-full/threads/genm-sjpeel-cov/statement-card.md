# Statement card — general-dimension pivot-chart c.o.v. base (`genm-sjpeel-cov` tide)

**Status:** sorry-free + clean-three (forced `#print axioms`) for all delivered results. New module
`lean/DLNFibre/DLN/RLCT/Foundations/PivotSchurChart.lean`, wired into
`RouteMSJResolution` (import + API pins + docstrings). Green in the full import closure of
`RouteMSJResolution` (8301 jobs) and full `scripts/lb DLNFibre`. Base
`origin/genm-sjpeel @300fe28d`; branch `genm-sjpeel-cov`. **NOT yet wired into `DLNFibre.lean`**
(single-writer aggregator) — controller to add `import DLNFibre.DLN.RLCT.Foundations.PivotSchurChart`
(it is transitively pulled in via `RouteMSJResolution` already, but add the explicit line per convention).

This tide builds the **c.o.v. base** the boundary peel `sjBoundaryPeel` (piece 3 of the R1-UPPER
`(S,J)` mountain; design cert `threads/genm-r1upper-design/design-cert.md`, piece 2) consumes on each
pivot chart. It does NOT touch `sjBoundaryPeel`'s or `sjJointResolution`'s sorries — the module still
carries exactly those two honest sorries. The genuinely-new analytic ASSEMBLY on top of this base
(radial blow-up → 1-D Beta fibre bound → a.e. gluing) is LATER tides.

## The target

> **Claim.** The network-free matrix-algebra + measure-theory base of Aoyagi's Lemma-2 pivot-chart
> change of variables, at general (opaque) block dimensions: (i) the pivot-chart cover of the front
> factor by charts with a `t×t` invertible minor; (ii) the unit-triangular LDU exposing the Schur
> corank block `Γ`; (iii) the Jacobian-1 measure-preserving block shear that exposes `Γ`.
>
> - **Lean:** module `DLNFibre.DLN.RLCT.Foundations.PivotSchurChart`
>   (`lean/DLNFibre/DLN/RLCT/Foundations/PivotSchurChart.lean` @ base `300fe28d`, branch
>   `genm-sjpeel-cov`).
> - **Gloss.** For a front factor `A₀ : Matrix (Fin m) (Fin n) K` over a field, `t ≤ A₀.rank` iff some
>   `t×t` minor is a unit (`pivotLocus_eq_iUnion`); for an invertible pivot block `P`, block-form
>   `A₀ = fromBlocks P B C D = L · diag(P, Γ) · U` with `L`, `U` det-1 and `Γ = D − C P⁻¹ B`
>   (`aoyagi_ldu`); the block shear `(x, D) ↦ (x, D − K x)` is measure-preserving for measurable `K`
>   (`measurePreserving_shearSub`).
> - **Proved (sorry-free, clean-three `[propext, Classical.choice, Quot.sound]`).**
>   - **§A Aoyagi Lemma 2 (algebra):** `aoyagiSchur` (`Γ = D − C ⅟P B`), `aoyagiLower`/`aoyagiUpper`
>     (the unit-triangular factors), `aoyagi_ldu` (the LDU `A₀ = L · diag(P,Γ) · U`, from Mathlib
>     `fromBlocks_eq_of_invertible₁₁`), `aoyagiLower_det = 1` / `aoyagiUpper_det = 1` (the algebraic
>     "Jacobian 1"), `aoyagi_det_square` (det factorisation, square-Γ diagnostic case).
>   - **§B pivot-chart cover:** `exists_indep_cols_of_le_rank` (rank ≥ t selects t independent
>     columns), `exists_nonsingular_submatrix_of_le_rank` (**reverse**: rank ≥ t ⟹ a unit `t×t` minor,
>     via the column selection + `Core.exists_pivot_cols_of_rank` on the transpose),
>     `isUnit_submatrix_le_rank` (**forward**: a unit minor ⟹ rank ≥ t), the monotonicity helpers
>     `rank_submatrix_id_col_le`/`_row_le`/`rank_submatrix_le'`, the chart set `pivotChart`, and the
>     characterisation `pivotLocus_eq_iUnion` (`{A | t ≤ rank} = ⋃_{ρ,κ} pivotChart ρ κ`).
>   - **§C Jacobian-1 measure statement:** `measurePreserving_shearSub` (the block shear `D ↦ D − K x`
>     is measure-preserving, a `skew_product` with identity base and per-fibre translation).
> - **Assumed.** none (the delivered results are unconditional; §A over any `CommRing`, §B over any
>   field, §C for any measurable `K` with the ambient additive/measure typeclasses).
> - **Cited.** Mathlib `fromBlocks_eq_of_invertible₁₁` / `det_fromBlocks_one₁₁` / `det_fromBlocks₁₁`
>   (Schur complement), `MeasurePreserving.skew_product` + `measurePreserving_add_right`, the
>   rank/column-span API (`rank_eq_finrank_span_cols`, `finrank_span_eq_card`, `rank_transpose`,
>   `rank_of_isUnit`); the banked in-repo `Core.Matrix.exists_pivot_cols_of_rank` and
>   `Foundations.CoreShearMP.measurePreserving_coreShear` (pinned as the function-space instance).
> - **Deferred (LATER tides — the analytic ASSEMBLY that USES this base).** the radial blow-up
>   `Γ = z·V` (Jacobian `z^{a−1}`); the finite-cutoff 1-D Beta `z`-integral collapsing the fibre to
>   `P_tail^{−(c'−a/2)}·P_full^{−a/2}`; the `lintegral_mono_ae` a.e. gluing over the chart cover into
>   `sjBoundaryPeel`. `sjBoundaryPeel` and `sjJointResolution` remain their honest sorries (untouched).
> - **Status.** sorry-free + clean-three; fidelity review pending (reviewer to confirm the Lean matches
>   the cert's piece-2 pivot–Schur chart).

## What is CLOSED (sorry-free) — the reusable c.o.v. base

| § | Declaration(s) | How |
|---|---|---|
| A (Aoyagi Lemma 2) | `aoyagiSchur`, `aoyagiLower`, `aoyagiUpper`, `aoyagi_ldu`, `aoyagiLower_det`, `aoyagiUpper_det`, `aoyagi_det_square` | thin wrapper of Mathlib `fromBlocks_eq_of_invertible₁₁` + `det_fromBlocks_one₁₁` |
| B (pivot cover) | `rank_submatrix_id_col_le`/`_row_le`/`rank_submatrix_le'`, `exists_indep_cols_of_le_rank`, `exists_nonsingular_submatrix_of_le_rank`, `isUnit_submatrix_le_rank`, `pivotChart`, `pivotLocus_eq_iUnion` | column-span monotonicity; size-`t` independent-column subfamily (`exists_linearIndependent'`); `Core.exists_pivot_cols_of_rank` on the transpose for the row pivots |
| C (Jacobian-1 measure) | `measurePreserving_shearSub` | `MeasurePreserving.skew_product` (identity base) + per-fibre `measurePreserving_add_right` |

Wired into `RouteMSJResolution`: import added; two API-pin `example`s (`pivotLocus_eq_iUnion`,
`aoyagi_ldu` at the front-factor block dimensions); the piece-2 module note and `sjBoundaryPeel`'s
residual docstring extended to name the landed base (the sorry left intact).

## Key statement shapes (fidelity anchors against the cert / Aoyagi §5 Lemma 2)

- **`aoyagi_ldu`**: `fromBlocks P B C D = aoyagiLower P C * fromBlocks P 0 0 (aoyagiSchur P B C D) *
  aoyagiUpper P B` with `aoyagiSchur P B C D = D − C ⅟P B`, `aoyagiLower P C = fromBlocks 1 0 (C ⅟P) 1`,
  `aoyagiUpper P B = fromBlocks 1 (⅟P B) 0 1`. Matches Aoyagi's `Q₁ C^{(s)} Q₂ = diag(pivot, Γ)`,
  `Γ = A₀⁽⁴⁾ − A₀⁽³⁾(A₀^{[t]})⁻¹A₀⁽²⁾` (cert §2). Both triangular factors have det 1.
- **`pivotLocus_eq_iUnion t`**: `{A : Matrix (Fin m) (Fin n) K | t ≤ A.rank} = ⋃ (ρ : Fin t ↪ Fin m)
  (κ : Fin t ↪ Fin n), pivotChart ρ κ`, `pivotChart ρ κ = {A | IsUnit (A.submatrix ρ κ)}`. The finite
  chart cover of the rank-`≥ t` front-factor locus by the `t×t`-invertible-minor charts.
- **`measurePreserving_shearSub`**: `MeasurePreserving (fun p : α × β => (p.1, p.2 − K p.1)) volume
  volume` for measurable `K : α → β` (β an additive group with right-invariant volume). The MEASURE
  form of "Jacobian 1"; the concrete Aoyagi correction `K = C P⁻¹ B` (continuous, hence measurable, on
  the pivot chart) exposes `Γ = D − K` as the new fibre variable.

## Scope note (what this tide is NOT)

Per the design cert, the c.o.v. base is Aoyagi §5 piece 2 (algebraic plumbing) + the Jacobian-1
measure fact. It is NOT the peel itself. The exact per-step identity
`J ≍ P_tail^{−(c'−a/2)}·P_full^{−a/2}` (cert §ADDENDUM) needs the radial blow-up + finite-cutoff Beta
integral on top of this base, and the a.e. gluing over the cover — all confined to `sjBoundaryPeel`
(piece 3) and its sub-tides. The det factorisation `aoyagi_det_square` is stated only for square `Γ`
(the general Aoyagi corank block `(M₀−t)×(M₁−t)` is rectangular; `det` does not apply) — flagged
in-file to avoid an overclaim.

## Recommended next-tide order (from here)

1. **Radial blow-up + 1-D Beta fibre bound** (piece 3 core) — on a pivot chart, apply `aoyagi_ldu` +
   `measurePreserving_shearSub` to expose `Γ`, blow up `Γ = zV` (Jacobian `z^{a−1}`), and do the
   finite-cutoff `z`-integral (the cert's `½·B(a/2, c'−a/2)` Beta). Consumes this tide's base.
2. **a.e. assembly into `sjBoundaryPeel`** — glue the per-chart bounds over `pivotLocus_eq_iUnion` with
   `lintegral_mono_ae` (the degenerate low-rank locus is null; the naive fixed-`Q` pointwise lift is
   FALSE under the `Real.rpow` `0^{neg}=0` convention — see `sjBoundaryPeel`'s docstring).
3. **`sjJointResolution`** (pieces 4/5/7) — the standing L≥3 wall (unchanged by this tide).

## Instrument caveat
§A/§C transcribe Aoyagi §5 Lemma 2 (the LDU + the Jacobian-1 shear); §B is the classical rank↔minor
characterisation. All three are proved in Lean sorry-free + clean-three (forced `#print axioms`
`[propext, Classical.choice, Quot.sound]`). The base is network-free (a field for §B, a `CommRing` for
§A, generic measure/additive typeclasses for §C), so it is reusable beyond the front factor.
