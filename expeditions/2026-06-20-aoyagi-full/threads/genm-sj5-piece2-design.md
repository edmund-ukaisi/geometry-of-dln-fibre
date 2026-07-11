# Piece #2 design — the AG-free corank-survival bridge (`ρ ≥ b` → corank rows survive)

**Thread `genm-sj5-desc2`. Pen-and-paper BEFORE build (controller watch-point: keep AG-free).
Build gated on cover's #1-PASS.**

## The core lemma (AG-free, banked-adjacent)

> **`corank_survival_ae`.** For `Zdeep : Matrix (Fin m) (Fin D) ℝ` with `b ≤ Zdeep.rank`,
> `∀ᵐ A : Matrix (Fin b) (Fin m) ℝ, (A * Zdeep).rank = b`.

This is cert §8 / the controller's #2 verbatim: "on a rank-`r ≥ b` cell, for a.e. FREE `A_cor`,
`rank(A_cor·Zdeep) = min(b,r) = b`; the rank-deficient set is a proper minor-cut null set." The
`b ≤ Zdeep.rank` hypothesis is #1's output (`ρ ≥ b`, the co-minimizing deeper rank).

## Proof (pure linear algebra + measure, NO AG components)

1. **Factor** `Zdeep = U * V`, `U : Fin m → Fin r`, `V : Fin r → Fin D`, both rank `r = Zdeep.rank ≥ b`
   — banked `D1JointDiffRankExact.exists_rank_factorization_gen`.
2. **Right-mul by full-row-rank `V` preserves rank:** `rank(A·Zdeep) = rank(A·U·V) = rank(A·U)`
   (banked range/rank lemmas `range_rightMul_eq_of_factor` / `finrank_range_*`, D1JointDiffRankExact).
   `A·U : Fin b → Fin r`, `b ≤ r`, so `rank(A·U) ≤ b`.
3. **rank `= b` ⟺ a `b×b` minor of `A·U` is nonzero** — banked `Core.RankLocusClosed`
   (`rank_le_iff_forall_submatrix_det_eq_zero` / `exists_submatrix_det_ne_zero_of_le_rank`).
4. **The deficient locus is a proper minor-cut null set.** Each `b×b` minor `det((A·U).submatrix …)`
   is a polynomial in `A`'s entries (linear in `A`); NOT identically zero — a witness `A₀` with
   `rank(A₀·U) = b` exists because `U` has rank `r ≥ b` (pick `b` independent rows / a left selection).
   So `{A : rank(A·U) < b}` is the common zero locus of finitely many nonzero polynomials in `A`, hence
   Lebesgue-null — the "nonzero `MvPolynomial` ⟹ `∀ᵐ z, eval z ≠ 0`" pattern banked in
   `DeepestCoreNonvanishing` (`dlnLoss_deepest_core_ae_ne_zero`, encode `= eval z poly`, `poly ≠ 0`).

## AG-FREE confirmation (the controller's critical watch-point)

- Genericity is in the **FREE integration variable `A`** (the corank block), with `Zdeep` **fixed** of a
  **given** rank `r` (the rank comes from the cell it sits in / #1's arithmetic `ρ ≥ b`, NOT from a
  generic point of a variety).
- The deficient set is a **minor-cut null set** (polynomial nonvanishing → measure zero) — Borel /
  measure-theory, D1-lane. **No irreducible-component decomposition, no generic-rank-on-a-component.**
- The rank of `Zdeep` is an INPUT (`b ≤ Zdeep.rank`), never derived as "the generic rank on the top-dim
  component". #1 supplies `ρ ≥ b` combinatorially; the cell `{rank Zdeep = r}` (if stratified) is
  minor-Borel. So the AG wall (#114) does NOT reappear. ✓

## ★ Route-interface question for the controller (before I state #2 at the right seam)

Two banked terminals exist, with DIFFERENT corank-survival needs:
- **route-A base** `RouteMSJLeafFinite`/`LeafRayleigh` — Rayleigh bound `c·frobSq Γ ≤ frobSq(Γ·Z)`,
  needs the **units interface** `Z·Zᵀ ≽ c·I` (`Z` full row rank). `corank_survival_ae` (`rank = b`)
  ⟹ `(A·Zdeep) full row rank` ⟹ `(A·Zdeep)(A·Zdeep)ᵀ ≻ 0` ⟹ `∃c>0, ≽ cI` — the **units bridge**.
- **isotropic PURE** `RouteMSJCorankPure` — explicitly REMOVES the anisotropy `Δ↦Δ·Q_b` by CoV and
  integrates `Δ` through its own `frobSq Δ`, "NEVER integrating Δ out against Q_b (the divergent Gram
  determinant)". This route does NOT need corank survival at all.

Which route does the CHOSEN `DecoratedStepHyp` peel use? If route-A: #2 delivers `corank_survival_ae`
+ the **units bridge** `full-row-rank ⟹ ∃c>0, Z·Zᵀ≽cI` (feeds LeafFinite's `hZ`). If isotropic: #2's
role is only the a.e.-nonvanishing of the corank generator (`H₁` a unit a.e.), NOT the units interface.
The two banked terminals suggest a route decision I should not re-litigate — please confirm the peel's
consumer so I state #2's output at the exact seam.

## Cleaner proof (minor-only, no factorization needed) — FULLY BANKED-ADJACENT

1. `Core.RankLocusClosed.exists_submatrix_det_ne_zero_of_le_rank Zdeep (b ≤ Zdeep.rank)` →
   `(ρ₀ : Fin b ↪ Fin m, σ₀ : Fin b ↪ Fin D)` with `det (Zdeep.submatrix ρ₀ σ₀) ≠ 0`.
2. Row-selection `A₀` (from `ρ₀`): `(A₀ * Zdeep).submatrix id σ₀ = Zdeep.submatrix ρ₀ σ₀`, so the
   `(id, σ₀)`-minor of `A₀ * Zdeep` is `≠ 0` — the ACHIEVABILITY witness (no explicit left-inverse).
3. `A ↦ det ((A * Zdeep).submatrix id σ₀)` is an `MvPolynomial.eval A` of a poly `P` (entries of
   `A * Zdeep` are affine in `A`; `det` a polynomial) — mirror the `coreXmat`/`corePoly`/`prodPolyAux_map`
   ring-hom encoding in `DeepestCoreNonvanishing`. `P ≠ 0` (nonzero at `A₀`, step 2).
4. `Core.MeasureTheory.PolynomialZeroSet.MvPolynomial.ae_eval_ne_zero P hP` (banked `@68ef083`):
   `volume {A | eval A P = 0} = 0`.
5. `rank (A*Zdeep) < b ⟹ det ((A*Zdeep).submatrix id σ₀) = 0` (banked
   `RankLocusClosed.submatrix_det_eq_zero_of_rank_le`), so `{rank < b} ⊆ {eval P = 0}` — null. With the
   trivial upper bound `rank (A*Zdeep) ≤ b` (b rows), `∀ᵐ A, rank (A*Zdeep) = b`.

The U·V factorization (`D1JointDiffRankExact`) is NOT needed — the minor route is direct. The one piece
of genuine work is step 3 (det-as-`MvPolynomial`) — and even it has a **direct template in
`RankLocusClosed` itself** (the "Polynomialization: rank-pattern minors as coordinate polynomials"
section: `genericTuple` / `canonicalCoord` / `eval_genericTuple`, "each `(s)`-minor of the generic
`submult` is a polynomial whose value at `canonicalCoord A` is the numerical minor"). Adapt that to
`A ↦ (A * Zdeep).submatrix id σ₀`'s det. **Signatures all verified — no wall; a ~150–200 line build.**

## Build (on cover #1-PASS + route-interface confirmation)

New module `RouteMSJCorankSurvival.lean` importing `Core.RankLocusClosed` +
`Core.MeasureTheory.PolynomialZeroSet` (+ mirror `DeepestCoreNonvanishing`'s poly-encoding).
Deliverables: `corank_survival_ae` + (if route-A) the units bridge
`full-row-rank ⟹ ∃c>0, Z·Zᵀ≽c·I`. Pre-stage the banked lemma names/types as `example` contracts first.

## Units bridge (#2 b→units) — scoping (for fresh-budget pickup)

> **Target.** `Z : Matrix (Fin n) (Fin D) ℝ`, `Z.rank = n` (full ROW rank) ⟹
> `∃ c > 0, (Z * Zᵀ - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef`. Feeds route-A
> `corankLeaf_rpow_lt_top`'s `hZ` (and via `corank_survival_ae`, `Z := A·Zdeep` is full-row-rank a.e.).

Two sub-facts:
- **(1) `Z.rank = n ⟹ (Z * Zᵀ).PosDef`.** `Z*Zᵀ` is always PosSemidef (`Matrix.posSemidef_self_mul_conjTranspose`,
  over ℝ `conjTranspose = transpose`). Full row rank ⟹ `Zᵀ *ᵥ x ≠ 0` for `x ≠ 0` (left-nullspace of `Z`
  is `0`), so `xᵀ(ZZᵀ)x = ‖Zᵀ *ᵥ x‖² > 0` — PosDef via `posDef_iff_dotProduct_mulVec`. The
  invertibility half is banked-adjacent in `Core.Matrix.GramFullRank` (`gram_det_ne_zero_of_submatrix_det_ne`,
  `right_factor_det_ne_of_rank_eq`); the `≠0`-dotProduct is the elementary bit.
- **(2) `A.PosDef ⟹ ∃ c > 0, (A - c • 1).PosSemidef`.** NOT banked. Cleanest is the min over the unit
  sphere: `m := min_{‖x‖=1} xᵀAx` (compact sphere, continuous form, `IsCompact.exists_isMinOn`), `m > 0`
  (PosDef, minimiser `≠ 0`), then homogeneity gives `xᵀAx ≥ m‖x‖²` ∀x, i.e. `(A - m•1) ≽ 0`. AVOID the
  eigenvalue/eigenvector route (lean/CLAUDE.md spectral-isDefEq-timeout hazard). ~60–100 lines; a
  fresh-budget spectral build.

**Status:** #2-core `corank_survival_ae` DONE (green, `RouteMSJCorankSurvival.lean`). Units bridge is
the clean next piece — deferred to fresh budget (DON'T-DEGRADE) so the spectral sub-fact (2) is built
carefully, not near a context boundary.
