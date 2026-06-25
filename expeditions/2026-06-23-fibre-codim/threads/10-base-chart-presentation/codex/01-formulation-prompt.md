# Codex consult — cleanest Lean 4 / Mathlib v4.29 formulation of the pivot-chart Schur presentation

## Context
DLNFibre harness. Lean 4, Mathlib pinned at v4.29. Engine layer (`DLNFibre.Core`), network-free, only depends on Mathlib.

We are building the FOUNDATION tile (G2-1) of a determinantal-presentation build. Goal of THIS tile:
the **pivot-chart Schur parametrization** of the exact-rank-`r` determinantal locus
`Mat^{rk=r}_{p×q}` over a field `k`.

On the pivot chart `U` where the top-left `r×r` block `Δ` is invertible, a block matrix
`M = [[Δ, B12],[B21, B22]]` (sizes `r,p−r` × `r,q−r`) has **rank exactly `r` iff the Schur complement
vanishes**: `B22 = B21 · Δ⁻¹ · B12`. This gives the bijection
`Mat^{rk=r} ∩ U ≅ GL_r × Mat_{r×(q−r)} × Mat_{(p−r)×r}`, dimension `δ = r(p+q−r)`.

This presentation must later (G2-3) feed a LOCALIZED Schur `AlgEquiv` trivializing the rank-chart of the
multiplication-map comorphism: localize the base coordinate ring at the pivot minor `Δ` and show the
exact-rank chart is a base change `Rt ≃ₐ[Rb] Rb ⊗[k] F_E` (free over the base). So the chart presentation
needs to be in a form whose coordinate ring localizes cleanly.

## Mathlib facts confirmed present at v4.29
- `Matrix.fromBlocks A B C D : Matrix (n ⊕ o) (l ⊕ m) α` and `toBlocks₁₁..₂₂`.
- `Matrix.fromBlocks_eq_of_invertible₁₁` (LDU): for `[Invertible A]`,
  `fromBlocks A B C D = fromBlocks 1 0 (C*⅟A) 1 * fromBlocks A 0 0 (D - C*⅟A*B) * fromBlocks 1 (⅟A*B) 0 1`.
- `Matrix.rank_mul_eq_left_of_isUnit_det` / `rank_mul_eq_right_of_isUnit_det`: multiplying by a
  matrix with unit determinant preserves rank.
- `Matrix.det_fromBlocks₁₁`, `isUnit_fromBlocks_zero₂₁/₁₂`, `fromBlocks_one`, `fromBlocks_multiply`,
  `det_fromBlocks_one₁₁`/`₂₂`.
- `Matrix.rank` (over CommRing), `rank_eq_finrank_range_toLin`, `rank_zero`, `rank_one`.

## What is MISSING in Mathlib v4.29 (confirmed by ripgrep)
- NO `rank (fromBlocks A 0 0 D) = rank A + rank D` (block-diagonal rank additivity).
- NO rank-normal-form / "equal rank ⟹ equivalent". (The harness already built map-level conjugation in
  `Core.FibreNormalForm`.)

## My planned route
1. **Block/Schur iff lemma** (over a field `k`, `m l n : Type*` Fintype DecidableEq, `Δ : Matrix m m k`
   `[Invertible Δ]`):
   `(fromBlocks Δ B12 B21 B22).rank = Fintype.card m ↔ B22 = B21 * ⅟Δ * B12`.
   - LDU-sandwich via `fromBlocks_eq_of_invertible₁₁`; `L`,`U` unipotent (det 1, `det_fromBlocks_one₁₁/₂₂`),
     so rank is preserved by `rank_mul_eq_left/right_of_isUnit_det`, reducing to
     `rank (fromBlocks Δ 0 0 S) = card m ↔ S = 0`, where `S = B22 − B21·⅟Δ·B12`.
   - For the reduced block-DIAGONAL step I plan to prove additivity directly:
     `rank (fromBlocks Δ 0 0 S) = rank Δ + rank S` via the `toLin'`/`mulVecLin` direct-sum
     decomposition of the range (range of a ⊕-block-diagonal map is the product of ranges), then
     `rank Δ = card m` (Δ invertible) and `= card m ⟺ rank S = 0 ⟺ S = 0`.
2. **Parametrization bijection**: `{M ∈ Mat^{rk=r} | toBlocks₁₁ M invertible} ≃ GLₘ × Matrix m n × Matrix l m`
   (or as a `Set`-level characterization feeding the localized AlgEquiv), `M ↦ (Δ, B12, B21)` with B22 forced.
3. Chart dim `= δ` (if reachable).

## Questions for you (red-team the formulation, xhigh effort)
1. **Index convention.** Should the block lemma be stated abstractly over `m ⊕ l` / `m ⊕ n` sum types
   (general Fintype), or concretely with `Fin r ⊕ Fin (p−r)` and a `reindex` from `Fin p`? Which feeds the
   later LOCALIZED comorphism `AlgEquiv` more cleanly — i.e. when the entries become `MvPolynomial`
   variables and we localize at `det Δ`? The chart's coordinate ring is `k[entries][1/det Δ]`; the
   parametrization should make `Rt ≃ Rb ⊗ F_E` legible.
2. **Block-diagonal rank additivity.** Is proving `rank (fromBlocks Δ 0 0 S) = rank Δ + rank S` via the
   `mulVecLin`/range direct-sum decomposition the right lever, or is there a slicker path for JUST the iff
   `rank (fromBlocks Δ 0 0 S) = card m ↔ S = 0` given Δ invertible? (e.g. exhibiting `card m ≤ rank` always
   via a `card m × card m` invertible submatrix, plus `rank ≤ card m ⟺ S = 0`.) Which is less Lean friction?
3. **Should the deliverable be `Matrix`-level or coordinate-ring-level?** The thread says either the
   parametrization bijection OR the explicit coordinate ring of `Mat^{rk=r} ∩ U`. For feeding the
   localized Schur AlgEquiv in G2-3, is the `Equiv`/bijection on matrices enough, or do we need the
   ring presentation (`MvPolynomial quotient ≃ₐ localization`) already in this tile?
4. Any v4.29-specific landmine in `fromBlocks` rank work (the `Sum` Fintype/DecidableEq instances,
   `reindex` rank lemmas, `toLin'` vs `mulVecLin`)?

Give a concrete recommendation on (1) and (3) — the exact statement signature you'd commit to — and the
cleanest discharge for (2). Be skeptical: flag if the bijection-to-`GLₘ×Mat×Mat` is the wrong abstraction
for what G2-3 actually consumes.
