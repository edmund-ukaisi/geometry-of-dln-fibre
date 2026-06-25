   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
OpenAI Codex v0.142.1
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim
model: gpt-5.1-codex-max
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019efd85-7c0a-7f52-aa68-08452f079a3c
--------
user
# Codex consult — brick 4: `IsUnit (chartPsiAeval ΔPdeep)` (Lean 4 / Mathlib v4.29)

## Goal
Prove `IsUnit (chartPsiAeval ΔPdeep)` in `Localization.Away gF`, where `gF` is a fixed element of a
poly ring. I want the **cleanest Lean route** for the matrix/determinant assembly — math is settled,
question is the slickest tactic-level decomposition.

## The setup (all LANDED, sorry-free)
- `ΔPdeep = det ((Matrix.of (multPoly d)).submatrix castLE castLE)` — det of the top-left r×r block
  of the p×q generic-product matrix `M := Matrix.of (multPoly d)` over a poly ring `MvPolynomial
  (RepCoord d) k`. (p = d last, q = d 0.)
- `chartPsiAeval : MvPolynomial (RepCoord d) k →ₐ[k] Away gF`.
- **Brick 2** (per-entry): `chartPsiAeval p = chartPsiTower (gaugeEquiv (endpointGauge⁻¹) (map
  (algebraMap k SchurLoc) p))`, where `chartPsiTower : MvPolynomial (RepCoord d) SchurLoc →ₐ[k] Away
  gF`.
- `gaugeEquiv_multPoly`: `gaugeEquiv d P (multPoly r c) = ((liftGauge d P last) · M_SL · (liftGauge d
  P 0)⁻¹) r c` over SchurLoc (M_SL = SchurLoc-version of M, via brick 1 `map_algebraMap_multPoly`).
- At `P = endpointGauge⁻¹`: `liftGauge(eg⁻¹) last = (liftGauge eg last)⁻¹ = (C-image of Lmat⁻¹)⁻¹ =
  C-image of Lmat`; `(liftGauge(eg⁻¹) 0)⁻¹ = liftGauge eg 0 = C-image of Hmat`. So gaugeEquiv(eg⁻¹)
  of multPoly = entry of `(C Lmat) · M_SL · (C Hmat)` over `MvPolynomial (RepCoord d) SchurLoc`.
- **Brick 3**: `chartPsiTower (map (algebraMap k SchurLoc) p) = algebraMap O(F) (Away gF) (mk_F p)`.
- Fibre fact (provable): `mk_F (multPoly a b) = normalForm a b` (mult = normalForm = diag(I_r,0) on
  the fibre F).
- Schur blocks over SchurLoc: `Lmat = reindex [[I,0],[B21Δ⁻¹,I]]`, `Hmat = reindex [[Δ,B12],[0,I]]`,
  `schurΔLoc` r×r with `det = detSchurS`-image, a UNIT (`isUnit_det_schurΔLoc`).
- `schurToGfib : SchurLoc →ₐ[k] Away gF`, and `chartPsiTower (C s) = schurToGfib s`.

## The reduction
`chartPsiAeval ΔPdeep = det (submatrix Mpsi castLE castLE)` (AlgHom.map_det + submatrix_map), where
`Mpsi := M.map chartPsiAeval`. Per-entry, `Mpsi rr cc = chartPsiTower((C Lmat · M_SL · C Hmat) rr
cc)`. Pushing the ring hom `chartPsiTower` through the matrix product:
`Mpsi = schurToGfib_mat(Lmat) · chartPsiTower_mat(M_SL) · schurToGfib_mat(Hmat)`,
and `chartPsiTower_mat(M_SL) = algebraMap-image of normalForm = E := diag(I_r,0)` over Away gF (brick
3 + fibre fact). So `Mpsi = L' · E · H'` where `L' = schurToGfib_mat(Lmat)`, `H' = schurToGfib_mat(Hmat)`,
both p×p / q×q, `E` p×q = diag(I_r,0).

I then need: `det (submatrix (L' · E · H') castLE castLE)` is a UNIT, where the submatrix takes the
top-left r×r block, `L' = reindex [[I,0],[*,I]]`, `H' = reindex [[Δ', B12'],[0,I]]` (Δ' = schurToGfib
of schurΔLoc, a unit), `E = reindex [[I_r,0],[0,0]]`.

## QUESTION
What is the cleanest Lean route to `det(submatrix (L'·E·H') castLE castLE) = (something unit)`?
Specifically: the top-left r×r block of `L'·E·H'`. Two candidate routes:

(A) **Reindex everything to the block split `Fin r ⊕ Fin (n−r)` and use `fromBlocks`.** Then `L'·E·H'`
in block coords = `[[I,0],[*,I]]·[[I,0],[0,0]]·[[Δ',B12'],[0,I]] = ...` and the (1,1) block computes
to `Δ'` by `fromBlocks_multiply`. The submatrix-castLE picks out the `Fin r` (= `Sum.inl`) block, so
`submatrix (...) castLE castLE = (block matrix).toBlocks₁₁ = Δ'`. Then `det Δ' = schurToGfib(detSchurS)`,
a unit via `IsUnit.map`. — Is there a clean lemma `submatrix M (castLE ∘ ...) = toBlocks₁₁` after a
`finSplit` reindex? How do `castLE` (into `Fin p`) and `finSplit hp : Fin p ≃ Fin r ⊕ Fin (p−r)`
compose — is `finSplit hp (castLE i) = Sum.inl i`? (There should be a lemma; `Lmat`/`normalForm` are
defined via `finSplit`, `normalForm = (fromBlocks 1 0 0 0).submatrix (finSplit hp) (finSplit hq)`.)

(B) **Avoid blocks: show the submatrix det directly equals `det Δ'`** via `det_mul`-style on
rectangular pieces — but `det_mul` needs square; `L'·E·H'` is p×q so `det` is not even defined on it.
The submatrix-of-product is the obstacle. Probably (A) is cleaner.

Please give: (1) which route, (2) the key Mathlib v4.29 lemmas (`finSplit` compose with `castLE`,
`submatrix_mul_equiv`, `fromBlocks_multiply`, `toBlocks₁₁`, `RingHom.map_det`/`AlgHom.map_det`,
`Matrix.submatrix_map`), (3) any traps with the reindex/submatrix interplay. Keep it to the matrix
algebra; assume bricks 1-3 + fibre fact are given as rewrites. ~40-60 LoC target.

warning: Model metadata for `gpt-5.1-codex-max` not found. Defaulting to fallback metadata; this can degrade performance and cause issues.
codex
**Recommendation**
- Go with route (A): reindex to `Fin r ⊕ Fin (p-r)` / `Fin r ⊕ Fin (q-r)`, use `fromBlocks` to compute the product, then identify the top-left block with your submatrix via the `finSplit`/`castLE` interaction. This keeps everything square where needed and reduces the goal to `det Δ'`, letting you finish with `AlgHom.map_isUnit`. ~40–60 LoC is realistic.

**Key lemmas & facts (Mathlib 4.29)**
- Block reindex:
  - `finSumFinEquiv` / `finSplit` give `Fin (r+(p-r)) ≃ Fin r ⊕ Fin (p-r)`.  
  - Compatibility: `finSumFinEquiv_symm_apply_left` (a.k.a. `finSumFinEquiv_symm_left`) says the left injection corresponds to `castLE`; so you get `finSumFinEquiv (castLE i) = Sum.inl i`. This is what identifies `castLE`-chosen rows/cols with the `11` block.
  - Reindexing matrices: `Matrix.reindex_linear_equiv` and `Matrix.reindex_apply` (`reindex_apply` reduces to `M (e.symm i) (f.symm j)`).
- Blocks:
  - Build: `Matrix.fromBlocks` / access: `Matrix.toBlocks` (`toBlocks₁₁`, `toBlocks₁₂`, …).
  - Multiplication: `Matrix.fromBlocks_multiply` (a.k.a. `fromBlocks_mul` with numbered subscripts) gives block product formulas.
  - Determinant of block-upper/lower-triangular: not needed since the `11` block becomes literally `Δ'`.
- Submatrix ↔ block:
  - `Matrix.submatrix` composed with the `finSumFinEquiv` reindex lets you prove  
    `submatrix M castLE castLE = (reindex ?e ?e M).toBlocks₁₁`. Typical proof:  
    ```
    ext i j; rfl  -- after rewriting with finSumFinEquiv_symm_apply_left
    ```
  - Helper lemma you can use/derive:  
    `by ext i j; rfl` after `simp [Matrix.submatrix, Matrix.toBlocks₁₁, Matrix.reindex_apply, finSumFinEquiv_symm_apply_left]`.
- Determinant functoriality: `AlgHom.map_det`, `RingHom.map_det`.
- Unit transport: `IsUnit.map` on `Δ'` with `schurToGfib` (or `chartPsiAeval`) once you have `det (submatrix …) = det Δ'` and `Δ'` unit (`isUnit_det_schurΔLoc.map`).

**Sketch of the clean Lean steps**
1. Set `eP := finSumFinEquiv` (or `finSplit hp`). Define `reL := Matrix.reindex eP eP L'`, etc., and similarly for `E`, `H'`.
2. Rewrite `L'`, `E`, `H'` via `fromBlocks` with shapes `(Fin r)` and `(Fin (p-r))`.
3. Compute the product using `fromBlocks_multiply`, obtaining `(reL.fromBlocks) ⬝ (reE.fromBlocks) ⬝ (reH.fromBlocks)`; the `11` block simplifies to `Δ'`.
4. Show `submatrix (L' ⬝ E ⬝ H') castLE castLE` is definitionally `(reindex eP eQ (L' ⬝ E ⬝ H')).toBlocks₁₁`; then rewrite the `toBlocks₁₁` of the block product to `Δ'` by `simp` with the block shapes (since off-diagonal zeros/identities kill the other terms).
5. Conclude `det _ = det Δ'`; finish with `exact (isUnit_iff_exists_inv).mp (IsUnit.map _ isUnit_det_schurΔLoc)`.

**Gotchas / simp tips**
- Use `simp [Matrix.submatrix, Matrix.reindex_apply, finSumFinEquiv_symm_apply_left]` to align indices.
- Keep shapes explicit: `simp` needs `(by omega)` proofs for `r ≤ p`, etc.; stash them as local lemmas.
- When rewriting `E`, ensure it is literally `fromBlocks 1 0 0 0`; `simp` will then collapse products.
- Make `Δ'` a square `r×r` matrix before taking `det`; avoid applying `det` to non-square blocks.
- Prefer `by classical exact` to open classical decidable eq instances for `simp` on `Fin`.

If you want, I can draft the ~50 LoC snippet with the exact `simp` set and the `submatrix_toBlocks₁₁` helper.
tokens used
3,917
**Recommendation**
- Go with route (A): reindex to `Fin r ⊕ Fin (p-r)` / `Fin r ⊕ Fin (q-r)`, use `fromBlocks` to compute the product, then identify the top-left block with your submatrix via the `finSplit`/`castLE` interaction. This keeps everything square where needed and reduces the goal to `det Δ'`, letting you finish with `AlgHom.map_isUnit`. ~40–60 LoC is realistic.

**Key lemmas & facts (Mathlib 4.29)**
- Block reindex:
  - `finSumFinEquiv` / `finSplit` give `Fin (r+(p-r)) ≃ Fin r ⊕ Fin (p-r)`.  
  - Compatibility: `finSumFinEquiv_symm_apply_left` (a.k.a. `finSumFinEquiv_symm_left`) says the left injection corresponds to `castLE`; so you get `finSumFinEquiv (castLE i) = Sum.inl i`. This is what identifies `castLE`-chosen rows/cols with the `11` block.
  - Reindexing matrices: `Matrix.reindex_linear_equiv` and `Matrix.reindex_apply` (`reindex_apply` reduces to `M (e.symm i) (f.symm j)`).
- Blocks:
  - Build: `Matrix.fromBlocks` / access: `Matrix.toBlocks` (`toBlocks₁₁`, `toBlocks₁₂`, …).
  - Multiplication: `Matrix.fromBlocks_multiply` (a.k.a. `fromBlocks_mul` with numbered subscripts) gives block product formulas.
  - Determinant of block-upper/lower-triangular: not needed since the `11` block becomes literally `Δ'`.
- Submatrix ↔ block:
  - `Matrix.submatrix` composed with the `finSumFinEquiv` reindex lets you prove  
    `submatrix M castLE castLE = (reindex ?e ?e M).toBlocks₁₁`. Typical proof:  
    ```
    ext i j; rfl  -- after rewriting with finSumFinEquiv_symm_apply_left
    ```
  - Helper lemma you can use/derive:  
    `by ext i j; rfl` after `simp [Matrix.submatrix, Matrix.toBlocks₁₁, Matrix.reindex_apply, finSumFinEquiv_symm_apply_left]`.
- Determinant functoriality: `AlgHom.map_det`, `RingHom.map_det`.
- Unit transport: `IsUnit.map` on `Δ'` with `schurToGfib` (or `chartPsiAeval`) once you have `det (submatrix …) = det Δ'` and `Δ'` unit (`isUnit_det_schurΔLoc.map`).

**Sketch of the clean Lean steps**
1. Set `eP := finSumFinEquiv` (or `finSplit hp`). Define `reL := Matrix.reindex eP eP L'`, etc., and similarly for `E`, `H'`.
2. Rewrite `L'`, `E`, `H'` via `fromBlocks` with shapes `(Fin r)` and `(Fin (p-r))`.
3. Compute the product using `fromBlocks_multiply`, obtaining `(reL.fromBlocks) ⬝ (reE.fromBlocks) ⬝ (reH.fromBlocks)`; the `11` block simplifies to `Δ'`.
4. Show `submatrix (L' ⬝ E ⬝ H') castLE castLE` is definitionally `(reindex eP eQ (L' ⬝ E ⬝ H')).toBlocks₁₁`; then rewrite the `toBlocks₁₁` of the block product to `Δ'` by `simp` with the block shapes (since off-diagonal zeros/identities kill the other terms).
5. Conclude `det _ = det Δ'`; finish with `exact (isUnit_iff_exists_inv).mp (IsUnit.map _ isUnit_det_schurΔLoc)`.

**Gotchas / simp tips**
- Use `simp [Matrix.submatrix, Matrix.reindex_apply, finSumFinEquiv_symm_apply_left]` to align indices.
- Keep shapes explicit: `simp` needs `(by omega)` proofs for `r ≤ p`, etc.; stash them as local lemmas.
- When rewriting `E`, ensure it is literally `fromBlocks 1 0 0 0`; `simp` will then collapse products.
- Make `Δ'` a square `r×r` matrix before taking `det`; avoid applying `det` to non-square blocks.
- Prefer `by classical exact` to open classical decidable eq instances for `simp` on `Fin`.

If you want, I can draft the ~50 LoC snippet with the exact `simp` set and the `submatrix_toBlocks₁₁` helper.
