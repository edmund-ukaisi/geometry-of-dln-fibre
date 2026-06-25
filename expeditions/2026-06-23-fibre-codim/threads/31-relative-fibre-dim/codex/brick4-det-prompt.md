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
