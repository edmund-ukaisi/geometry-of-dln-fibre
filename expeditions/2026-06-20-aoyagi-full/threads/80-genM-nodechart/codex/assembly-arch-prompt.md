# Final assembly architecture — the unconditional interior-det headline (Lean 4 / Mathlib v4.29)

## Goal
Close, sorry-free over opaque widths `M : Fin (L+1) → ℕ`:
`|det (fderiv ℝ phiFlatLiveR1 u)| = |u_p|^{minAdm M − 1} · ∏_{s:Fin L} ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)} )`.

## Banked (all sorry-free, axiom-clean)
- `interiorDet_headline_of_twoStairConj` (route B target): given `D : E →ₗ E`, equivs `eIn eOut : E ≃ₗ
  StairProd V (L+1)`, the conjugacy `eOut ∘ D ∘ eIn.symm = stairMap V (L+1) f c`, the regauge
  `|det (eOut.symm ∘ eIn)| = 1`, `|det (f 0)| = |u_p|^{minAdm−1}`, `|det (f (s+1))| = engine value` ⟹ the
  headline. (`f 0` radial, `f (s+1)` boundary, `c` the det-irrelevant shears.)
- The full per-layer fderiv-VALUE chain: `hasFDerivAt_chainA`/`chainQ`/`Cgen_interior`/`_leaf`/
  `Agen_interior`/`_leaf` (the chart fderiv reduces per-layer to these).
- `schurFrameProd_block_K/_KN/_XK/_XKNuE`: `Cgen s = [[K,KN],[XK,XKN+uE]]` (the Schur frame value).
- Engine dets: `radial_abs_det_minAdm` (`|det (radialFactor active p).D u| = |u_p|^{minAdm−1}` given
  `p ∈ active`, `active.card = minAdm`); `schurFrame_abs_det` (`|det (schurFrameDeriv X K N)| =
  |K.det|^{r+c}`); `lduCoreDeriv_abs_det` (`= ∏|q_i|^{2(t−1−i)}`). All on their NATIVE spaces:
  `radialFactor.D` on `Fin N → ℝ`; `schurFrameDeriv` on `SchurInc t r c`; `lduCoreDeriv` on `LDUParam t`.
- `radialActive_exists` (`∃ active, structPivot ∈ active ∧ active.card = minAdm`).
- A `ChartFactor`/`composeFold` framework: `composeFold_abs_det (fs : List ChartFactor) … : |det (∏
  foldDerivList fs u)| = (m.prod)` — det of a COMPOSITION of full-ambient `(Fin N→ℝ)→L(Fin N→ℝ)` factors
  telescopes to the product of the per-factor dets.

## The decorrelated cert (pen-and-paper, exact at (2,2,2)/(3,3,3,3)/(2,3,2)/(4,3,3,2)/(3,4,3,3))
Mechanism: every chart output is `h_j(non-radial coords)` or `h_j(...) + u·r_i` where `r_i` = the free
scalar entries of all `u`-scaled `Rmat_k`(k≥1)/`Rfin_L` blocks (the E-block + leaf DOF), DISJOINT from the
K/X/N/W coords. So the Jacobian's `r_i`-columns each carry a `u` factor ⟹ `det Dφ = u^D · G`, `G` u-free,
`D = #{free u-scaled R entries}`. Separately (geometric) `1 + D = minAdm`. The radial blow-up
`pivotBlowupOn(active, pivot)` with `active = {pivot} ∪ {the r_i}` realizes this; det `u^{minAdm−1}`.
The boundary `G = ∏_s schurFrameDeriv·lduCore` (u-free). LOAD-BEARING (all ∀M-verified): K/X/N/W
u-independent; R-vars disjoint from K-core vars; u linear.

## The architectural question

TWO routes to the headline. Which is the least-cast for the Lean build over OPAQUE widths?

**Route B (the banked `twoStairConj` target):** construct `V : ℕ → Type` (`V 0` the radial space, `V (s+1)`
the per-boundary engine space), `f`, `c : StairCoupling`, `eIn eOut : (Fin N→ℝ) ≃ₗ StairProd V (L+1)`, prove
`eOut ∘ Dφ ∘ eIn.symm = stairMap V (L+1) f c` + `|det(eOut.symm∘eIn)|=1` + the per-layer dets. The
conjugacy is the hard part: it asserts the global fderiv, regrouped by eIn/eOut, is EXACTLY the abstract
block-staircase `stairMap` (with `f 0` radial, `f(s+1)` = `schurFrameDeriv∘lduCore`, `c` the `−dN·W` shears).

**Route A (composeFold / det-factorization):** prove `det Dφ = |u|^D · G` DIRECTLY via the `u`-column-pull
(the cert's mechanism), with `D = minAdm−1` (count) and `G = ∏ boundary` (engine id). Either as a map
composition `phiFlatLiveR1 = composeFold [radial, shear, frames]` (needs map value-equality — Codex
earlier flagged this as ≥ the eIn/eOut cast cost), OR as a pure det-level factorization
`det Dφ = det(radial col-pull) · det(rest)` proven by the column-factoring lemma (no map equality).

Questions:
1. Is there a clean Lean lemma for "det of a matrix where a known set of COLUMNS each carry a common
   scalar factor `u` = `u^(#cols) · det(matrix with those columns divided by u)`"? (i.e. `Matrix.det`
   column-homogeneity / `det_updateColumn_smul` iterated.) If so, route A's det-level factorization avoids
   BOTH the abstract `stairMap` AND the map composition — directly `det Dφ = u^D · det(G-matrix)`, then
   identify `det(G-matrix)` with the engine. Is this the least-cast spine?
2. For route B: the conjugacy `eOut ∘ Dφ ∘ eIn.symm = stairMap` is a LINEAR MAP equality over opaque
   widths. Is proving it (entrywise / blockwise) likely MORE cast-heavy than route A's column-factor +
   per-boundary `det` identification? The `stairMap` is a nested `lowerTri`; matching `Dφ`'s regrouped
   blocks to it needs the eIn/eOut to exactly realize the radial/boundary/shear split.
3. The per-boundary engine identification (`G`'s s-th block det = `|K_s|^{r_s+c_s}·∏|q|^{...}`) is needed
   in BOTH routes. Given `schurFrameProd_block_*` (the Cgen=Schur-frame VALUE) + `schurFrame_abs_det` +
   `lduCoreDeriv_abs_det` are banked, what is the cleanest bridge from "the s-th diagonal block of Dφ
   (in the regrouped coords)" to "det = the engine value"? A per-boundary `LinearEquiv` (output block ≃
   SchurInc) conjugating the block fderiv to `schurFrameDeriv∘lduCore`?
4. Should I DELEGATE: spawn parallel formaliser sub-agents for (radial f0 + det), (per-boundary f(s+1) +
   engine id), (eIn/eOut coordinatization), while I drive the conjugacy assembly + headline? Or is the
   coupling through the V/eIn/eOut choices too tight for clean parallelism — build serially?

Rank routes A vs B by cast-risk for the OPAQUE-width Lean build; name the least-cast concrete spine + the
first 2 bankable lemmas to build. Be concrete and Lean-v4.29-specific.
