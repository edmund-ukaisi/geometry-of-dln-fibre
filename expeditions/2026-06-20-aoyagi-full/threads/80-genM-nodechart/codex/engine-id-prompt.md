# Engine identification design — Agen s fderiv = schurFrameDeriv ∘ lduCoreDeriv ⊞ shear (Lean 4 / Mathlib v4.29)

## Context (what is banked)

Building the opaque-`M` fderiv-as-staircase decomposition of a deep-linear-network achiever chart
`phiFlatLiveR1 : (Fin N → ℝ) → (Fin N → ℝ)`. The fderiv reduces (banked) per layer `s : Fin L` to the
fderiv of the chain layer `Agen s`. I have now banked, sorry-free over OPAQUE `Text`/`Wext` widths:

- `hasFDerivAt_chainA` / `chainAFDeriv` : fderiv VALUE of `chainA h N W C = [C−N·W ; W]` (kept block the
  product-rule differential of `C−N·W`, lift block `dW`).
- `hasFDerivAt_chainQ` / `chainQFDeriv` : fderiv VALUE of `chainQ h N = [I | N]`.
- `hasFDerivAt_Cgen_interior` : `Cgen k = Bmat k · chainQ(Nblk k) + u • Rmat k` fderiv (matMul + smul).
- `hasFDerivAt_Agen_interior` : `Agen k = chainA(Nblk k, Wblk k, Cgen(k+1))` fderiv (via chainA atom).

Key cast lever that works: take fderiv VALUES per-entry (each lands in ℝ, always normed) — the
reindex-as-CLE route stalls on Sum-indexed intermediates (no norm instance).

## The engine (banked, network-free, abstract)

The per-boundary Schur frame is `S(X,K,N,E) = [[K, K·N],[X·K, X·K·N + E]]`. Its differential is
`schurFrameDeriv X K N : SchurInc t r c →ₗ SchurInc t r c` where
`SchurInc t r c = Matrix (Fin t) (Fin t) × (Matrix (Fin t) (Fin c) × (Matrix (Fin r) (Fin t) × Matrix (Fin r) (Fin c)))`
(the increment tuple `(dK, dN, dX, dE)`), a 3-fold nested `lowerTri`. `|det (schurFrameDeriv X K N)| =
|K.det|^(r+c)` (`schurFrame_abs_det`). The LDU core `lduCoreDeriv l q u : LDUParam t →ₗ LDUParam t`
(`LDUParam t = (LowIdx t → ℝ) × (Fin t → ℝ) × (UpIdx t → ℝ)`) has `|det| = ∏_i |q_i|^{2(t−1−i)}`.

## The structural fact (verified on paper)

The chart's `Cgen s` value IS the Schur frame: `Bmat_s = bmatStack(K_s, X_s) = [K_s ; X_s·K_s]`,
`chainQ(N_s) = [I | N_s]`, `Rmat_s = rmatPad(E_s) = [[0,0],[0,E_s]]`, so
`Cgen s = Bmat_s · chainQ(N_s) + u·Rmat_s = [[K, K·N],[X·K, X·K·N + u·E]] = S(X, K, N, u·E)`.
The chart's `K_s` is itself the LDU core (so `K_s` reads through `lduCoreDeriv`); `X_s, N_s, E_s` are
free reader blocks.

So per layer `s`, the diagonal staircase block `f (s+1)` should be `schurFrameDeriv X_s K_s N_s ∘
(lduCoreDeriv on the K-slot)`, with det `|K_s.det|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)}`. The off-diagonal
`−dN·W` chain shears are the staircase couplings (det-irrelevant).

## The goal

Express `(fderiv phiFlatLiveR1 u).toLinearMap = eOut.symm ∘ stairMap V (L+1) f c ∘ eIn` (two-sided form,
`|det(eOut.symm∘eIn)|=1`), with `f 0` the radial blow-up and `f (s+1)` the engine block above, then feed
the banked `interiorDet_headline_of_twoStairConj` to get the unconditional headline.

## Questions (be concrete, skeptical, Lean-v4.29-specific)

1. **The cleanest intermediate to bank next.** Is it (a) a MATRIX identity `Cgen s = schurFrameValue X_s K_s N_s (u·E_s)` (define `schurFrameValue` = the [[K,KN],[XK,XKN+E]] block matrix via fromBlocks), then separately (b) `HasFDerivAt (Cgen s) (schurFrameDeriv … ∘ readers)`? Or go straight to the fderiv identification? The matrix identity (a) is over opaque `Text`/`Wext` widths with the `bmatStack`/`rmatPad`/`chainQ` reindexes — is proving it via the banked block-accessor lemmas (`bmatStack_top`/`_bot`, `chainQ_apply_castAdd/natAdd`, the `rmatPad` fromBlocks) per-block, or per-entry, the right grain?

2. **Identifying the chart's fderiv with `schurFrameDeriv`.** `schurFrameDeriv` lives on the abstract
   `SchurInc` increment space; my `Cgen` fderiv lives on `Matrix (Fin (Text s)) (Fin (Wext s)) ℝ` (the
   output) with input `Fin N → ℝ`. To equate them I need (i) an equiv `SchurInc t_s r_s c_s ≃ₗ (the chart's
   boundary-s output block)` and (ii) the chart's reader CLMs to factor as `(SchurInc-coordinate-reads) ∘
   eIn-block`. Is the right move to make `eIn`/`eOut` per-boundary equivs `Matrix block ≃ₗ SchurInc`, and
   prove the fderiv identity BLOCK-BY-BLOCK (one `s` at a time) rather than globally? Does `schurFrameDeriv`
   being a `lowerTri` nest help (match it against my `chainAFDeriv`'s kept/lift structure directly)?

3. **Is the staircase `stairMap V (L+1) f c` the right target, or should I bypass it?** The det I need is
   `∏_s |det (f s)|`. `stairMap_abs_det_twoConj` gives that from the conjugacy. But an ALTERNATIVE: prove
   `HasFDerivAt (Agen s) Ds` with `|det (Ds-restricted-to-diagonal)| = engine value` per layer, and assemble
   the global det via the BANKED `fderiv_abs_det_eq_prod_diagBlocks` (locality) — wait, that route was
   refuted (the row/col partition mismatch). Confirm the staircase two-sided conjugacy is still the only
   sound assembly, OR is there a per-layer `HasFDerivAt`-then-`LinearMap.det_comp` telescoping that avoids
   building the global `eIn`/`eOut` equiv at all (e.g. the chart fderiv = a composition of per-layer block
   maps, det = ∏ via det_comp, each factor's det = engine value)?

4. **The `V`/`f`/`c` types over opaque widths.** `V (s+1) = SchurInc t_s r_s c_s` (with `t_s = Text(s+1)`,
   `r_s = Text s − Text(s+1)`, `c_s = Wext s − Text(s+1)`), `V 0 = ℝ` (radial). `StairProd V (L+1)` is the
   nested product. Is building the layer-collecting `eIn`/`eOut : (Fin N → ℝ) ≃ₗ StairProd V (L+1)` —
   matching the flat coords to the per-layer `SchurInc` tuples over opaque widths — likely the single
   biggest cast cost? Any idiom to make that equiv cheaply (compose `paramsEquivFlatCLE` with per-layer
   `frameSplitEquiv`-style role splits)?

Rank the sub-pieces by cast-risk and give the least-risk next bankable target.
