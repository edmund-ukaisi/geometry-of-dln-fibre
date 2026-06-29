# Statement card — two-sided staircase det wrapper + the sharpened fderiv-value residual, `genm-detfderiv`

Branch `genm-detfderiv` (off `genm-detbridge`). This leg made the ROUTE DECISION (decorrelated Codex,
xhigh) for the lone remaining residual of the interior-det headline — the opaque-`M` fderiv-as-staircase
construction — and banked the network-free wrapper layer the construction feeds. The genuinely-new
opaque-`M` fderiv-VALUE construction itself is NOT closed (it is the large multi-tide cast zone the brief
flags); this card sharpens it into bankable sub-pieces.

## The route decision (decorrelated, Codex xhigh)

Artefact: `threads/80-genM-nodechart/codex/detfderiv-route-{prompt,answer}.md` (prompt at
`/tmp/codex-route-consult.md` reproduced into the thread). A tempting shortcut was found and REFUTED:

- **Locality route REFUTED for the real chart.** `RouteMLocalityDet.fderiv_abs_det_eq_prod_diagBlocks`
  gives `|det D| = ∏ |toSquareBlock (toDual∘g) a|` UNCONDITIONALLY from value-locality `hloc`. It looked
  like it bypassed the `e`/`f`/`c` construction. It does NOT: `fderiv_abs_det_eq_prod_diagBlocks` needs
  ONE grading `g` for BOTH rows and columns, but the real chart's row partition (`FlatIdx`, layer sizes
  `M_s·M_{s+1}`) and column partition (`ChartIdx`, boundary sizes `schurDim+liftDim`) genuinely DIFFER —
  the banked `RouteMGradingObstruction.flatLayer_ne_chartBoundary_222` (`(4,4)` rows vs `(6,2)` cols at
  `(2,2,2)`). A single `g` cannot grade both. And `toSquareBlock g a` indexes rows and cols by the SAME
  subtype, so comparing it to the engine `schurFrameDeriv`/`lduCoreDeriv` block (different row/col stories)
  reintroduces the per-block dependent-`Fin` reindex — WORSE than the staircase, not better.
- **Staircase route CONFIRMED**, with the refinement: a **two-equivalence wrapper**
  `eOut ∘ D ∘ eIn.symm = stairMap` (separate input/output regroupings, `|det(eOut.symm ∘ eIn)| = 1`)
  is less artificial than forcing one `e` to serve both partitions. Best assembly: per-layer `HasFDerivAt
  (boundaryRestrictedChart s) (engine block deriv)`, glued into the conjugacy.

## Banked this leg (sorry-free, clean-three, forced `#print axioms`)

- `lean/DLNFibre/DLN/RLCT/Validate/RouteMStairTwoSided.lean`
  - `stairMap_det_twoConj` — `det D = det (eOut.symm ∘ eIn) · ∏_s (f s).det` from
    `eOut ∘ D ∘ eIn.symm = stairMap V n f c`. Proof: `det` is endo-only, so rewrite `D` as the product of
    TWO endos of `E` — the conjugate `eOut.symm ∘ stairMap ∘ eOut` (det = det stairMap by `det_conj`) and
    the regauge `eOut.symm ∘ eIn` — then `det_comp` + `stairMap_det`.
  - `stairMap_abs_det_twoConj` — the `|·|` form: `|det D| = ∏_s |(f s).det|` given the regauge abs-det-`1`.
  - Non-vacuity: the single-`e` (`eIn = eOut`) special case recovers `stairMap_abs_det_conj`.
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMStairTwoSidedHeadline.lean`
  - `interiorDet_headline_of_twoStairConj` — the SAME interior-det headline output formula
    `|det D| = |u_p|^{minAdm−1}·∏_s(|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)})`, now from the two-sided
    conjugacy + regauge-det-`1` + the radial/boundary engine identifications (`Fin.prod_univ_succ` split).
  - Non-vacuity: fires on a concrete `L=1` frame with a genuinely DISTINCT `eIn ≠ eOut` (det-`1` `eIn`,
    `eOut = refl`).
- Axioms: all four results `[propext, Classical.choice, Quot.sound]` (determinant; no analysis).

These are the NETWORK-FREE wrapper the genuine construction feeds. NOT wired into `DLNFibre.lean` (the
controller wires at leg-close).

## The sharpened residual (still open — the opaque-`M` fderiv VALUE)

Feed `interiorDet_phiFlatLiveR1_of_stairConj` (single-`e`, banked) OR the new
`interiorDet_headline_of_twoStairConj` (two-sided) by constructing, over opaque `Text`/`Wext` widths:

1. **`V : ℕ → Type`** — layer spaces. Layer `0` = the radial scalar direction (`ℝ`); layer `s+1` = the
   per-boundary engine product type (the `SchurInc t_s r_s c_s` / `LDUParam`-style nested product carrying
   `K_s`, `X_s`, `N_s`, the leaf). `[FiniteDimensional]` instances per layer.
2. **`f : (s:ℕ) → V s →ₗ V s`** — diagonal blocks. `f 0` = the radial blow-up (det `|u_p|^{minAdm−1}`,
   `radial_abs_det_minAdm`); `f (s+1)` = `schurFrameDeriv X_s K_s N_s ∘ lduCoreDeriv …` (det the engine
   `|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{…}`, `schurFrame_abs_det × lduCoreDeriv_abs_det`).
3. **`c : StairCoupling V (L+1)`** — the `−dN_s·W_s` bilinear shears (det-irrelevant; the couplings drop).
4. **`eIn`/`eOut`** — the input/output regroupings of `Fin (routeMAmbient M)` into `StairProd V (L+1)`.
   `eOut = (regroup FlatIdx into layers) ∘ paramsEquivFlatCLE.symm`; `eIn = regroup ChartIdx (radial slot +
   per-boundary reader slots) into layers`. The regauge `eOut.symm ∘ eIn` is a coordinate permutation
   (abs-det `1`).
5. **`hconj`** (the load-bearing identity): `(fderiv ℝ phiFlatLiveR1 u).toLinearMap = e.symm ∘ stairMap ∘ e`
   (single-`e`) or `eOut ∘ D ∘ eIn.symm = stairMap` (two-sided). Via `phiFlatLiveR1_differentiableAt_of_Agen`
   the fderiv reduces per-layer to `fderiv (Agen s)`; the per-layer fderiv VALUE is the unbuilt core.

### Codex-endorsed assembly order (least-cast)
Build the per-layer atom FIRST: `HasFDerivAt (fun x => Agen … s) (engine-block-deriv ⊞ shear) u` for one
layer `s`, over opaque `Fin (Wext)` widths — the `chainA(N_s, W_s, Cgen(s+1))` fderiv = the Schur⊗LDU
diagonal block (det = engine value) PLUS the `−dN·W` shear (det-1). The `(2,2,2)` `shear222`/`Frame222` and
`(3,3,3,3)` `Frame3333Deriv` are the concrete templates (both fully-explicit `Fin 8`/`Fin 27`); the work is
generalizing the per-piece factorization `DFrame = F_radial · ∏ F_s` to opaque widths. Then `eIn`/`eOut`
collect the layers and the couplings absorb the partition mismatch (the `StairFold` docstring's mechanism).
This is the dependent-`Fin` `Matrix.of`/reindex cast zone the CLAUDE.md gotchas + memory notes flag as the
cost driver — genuinely multi-tide.

## Sub-piece 1 PROGRESS (banked this leg — the per-layer fderiv-VALUE atoms)

`lean/DLNFibre/DLN/RLCT/Validate/RouteMChainFDerivValue.lean` (sorry-free, clean-three, forced
`#print axioms` `[propext, Classical.choice, Quot.sound]`, zero warnings, non-vacuity in-file):
- `chainAFDeriv` / `hasFDerivAt_chainA` — the fderiv VALUE of a `chainA` layer (the `[C−N·W ; W]` lift
  column) over OPAQUE `Fin (Wext)` widths: kept entries the product-rule differential of `C−N·W`
  (`HasFDerivAt.matMul`'s `precompR`/`precompL`), lift entries `dW`. Per-entry assembly
  (`hasFDerivAt_pi''` ×2 + `finSplit` kept/lift split + `chainA_apply_castAdd`/`_natAdd`), dodging the
  Sum-indexed no-norm wall exactly as `diffAt_chainA` does.
- `chainQFDeriv` / `hasFDerivAt_chainQ` — the fderiv VALUE of a `chainQ` layer (the `[I | N]` chaining
  row): kept columns the constant `I` (fderiv `0`), lift columns `dN`. Same column-split assembly.

The KEY cast lesson (re-confirmed): get the fderiv VALUE PER-ENTRY (each lands in `ℝ`, always normed) —
the `reindex`-as-CLE route stalls on the Sum-indexed intermediate (no norm instance), per `diffAt_chainA`'s
note. `ContinuousLinearMap.proj_pi` is `rfl`, so `(proj j).comp ((proj r).comp (clmPi …))` reduces to the
per-entry coordinate by `rw [… from rfl]` before the `finSplit` case split.

## NEXT concrete step (sub-piece 1, continued)
Thread the two atoms up: `Cgen` fderiv-value (`Cgen k = Bmat k · chainQ(Nblk k) + u • Rmat k` interior,
`u • Rfin` leaf) via `HasFDerivAt.matMul`/`.add`/`.smul` + `hasFDerivAt_chainQ`; then `Agen` fderiv-value
(`= chainA(Nblk s, Wblk s, Cgen(s+1))`) via `hasFDerivAt_chainA`. This needs the live-decoder block
fderiv VALUES (`Bmat`/`Nblk`/`Wblk`/`Rmat`/`Rfin` of `genBlkFlatLiveR1`) — reader fderivs are projection
CLMs; the `Rmat` `Function.update` + `Rfin` `dite` are cased as in `diffAt_liveRmat`/`_Rfin`; the radial
`u = x p₀` read is `differentiableAt_apply`. Then the ENGINE IDENTIFICATION (recognizing the assembled
`Agen s` fderiv as `schurFrameDeriv ∘ lduCoreDeriv ⊞ shear`) + the `eIn`/`eOut`/`V`/`f`/`c` assembly
remain (sub-pieces 2–5).

## Reusable for the residual (banked this leg + prior)
- This leg: `hasFDerivAt_chainA` / `hasFDerivAt_chainQ` (the per-layer fderiv-value atoms),
  `stairMap_abs_det_twoConj` (the det once `eIn`/`eOut`/`f`/`c` are exhibited),
  `interiorDet_headline_of_twoStairConj` (the headline wrapper for the rectangular layout).
- Prior: `stairMap_abs_det_conj` (single-`e`), `interiorDet_phiFlatLiveR1_of_stairConj` (the real-chart
  target), `fderiv_det_one_of_shear` (the `−dN·W` shear is det-1), `finSplit.symm` cast lemmas,
  `chainA_apply_castAdd/natAdd`, `phiFlatLiveR1_differentiableAt(_of_Agen)`, `diffAt_Agen`,
  `radial_abs_det_minAdm`, `schurFrame_abs_det`, `lduCoreDeriv_abs_det`.
