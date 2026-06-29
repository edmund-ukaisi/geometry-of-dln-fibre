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

## Sub-piece 1c BANKED (this leg) — `Cgen`/`Agen` fderiv VALUES
`lean/DLNFibre/DLN/RLCT/Validate/RouteMAgenFDerivValue.lean` (sorry-free, clean-three, axiom-clean, zero
warnings): `hasFDerivAt_Cgen_interior` (`Bmat·chainQ + u•Rmat` via `HasFDerivAt.matMul` + `hasFDerivAt_chainQ`,
`.add`, `HasFDerivAt.smul`), `hasFDerivAt_Cgen_leaf` (`u•Rfin`), `hasFDerivAt_Agen_interior` (via
`hasFDerivAt_chainA`), `hasFDerivAt_Agen_leaf` (const `0`). GENERIC in the block fderivs (hypotheses) — the
live-decoder block fderiv VALUES discharge them at the wiring stage. Cast notes: `HasFDerivAt.matMul` must
be called by NAME (dot-notation hits `HasFDerivAtFilter.matMul`); the leaf `0` fderiv needs the CLM type
ascribed (`(0 : … →L[ℝ] …)`) or the `Module` instance is stuck.

## NEXT concrete step — the ENGINE IDENTIFICATION (Codex engine-id consult, xhigh; artefacts
`threads/80-genM-nodechart/codex/engine-id-{prompt,answer}.md`)

Decorrelated design for recognizing `Agen s`'s fderiv as the engine block:

- **Least-risk next bank (Codex rank-4, do FIRST):** the MATRIX VALUE identity `Cgen s = Schur frame`.
  Define `frameOut : Matrix (Fin (Text s)) (Fin (Wext s)) ℝ ≃L SchurInc t r c` (the output block split, SAME
  row/col orientation as `bmatStack`/`rmatPad`/`chainQ`), and prove
  `frameOut (Cgen u … s) = schurFrameMap (K_s, N_s, X_s, u•E_s)` i.e. `Bmat·chainQ + u•Rmat =
  [[K,KN],[XK,XKN+uE]]`. Proof grain: **per-block theorem statements, per-entry proofs INSIDE** (do NOT
  one giant `ext i j` over opaque `Fin (Text s)`). Four block lemmas (K / KN / XK / XKN+uE) via the banked
  accessors `bmatStack_top`/`_bot`, `chainQ_apply_castAdd`/`_natAdd`, `rmatPad_*_*` (+ `fromBlocks`), each
  closed with `Matrix.mul_apply` over the `chainQ`/`bmatStack` splits.
- **K-slot adapter (avoid a Matrix/LDUParam mismatch):** use `FrameParam t r c := LDUParam t × (Matrix (Fin
  t)(Fin c) × (Matrix (Fin r)(Fin t) × Matrix (Fin r)(Fin c)))` as `V (s+1)` (NOT raw `SchurInc`), with a
  local CLE `FrameParam ≃L SchurInc` (`matrixSplit.symm` on the K slot, id elsewhere). The engine block is
  then the conjugated `raw.symm ∘ schurFrameDeriv X K N ∘ raw ∘ (lduCoreDeriv on K-slot, id elsewhere)` —
  the conjugation cancels in det. Safer than pretending `LDUParam`/`Matrix` interchange.
- **Fderiv identification** then becomes a chain-rule/congruence problem one boundary at a time (local
  input/output coordinate equivs first, assemble globally) — NOT a global reindex fight.

**Codex cast-risk ranking** (highest→lowest), to sequence the remaining sub-pieces:
1. Global `eIn`/`eOut` into dependent `StairProd V` — DO NOT hand-build from `Fin N`; compose the existing
   spine (`paramsEquivFlatCLE`, `chartIdxEquiv`, `frameSplitEquiv`, local matrix/tuple split CLEs).
2. Output-side `Agen`→staircase wiring (chain shears + the `s`/`s+1` shift).
3. K-slot raw-matrix vs `LDUParam` coordination (solved by the `FrameParam` adapter above).
4. `Cgen = Schur frame` value identity over opaque widths ← **DONE** (`RouteMSchurValue.lean`).
5. Boundary fderiv identification after the value identity — ENTANGLED with the radial separation (see
   the `u`-factoring finding below); needs the #1 `eIn`/`eOut` design first.
6. Determinant computations once the maps type.

## Sub-piece #4 BANKED (this leg) — `Cgen s = Schur frame` matrix VALUE identity
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurValue.lean` (sorry-free, clean-three, axiom-clean, zero
warnings): `schurFrameProd` (the abstract `bmatStack(K,X)·chainQ(N) + u•rmatPad(E)`) + the four block
lemmas `schurFrameProd_block_K`/`_KN`/`_XK`/`_XKNuE` (`= K`, `K·N`, `X·K`, `X·K·N + u·E`). Per-block
statements, per-entry proofs via `bmatStack_top`/`_bot` + `chainQ_apply_castAdd`/`_natAdd` (wrapped as
private `chainQ_left`/`_right`, threading `h2`) + `rmatPad_*_*` + `Matrix.mul_apply` / `Finset.sum_eq_single`
to collapse the `1`-boole chaining sum. No global `ext` over opaque widths.

## STRUCTURAL FINDING (verified vs the banked `(2,2,2)` det) — the `u`-factoring, before #5/#1
Comparing `schurFrameProd`'s differential (blocks `K`,`KN`,`XK`,`XKN+u·E`) to the engine
`schurFrameDeriv X K N (dK,dN,dX,dE) = (dK, K·dN+dK·N, dX·K+X·dK, dE + X·dK·N + X·K·dN + dX·K·N)`: the
first three blocks MATCH, but the chart's bottom-right E-term is `u·dE` vs the engine's `dE`. Naively this
would add a per-boundary `u^{r_s·c_s}` to the det. **It does NOT** — verified against the banked `(2,2,2)`:
`phi222_abs_det = |u0|²·|u4|` with `minAdm=3` so radial `=|u0|^{minAdm−1}=|u0|²`, boundary `=|u4|=|K|^{r+c}`
(`r=c=1`), and NO extra `|u0|^{r·c}=|u0|¹` factor. The reason (read off `T222Deriv`): the chart factors as
`(single multi-coord radial pivot-blowup, det u^{minAdm−1} = u^{card−1} over `minAdm` activated coords)
∘ shear (det 1) ∘ (per-boundary Schur frames, det |K|^{r+c}, u-FREE)`. The radial `u` is a SINGLE blow-up
direction (`pivotBlowupOnDeriv_det = (x p)^{card−1}`), NOT distributed as `u·E` per boundary in the
det-relevant way; the `u·E` in `Cgen` is reparametrized into the radial layer.

**Consequence for the staircase `V`/`f`:** the radial layer `f 0` (det `|u|^{minAdm−1}`) and the boundary
layers `f (s+1) = schurFrameDeriv ∘ (LDU on K)` (det `|K_s|^{r_s+c_s}·∏|q|^{…}`, u-FREE) are SEPARATED by
the `eIn`/`eOut` regrouping. So #5 (boundary fderiv id) is ENTANGLED with the radial separation that #1
(global `eIn`/`eOut`) provides — the `u·E` must land in the radial layer, not the boundary block. This is
why #1 must be designed before #5 can be stated cleanly (matches the coordinator's "eyes on #1 first").

Staircase two-sided conjugacy CONFIRMED (again) as the sound assembly; the `det_comp` bypass is not easier
(it needs value equality of the whole nonlinear map — the same/worse cast cost).

## BUILD-READY #1 SPEC (genm-detradj radial-model cert, exact at (2,2,2)/(3,3,3,3)/(2,3,2) + Codex)
Cert scripts: `origin/worktree-agent-a29183139e1c0384f`, `pnp-radial-adjudication/` (`pnp_final_cert.py`,
`pnp_branch_distinction.py`, `pnp_u_linear.py`). The radial model is PINNED — corrects my earlier sketch:

- **`V 0 = ℝ^minAdm`** (NOT `ℝ`). `active = {structPivot} ∪ {ALL free entries of the u-scaled Rmat_k
  (k≥1) + Rfin_L}` — the E-block + leaf DOF, SPREAD across boundaries. `f 0 = pivotBlowupOn(active,
  structPivot)`, `|det f 0| = |u|^{minAdm−1}` via `radial_abs_det_minAdm` + `active.card = minAdm` (the
  count is the BANKED `leafH = minAdm−1`, NOT re-derived per-M). The radial-blowup model is
  `pbon(active,p,vec) i = vec[p]` (i=p) / `vec[p]·vec[i]` (i∈active) / `vec[i]` (else).
- **CRITICAL: `active ≠ deepestCoords`** (that's the CLEAN branch). INTERIOR branch they DIFFER:
  (2,2,2) active `{0,6,7}` card 3 ≠ deepest A_1 dim 4; (3,3,3,3) active `{0,13,14,24,25,26}` card 6 ≠
  deepest A_2 dim 9. Build `active = {pivot} ∪ {R/Rfin free DOF}`, NOT a single layer's coords.
- **`eIn` (input, from `chartIdx`):** regroup `ChartIdx → V 0 = radial DOF (pivot + R/Rfin free, INCLUDING
  the E-entries)`, `V(s+1) = K/X/N only` (u-FREE). NOTE the E-DOF routes into `V 0`, NOT `V(s+1)` — so
  `V(s+1)` is `K/X/N`, NOT the full `FrameParam`-with-E my earlier sketch had.
- **`eOut` (output, from `paramsFlat`):** regroup `FlatIdx`; `|det(eOut.symm∘eIn)| = 1` (two-sided,
  partitions differ); the shear `c` absorbs the mismatch (the `−dN·W` + the additive `C_{k+1}`).
- **`f(s+1) = schurFrameDeriv ∘ lduCore`, u-FREE**, `|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)}`.
  `∏_s` = the headline ∀M.
- **LOAD-BEARING hypotheses to SUPPLY** (all machine-verified in the cert): (i) `Bmat`/`Nblk`/`Wblk`/K-core
  u-independent; (ii) `R`/`Rfin` DOF disjoint from the other coords; (iii) `u` linear (no `u·x_j·x_k`) —
  holds because `C_{k+1}` enters `A_k` only ADDITIVELY via `C_{k+1} − N_k·W_k` (`pnp_u_linear.py`:
  max u-degree 1, no `u·(2+ free coords)`).

HOLD: one final backstop pending (genm-detradj's 4th tuple, wide interior both-drop e.g. (3,4,3,3),
confirming `structPivot` is never inside a K-core — would reshape the `eIn` routing if it breaks).

## Reusable for the residual (banked this leg + prior)
- This leg: `hasFDerivAt_chainA` / `hasFDerivAt_chainQ` (the per-layer fderiv-value atoms),
  `hasFDerivAt_Cgen_interior`/`_leaf` + `hasFDerivAt_Agen_interior`/`_leaf` (the threaded chain-layer
  fderiv values), `schurFrameProd_block_K`/`_KN`/`_XK`/`_XKNuE` (the `Cgen = Schur frame` value blocks),
  `stairMap_abs_det_twoConj` (the det once `eIn`/`eOut`/`f`/`c` are exhibited),
  `interiorDet_headline_of_twoStairConj` (the headline wrapper for the rectangular layout).
- Prior: `stairMap_abs_det_conj` (single-`e`), `interiorDet_phiFlatLiveR1_of_stairConj` (the real-chart
  target), `fderiv_det_one_of_shear` (the `−dN·W` shear is det-1), `finSplit.symm` cast lemmas,
  `chainA_apply_castAdd/natAdd`, `phiFlatLiveR1_differentiableAt(_of_Agen)`, `diffAt_Agen`,
  `radial_abs_det_minAdm`, `schurFrame_abs_det`, `lduCoreDeriv_abs_det`.
