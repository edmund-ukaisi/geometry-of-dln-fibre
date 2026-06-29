# Strategic fork: closing the interior-det headline on `phiFlatLiveR1` (Lean 4 / Mathlib v4.29)

## Context

We want, sorry-free, the UNCONDITIONAL interior-determinant headline for a deep-linear-network
achiever chart `phiFlatLiveR1 : (Fin N → ℝ) → (Fin N → ℝ)` (N = `routeMAmbient M`, opaque in the width
tuple `M : Fin (L+1) → ℕ`):

  `|det (fderiv ℝ phiFlatLiveR1 u)| = |u_p|^{minAdm−1} · ∏_{s:Fin L} ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)} )`.

The chart is `phiGen = paramsEquivFlat M ∘ chartParamsGen`, where `chartParamsGen ⟨s⟩ = reindex (Agen s)`,
`Agen s = chainA(N_s, W_s, Cgen(s+1))` (a per-layer chain with a `−dN·W` bilinear shear coupling
adjacent layers). `paramsEquivFlat` is a measurable/linear reshape (Pi ≃ Pi).

## What is BANKED (sorry-free, clean)

1. `phiFlatLiveR1_differentiableAt` — the chart is differentiable; `diffAt_Agen` per layer.
2. Value-level locality at the `Agen` level: `Agen_genBlkFlatStruct_reads_le` — output layer `s` reads
   only input layers `≤ s` (one-sided dependency); plus per-reader/per-block `_indep_of` lemmas.
3. `fderiv_abs_det_eq_prod_diagBlocks` (NETWORK-FREE, UNCONDITIONAL): for any differentiable self-map
   `f` of `Fin N → ℝ` with `HasFDerivAt f D u` and a grading `g : Fin N → ℕ` such that
   `g i < g j ⟹ output coord i is invariant under changing input coord j`, then
   `|det D| = ∏_{a ∈ image (toDual∘g)} |(toMatrix' D).toSquareBlock (toDual∘g) a).det|`.
4. Engine diagonal-block dets: `radial_abs_det_minAdm` (radial block det = `|u_p|^{minAdm−1}`),
   `schurFrame_abs_det` (`|det (schurFrameDeriv X K N)| = |K.det|^{r+c}`),
   `lduCoreDeriv_abs_det` (`= ∏_i |q_i|^{2(t−1−i)}`).
5. Staircase machinery: `stairMap_abs_det_conj` (if `D = e.symm ∘ stairMap V (L+1) f c ∘ e` for a
   `LinearEquiv e : (Fin N → ℝ) ≃ₗ StairProd V (L+1)`, then `|det D| = ∏_s |det (f s)|`), and the
   headline wrapper `interiorDet_headline_of_stairConj` that splits radial layer 0 from boundary layers.
6. Two headline targets with IDENTICAL output formula:
   - `interiorDet_headline_of_blockTri`: takes `hbt : DFrame.BlockTriangular g` + per-grade
     `toSquareBlock` block-det identifications (`himg`/`hR`/`hB`) → headline. (locality route)
   - `interiorDet_phiFlatLiveR1_of_stairConj`: takes the staircase conjugacy `D.toLinearMap = e.symm ∘
     stairMap ∘ e` + `hR`/`hB` on `f` → headline. (staircase route)

## The fork

Both routes need, as their irreducible core, to IDENTIFY the per-layer diagonal-block determinant of the
opaque-width Jacobian with the engine values (radial = `|u_p|^{minAdm−1}`; boundary s = Schur⊗LDU).

The staircase route ADDITIONALLY requires constructing `V : ℕ → Type`, `f`, `c : StairCoupling`, and a
`LinearEquiv e : (Fin N → ℝ) ≃ₗ StairProd V (L+1)`, and proving the exact map identity
`(fderiv phiFlatLiveR1 u).toLinearMap = e.symm ∘ stairMap V (L+1) f c ∘ e`. This is over opaque
`Text`/`Wext` widths (dependent `Fin` reindex — historically the cost driver, cost prior tides).

The locality route AVOIDS the `e`/`f`/`c` construction: it needs
(a) lift the banked `Agen`-level value-locality to coordinate-level locality of `phiFlatLiveR1`
    (`phiFlatLiveR1 v i = phiFlatLiveR1 u i` whenever `v` agrees with `u` off a higher-bLayer coord `j`),
    then `fderiv_abs_det_eq_prod_diagBlocks` gives the product over `toSquareBlock (toDual∘bLayer)` blocks
    DIRECTLY — no equiv, no stairMap;
(b) `himg`: the image of the grading is `{0} ∪ {s+1}` (the radial + boundary layers);
(c) `hR`/`hB`: identify `(toMatrix' D).toSquareBlock (toDual∘g) a).det` with the engine values.

## Questions

1. Is there any reason the locality route (b)+(c) CANNOT close the unconditional headline that the
   staircase route can? I.e. is the staircase conjugacy genuinely required, or is it a strictly heavier
   path to the same identical output formula?

2. The hard part of BOTH routes is (c): identifying a `toSquareBlock`/`stairMap`-block determinant with
   the engine value over opaque widths. In the locality route, `(toMatrix' D).toSquareBlock g a` is the
   submatrix of partial derivatives `∂(output coord i)/∂(input coord j)` for `i,j` at grade `a`. To equate
   its det with the engine `schurFrameDeriv`/`lduCoreDeriv` det, I must show this submatrix is (conjugate
   to / equal to) the engine's block fderiv. Is identifying a `toSquareBlock` of `toMatrix' (fderiv …)`
   with a known small-matrix fderiv over opaque `Fin` widths likely to be LESS cast-painful than building
   a global `LinearEquiv e` and proving the global stairMap conjugacy? Or does the per-block
   `toSquareBlock` reindex (a `{i // g i = a} ≃ Fin (block width)` equiv per layer) reintroduce exactly
   the same dependent-Fin reindex pain?

3. Is there a THIRD option I'm missing: e.g. proving the per-layer block fderiv identification once as
   `HasFDerivAt (layer-restricted chart) (engine block deriv)` and assembling, sidestepping both the
   global equiv AND the toSquareBlock reindex?

Be concrete and skeptical. The goal is the least-cast path to the SAME unconditional sorry-free headline.
