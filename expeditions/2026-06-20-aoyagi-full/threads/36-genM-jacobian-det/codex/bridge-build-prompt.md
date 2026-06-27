# Lean 4 / Mathlib — finalize the ∀M achiever-chart construction: rate is FREE, det is the crux

## Goal
Construct `nodeChartGeneral M : NodeAchieverChart M` ∀M (a structure bundling ONE map `phi : (Fin N → ℝ)
→ (Fin N → ℝ)` with BOTH a RATE field and a DET field), to discharge an in-gate atom
`routeMCore_box_diverges_achiever`. N = routeMAmbient M = flatDim M.

The two load-bearing fields of `NodeAchieverChart M`:
- `leaf_integrand`: ∀ c (u : Fin N → ℝ),
  `(∏ j |u_j|^{leafH j}) · |routeMCore M (phi u)|^{-c} = monomialIntegrand N (δ_p) leafH c u · (Ufun u)^{-c}`
  — unfolds to needing `routeMCore M (phi u) = (u_p)² · Ufun(u)` (loss = pivot² × unit), p the radial pivot.
- `cov`: a change-of-variables saying `|det Dφ(u)| = ∏ j |u_j|^{leafH j}` (off `{u_p=0}`).
- side: `leafH p = minAdm M − 1`; threshold reads ONLY the binding axis p (spectator axes k=0 are free).

## What is BANKED (reuse, do NOT rebuild)
- `routeMCore_phiGen u M t B hle hC0 : routeMCore M (phiGen u M t B hle) = u² · VvalGen u M t B hle`.
  `phiGen u M t B hle := paramsEquivFlat M (chartParamsGen u M t B hle)`. Here `u : ℝ` is the SCALAR
  radial parameter and `B : GenBlk M t` is block data; they are INDEPENDENT arguments. `hC0` is the
  identity-boundary condition `C 0 · suffix 0 = suffix 0`.
- `genBlkFlatStruct M t ha x : GenBlk M t` — the STRUCTURED disjoint-slot decoder reading free
  Schur/lift coords from `x : Fin N → ℝ` via `chartIdxEquiv` role slots (Bmat 0 = I, Rmat 0 = 0,
  structural, NOT x-dependent at the boundary k=0).
- `hC0_struct M t ha u : <hC0 for genBlkFlatStruct M t ha (fun _ => u)>` — proven; its proof
  (`C0_eq_one`) touches ONLY `.Bmat 0`/`.Rmat 0`, both constant in x.
- `routeMCore_phiFlatStruct M t ha u : routeMCore M (phiFlatStruct M t ha u) = u² · V` where
  `phiFlatStruct M t ha u := phiGen u M t (genBlkFlatStruct M t ha (fun _ => u)) (hleStruct M t ha)`.
  This is the CONSTANT-x diagonal (all coords = scalar u) — a 1-parameter family, NOT a full chart.
- DET infra: `composeFold (fs : List (ChartFactor N))` (foldr ∘); `composeFold_abs_det_leafH fs leafH u
  hdet : |det (fderiv (composeFold fs) u)| = ∏ |u_j|^{leafH j}` GIVEN the per-factor det product `hdet`.
  `conjBlockFactor E g gD hg : ChartFactor N` with `|det (D u)| = |det gD ((E u).1)|` (det-preserving
  block conjugation via ANY CLE E : (Fin N → ℝ) ≃L Block × Rest). Banked factor maps:
  `schurChartFactor E` (det |K.det|^{r+c}), `lduChartFactor E` (det ∏|q_i|^{2(t-1-i)}),
  `chainChartFactor Nblk E` (det 1, FIXED N), `radialFactor active p` (det |u_p|^{card-1}).
- `paramsEquivFlatCLE M : Params M ≃L (Fin N → ℝ)` (LINEAR, |det|=1).
- The `(4,4,2,2)` anchor is a PURE radial blow-up: `phi4422 = paramsEquivFlat ∘ pack ∘ pivotBlowupOn`,
  det = |u_0|^{minAdm-1}, NO Schur/LDU. The `(3,3,4)` anchor needs a Schur shear (det 1) + b=aβ.

## MY KEY REFRAME (please validate or break)
The blueprint (UPDATE-8 OPTION-1) routed BOTH rate and det through a single bridge
`composeFold fs = phiFlatStructV`. But I observe:

**The RATE is FREE at a general vector x.** Define the VECTOR-parametrized structured chart
  `phiFlatStructV M t ha x := phiGen (x p) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)`  (p = ⟨0,_⟩)
Then `routeMCore_phiGen (x p) M t (genBlkFlatStruct M t ha x) (hleStruct) (hC0_x)` gives
  `routeMCore M (phiFlatStructV x) = (x p)² · VvalGen (x p) M t (genBlkFlatStruct M t ha x) hle`
directly — NO bridge — provided I generalize `hC0_struct` from `(fun _ => u)` to arbitrary `x`
(should be free: C0_eq_one only reads the constant Bmat 0 / Rmat 0). Ufun x := VvalGen (x p) ... x.

So the bridge `composeFold fs = phiFlatStructV` is needed ONLY for the DET field (to invoke
`composeFold_abs_det_leafH`). The det of `phiFlatStructV = paramsEquivFlat ∘ chartParamsGen ∘
genBlkFlatStruct` is the genuinely hard part.

### Questions
1. Is the rate-direct reframe SOUND? i.e. does `routeMCore_phiGen` genuinely apply at scalar `(x p)` with
   block data `genBlkFlatStruct M t ha x` reading the SAME x, and does `hC0` generalize trivially to
   arbitrary x (given Bmat 0 / Rmat 0 are x-independent constants)? Any trap where the SCALAR (x p) and
   the block data x being correlated breaks the rate identity `prod = u·H`?  (In phiFlatStruct the scalar
   and block coords were identified as `fun _ => u`; here scalar = one coordinate x p, block = the rest
   of x. The rate engine telescopes `prod = u·H` via hC0 + telescope — does it care that u = x p is also
   one of the coords feeding B? I believe not, since the telescope is pure matrix algebra in B and u.)

2. For the DET: is the cleanest path STILL the bridge `composeFold fs = phiFlatStructV` with the
   Params-conjugated factors (OPTION-1)? Or, since I now need the bridge ONLY for det, is there a cheaper
   det route — e.g. split `det D(phiFlatStructV) = det(paramsEquivFlat) · det D(chartParamsGen ∘
   genBlkFlatStruct)` and compute the latter map's Jacobian det directly via the chain rule on its
   explicit block structure (radial blow-up × Schur shear × LDU × chain telescope)? Which is less Lean
   pain at OPAQUE dependent widths (Text/Wext)?

3. Concretely: the achiever leafH for general M. The det telescope gives `|u_p|^{minAdm-1}` (radial) ×
   ∏(spectator LDU/Schur exponents). Confirm the threshold is unchanged: monomialThreshold reads ONLY the
   binding axis p (k_p=1, h_p=minAdm-1), the spectators have k=0 so ratio ∞. So leafH can carry ANY
   exponents on spectator axes. Does this mean I can pick a DELIBERATELY SIMPLE leafH (e.g. just
   δ_p·(minAdm-1), zero elsewhere) by choosing a chart whose det is EXACTLY |u_p|^{minAdm-1} — i.e. a
   PURE radial blow-up reshape like (4,4,2,2) — IF such a reshape realizes chartParamsGen? Or does the
   general descent path genuinely force LDU q-monomials (det ≠ pure radial) so leafH MUST carry
   spectators? (i.e. is the (4,4,2,2) pure-blow-up special, or generalizable by choosing the chart?)

4. If the full factor decomposition IS needed: confirm the OPTION-1 funext-s bridge is the right crux
   shape and the chainVarMap (variable-N, det 1) correction. Give the MINIMAL module sequence + the
   single riskiest sub-lemma.

Be concrete and Lean-level. The make-or-break is whether I can AVOID the full Schur/LDU/chain
reconstruction for the DET by either (a) a direct chain-rule det of chartParamsGen∘genBlkFlatStruct, or
(b) choosing the chart to be a pure radial blow-up reshape. If neither, I build the full OPTION-1 bridge.
