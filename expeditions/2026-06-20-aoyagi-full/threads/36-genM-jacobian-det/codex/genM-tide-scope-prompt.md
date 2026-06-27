# ∀M achiever-chart Lean build — tide-scope adjudication

I'm a Lean 4 (Mathlib v4.29) formaliser closing the FINAL piece of an "R1-lower atom": building
`nodeChartGeneral M (hpos : 1 ≤ minAdm M) : NodeAchieverChart M` for ARBITRARY dimension vector
`M : Fin (L+1) → ℕ`, then discharging `routeMCore_box_diverges_achiever` ∀M. I need a sharp,
decorrelated read on the achievable SCOPE for ONE tide (context-bounded), and the cleanest route.

## What `NodeAchieverChart M` requires (11 fields)
A chart `phi : (Fin N → ℝ) → (Fin N → ℝ)` (`N = routeMAmbient M`), a pivot axis `p`, Jacobian exponents
`leafH : Fin N → ℕ` with `leafH p = minAdm M − 1`, a unit `Ufun` with a compact bound + a.e.-positivity,
a `leaf_integrand` identity `(∏ |u_j|^{leafH j})·|F(phi u)|^{-c} = monomialIntegrand·U^{-c}`, a
change-of-variables `cov` (Jacobian c-o-v: `∫ phi''(V\{u_p=0}) g = ∫_{V\{u_p=0}} ofReal(∏|u_j|^{leafH j})·g(phi u)`),
and `image_subset` (a box maps into the cube).

## What is BANKED parametric (∀M, sorry-free)
1. `tStar M : Fin L → ℕ` — chosen `Mval`-minimizer (achiever path); `Mval_tStar_eq : Mval M (tStar M) = minAdm M`;
   `rBlock`/`cBlock` (per-boundary residual block dims); `sum_rBlock_cBlock_eq_minAdm : ∑ rBlock·cBlock = minAdm`.
2. `GenBlk M t` — per-boundary block data (matrices at opaque widths `Text M t k`, `Wext M k`):
   `Bmat k`, `Nblk k`, `Wblk k`, `Rmat k`, `Rfin k`. The chain `chainOfMt u M t B hle` builds
   transitions `C k = Bmat k · chainQ(N_k) + u•Rmat k` (interior), `C L = u•Rfin L` (leaf);
   layers `A k = chainA(N_k)(W_k)(C(k+1))`.
3. `chartParamsGen u M t B hle : Params M` = the chain's layers reindexed to M-widths.
4. **`routeMCore_phiGen u M t B hle (hC0) : routeMCore M (phiGen u M t B hle) = u² · VvalGen u M t B hle`** —
   the RATE, DECODER-AGNOSTIC, fully parametric, for ANY `B` satisfying `hC0` (the identity-boundary
   `C 0 · suffix 0 = suffix 0`). `VvalGen = ‖HrGen‖²` (Frobenius), `HrGen = reindex(Hmat 0)`, the
   telescoped `prod = u•HrGen`.
5. `genBlkFlatStruct M t ha x : GenBlk M t` — a PARAMETRIC structured decoder reading free Schur/lift
   coords from disjoint `chartIdxEquiv` slots (`readK/X/N/E/W`), with `Bmat (k+1) = bmatStack (readK)(readX)`,
   `Rmat (k+1) = rmatPad (readE)`, identity boundary `Bmat 0 = reindex 1`, `Rmat 0 = 0`.
   **BUT `Rfin := fun _ => 0`** (the leaf is DEAD) — so `chartParamsGen(genBlkFlatStruct …)` has det 0
   (the "D1 bug"). `hC0_struct` (the identity-boundary fact) is banked unconditional for it.
6. `radialFactor active p : ChartFactor N` (det `|u_p|^{card−1}`); parametric Schur/LDU factor MAPS
   `schurFrameMap {t r c}` (det `|det K|^{r+c}`), `lduCoreMap {t}` (det `∏|q|^{2(t−1−i)}`); a
   `composeFold`/`ChartFactor` det-telescope engine `composeFold_abs_det`; `cleConjFactor` (CLE conjugation),
   `phiTarget_abs_det_of_factored : |det Dφ| = ∏|u_j|^{leafH j}` GIVEN `composeFold fs = φ` + det bookkeeping;
   `paramsEquivFlat M` (measure-preserving reshape `Params M ≃ Fin N → ℝ`).
7. `routeMCore_box_diverges_of_nodeChart M W c' hc' ε hε` — the M-agnostic ASSEMBLY: takes a
   `NodeAchieverChart M`, returns the atom conclusion. So once `nodeChartGeneral` lands, the atom is one line.

## What is BANKED only at CONCRETE anchors (the templates to generalize)
- `(2,2,2)` (`RouteM222Det.lean`, 1141 lines) and `(3,3,3,3)` (`RouteM3333Det.lean`, 586 lines):
  each defines a CONCRETE full-rank decoder `B_det222`/`B_det3333` (a `GenBlk` with `match k` per-boundary,
  explicit Schur-frame matrix entries like `!![x1, x1*x2; x1*x3, x1*x2*x3+x4; …]`, a LIVE `Rfin` =
  `!![1, x7]` / `!![x24,x25,x26]` — the D1 fix), the bridge `chartParamsGen(B_det x) = chartParams… x`
  (a hand-built EXPLICIT chart with per-node polynomial entries), then det via a hand-built
  `T = pivotBlowupOn ∘ shear ∘ …`, `pack`, injectivity, cov, `Ufun = ‖Hbar‖²` (explicit polynomial).
- The explicit charts (`chartParams3333`, `Hval3333`) are MASSIVE sympy-computed polynomial tables — they
  do NOT obviously come from a parametric recursion.

## The route the certificate committed (route (i) parametric)
`φ_M = Q_M ∘ T_M`, `T_M = composeFold(radialFactor active p :: per-boundary schur/ldu/shear factors)`,
det via `composeFold_abs_det` → `∏|x_j|^{leafH_M j}`, `leafH_M p = minAdm−1`. The ONE heavy piece: the
bridge funext `chartParamsGen(B_det M x) = pack_M(T_M x)` over OPAQUE widths via `chainA_apply_castAdd`
(kept row = `C_{s+1}−N_s·W_s`) / `chainA_apply_natAdd` (lift row = `W_s`), generalizing the anchor bridges.

## The CRUX of my question
Both anchors route through a hand-built EXPLICIT chart (`chartParams222`/`chartParams3333`) with per-node
polynomial entries that look sympy-generated, NOT parametric-recursion-derived. The ∀M `pack_M(T_M x)`
must REPLACE that explicit chart with a parametric `composeFold` whose layers EQUAL the chain layers
`chainA(N_s)(W_s)(C(s+1))` — and `C(s+1)` is itself a recursion (`Bmat·chainQ + u•Rmat`) over opaque widths.

Questions (answer sharply, rank by tractability for ONE context-bounded tide):

**Q1.** Is there a route to `Ufun`/positivity/cov that AVOIDS re-deriving the explicit `Hval`/`Uval`
parametrically? Specifically: can I take `Ufun := VvalGen (x p) M (tStar M) (B_det M x) hle` directly
(the banked rate's unit), get `F∘phi = (x p)²·Ufun` for FREE from `routeMCore_phiGen`, and then need only
(a) `VvalGen > 0` a.e. (non-vacuity: `HrGen ≠ 0` somewhere — is this provable parametrically, e.g. from
full-rank `B_det M` off `{x_p=0}`?), and (b) `VvalGen` continuous/measurable in `x` for the compact bound?
Or does `cov` force the explicit Jacobian `∏|u_j|^{leafH j}` which itself forces the `T_M`/`pack_M`
factorization and hence the bridge funext anyway?

**Q2.** The `cov` field needs `|det Dφ_M| = ∏|u_j|^{leafH_M j}` as a genuine Jacobian-c-o-v. This forces
the bridge `phi_M = Q_M ∘ T_M` (the `composeFold` factorization) and `InjOn` off the det-zero locus. Is
the bridge funext `chartParamsGen(B_det M x) = pack_M(T_M x)` over opaque widths genuinely ONE-tide
tractable, or is it the multi-tide wall the thread history (15 prior updates, repeated walls here)
suggests? What is the single most-likely-to-stall sub-step?

**Q3.** Given context bounds, what is the RIGHT checkpoint to land in ONE tide and report at? Options:
(a) the width-parametric DEFINITIONS only — `B_det M` (full-rank, with live `Rfin`), `T_M`, `pack_M`,
`leafH_M` — each SPECIALIZE-CHECKED to reduce to the banked anchors, full-rank verified off `{x_p=0}`,
but the bridge funext + cov + nodeChart deferred; OR (b) push for the full bridge funext; OR (c) something
else. Is `B_det M` (the parametric full-rank decoder generalizing `B_det222`/`B_det3333`) itself a
contained sub-tide, or does even DEFINING it parametrically require resolving the Schur-frame entry
structure that the anchors hand-coded?

**Q4.** `genBlkFlatStruct` is banked parametric but has dead `Rfin`. Is the cleanest `B_det M` a small
edit of `genBlkFlatStruct` (swap `Rfin := fun _ => 0` for a live leaf reader + designate a fixed-1 pivot
residual), reusing its banked `hC0_struct`/rate — or a fresh decoder? What exactly must the live `Rfin`
encode so that (i) `hC0` still holds (it's decoder-agnostic but reads `Bmat 0`/`Rmat 0`, untouched), and
(ii) the chart is full-rank off `{x_p=0}` (the D1 fix)?

Be concrete and Lean-aware. I want the truth about scope, not encouragement.
