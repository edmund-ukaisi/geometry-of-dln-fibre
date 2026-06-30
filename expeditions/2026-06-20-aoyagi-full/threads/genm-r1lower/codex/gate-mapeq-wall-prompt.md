<task>
Lean 4 + Mathlib, RLCT lower-bound for deep linear nets, depth L=2. I must scope BOUNDED-vs-WALL
for the ∀M-L2 interior achiever chart's pure-monomial Jacobian `cov` field, BEFORE a heavy build.

GOAL: a `NodeAchieverChart M` whose chart `φ` has `|det Dφ| = ∏_j |u_j|^{leafH_j}` (a PURE MONOMIAL),
rate `routeMCore(φ u) = u_p²·U` (U a.e.-positive), so the box-integral diverges at c'=½·minAdm.

STATE OF THE ART (all sorry-free unless flagged):
- The chart target is `phiFlatStructV = paramsEquivFlat ∘ chartParamsGen(x_p) ∘ genBlkFlatStruct`,
  the structured/dead-leaf decoder. Its RATE `routeMCore(phiFlatStructV x)=x_p²·U` is BANKED (∀M).
  Its unit a.e.-positivity (interior class) is BANKED (pivot-survival witness).
- A reusable det telescope is banked: `composeFold fs` for `fs : List (ChartFactor N)` has
  `|det D(composeFold fs)| = ∏_i |det D_i(prefix_i)|` (chain rule + det product). The per-FACTOR maps
  are banked as full-ambient ChartFactors with their abs-dets:
    * Schur frame `S(X,K,N,E)`, `|det DS| = |det K|^{r+c}`  (banked schurFrame_abs_det)
    * LDU core `(l,q,u) ↦ split((1+L)diag(q)(1+U))`, `|det| = ∏_i |q_i|^{2(t-1-i)}` (banked)
    * chain unit (linear), `|det|=1` (banked)
    * radial pivot blow-up `pivotBlowupOn`, `|det| = |u_p|^{minAdm-1}` (banked)
- The BRIDGE `composeFold fs = phiFlatStructV` (map-equality, needed to transfer the det to the chart)
  has been REDUCED, sorry-free, to a Params-level layer-op equality via a single collapse CLE
  `bridgeCLE` (CLE-conjugation cancellation, `composeFold_eq_cleConj_foldr`). The reduced obligation:
    decompose the MONOLITHIC Params-level op `phiParamsStruct` (= chartParamsGen ∘ genBlkParamsStruct)
    into a DEPENDENCY-ORDERED fold of layer-ops `gs : List (Params M → Params M)` (Schur_s, LDU_s,
    chain_s, radial), each whose CLE-conjugated ChartFactor has the banked per-factor det, such that
    `(gs.foldr (∘) id) = phiParamsStruct` (as Params→Params maps).
- The monolithic-op collapse MECHANISM is validated end-to-end (a single trivial gs = [phiParamsStruct]
  reproduces phiFlatStructV). What is OPEN: the genuine Schur/LDU/chain/radial layer-op DECOMPOSITION
  of phiParamsStruct over OPAQUE Wext/Text widths, with the per-factor dets summing (in exponents) to
  ∏_j |u_j|^{leafH_j} (the multi-axis leafH = radial minAdm-1 on the pivot + per-boundary LDU pivot
  exponents 2(t-1-i) + frame r_s+c_s).
- Worked FIXED-WIDTH anchors exist: (3,3,3,3) phi3333 (a bespoke Q∘T chart, NOT composeFold) proves
  |det| = |u0|^5·|u1|^4·|u4|^2·|u9|^3 via an LDU coordinatization Kparam3333 straightening det K into
  a monomial. (3,3,4) phi334 similarly. So the GEOMETRY is real at fixed widths.
- ALSO open: the `cov` is not just the det — it is the lintegral change-of-variables
  ∫_{φ''(V\{u_p=0})} g = ∫_{V\{u_p=0}} (∏|u_j|^{leafH_j})·g(φ u). Needs φ injective off the
  weighted-axis planes + an n-fold null-slice argument (the (3,3,3,3) phi3333_cov is the 4-slice
  template). The weighted-axis COUNT grows with M (1→2→4 across the anchor family).

THE TWO RISK LOCI to adjudicate:
(R1) The layer-op decomposition of phiParamsStruct over opaque widths: is decomposing the monolithic
     chartParamsGen∘genBlkParamsStruct into ordered Schur_s/LDU_s/chain_s/radial layer-ops (Params→Params)
     with the right per-factor dets a BOUNDED build (a dependency-ordered telescope, the fixed-width
     anchors generalize), or is there a genuine obstruction (e.g. the LDU straightening Kparam needs to
     be DEFINED ∀M and its det-monomialization proven over opaque widths — the (z1z4-z2z3 ↦ u1u4) move
     at general K-size)?
(R2) The n-fold null-slice `cov` with a VARIABLE weighted-axis count: is the change-of-variables (injOn
     + Sard-style null slice) a bounded generalization of the fixed 4-slice phi3333_cov, or does the
     variable axis count make the injOn/null-slice argument a wall?
</task>

<output_contract>
For EACH of R1 and R2: a verdict in {BOUNDED, WALL, BOUNDED-BUT-MAJOR} + ≤4 sentences naming the single
hardest sub-step and why it is/ isn't a wall. Then: a 1-line overall recommendation (proceed solo /
proceed with sub-hands / STOP-and-report-wall). Then: the single cheapest discriminating test I could
run in Lean or on paper to confirm the verdict for R1 specifically. Mark each claim DERIVED (from the
shapes I gave) vs INFERENCE. Total under ~400 words.
</output_contract>

<grounding_rules>
You do NOT have the repo. Reason only from the shapes/facts above. Do not invent Mathlib lemma names.
The fixed-width anchors (phi3333, phi334) ARE built and sorry-free — treat their existence as DERIVED
evidence the geometry is real. The opaque-width generalization is the uncertain part. If a question
cannot be settled from the given shapes, say UNSURE and name what repo fact would settle it.
</grounding_rules>
