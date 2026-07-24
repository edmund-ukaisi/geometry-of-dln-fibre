# Next-build render — the math to close `exists_coreResolution:311` (option b, the ideal-route `hideal`)

Phase-checkpoint planning render (2026-07-24), post `survey-inv` kernel-verification. General/thorough; NO
instance-as-justification. Separates **A** (proved, swap/wire) from **B** (genuinely-unbuilt math), with the
**bypass verdict**. Companion to BUILD-STATE.md (the inventory) + ideal-route-full-render.md (the L-A/L-B/Thm-4
spine, rev-render-verified).

## 1. The delivery pipeline — PROVEN (clean-three), a chain of hypotheses
Closing one chart's `hideal` reduces along a proven chain:
- **per-step `StepInv`** (`Core.Aoyagi.StepInvShearChild`, CLEAN): `stepInv_delta0_pullback_child` (δ=0 =
  plain pullback `b'=b∘σ`, trivial/general); `stepInv_delta1_shear_child` (δ=1 = **the coupled Case-1 step,
  "THE WALL's heart"**, proved ABSTRACTLY vs FIX-A/FIX-RESID). Key hypotheses: `σ = blockBlowupMap center
  pivot ∘ sh` (blow-up OUTERMOST — the monument/L7 order, so **SEAM-1 composition-order is RESOLVED in the
  step algebra**), `sh` pivot-keeping, and **`hsupp`: the parent residual is a center-coordinate combination
  `residⱼ u = ∑_{i∈center} cⱼᵢ u · uᵢ`**. Produces the child residual as the STRICT TRANSFORM
  (`blockBlowupCoordQuot`), witness `q'=q∘σ`.
- **`terminal_bezout`** (CLEAN): at the terminal (residual trivial) + a cleared pivot `(Fᵢ₀∘g)=b·unit`,
  `unit 0≠0`, invert on `{unit≠0}` ⟹ upgrade `StepInv` (divisibility) to `PrincipalInv` (the ideal identity
  `⟨F∘g⟩=⟨b⟩`, both ways).
- **`principalInv_regionRepresents`** (L1, CLEAN): `PrincipalInv → hideal_fwd ∧ hideal_bwd` (the
  `RegionRepresents` both ways = the `Chart.hideal` fields).
- **`chart_of_collapse` / L6′ / L8′** (CLEAN): `hideal` + `hcollapse` (`|jacDet gmap|=jacWeight jac`, unit≡1)
  ⟹ a fully-certified `Chart (coreGen d e) 0`.
So GIVEN the fold emits (per chart) terminal `PrincipalInv` + `FoldRealizes` (the collapse `hcollapse`), the
`Chart` → `AtlasRealizesExponents` → `:311` follow (modulo the import-cycle + `hcover`). The value half
(`hlb`+`hattain`) + D12 are already clean-three.

## 2. THE BYPASS VERDICT (the crux the survey surfaced)
The ideal-route fold, built via the CLEAN per-step children (`stepInv_delta0/delta1`), **SUPERSEDES** the
geometric-fold's per-step `case1/2_preserves_stepInv''` (which carry `sorryAx` via the frontiers): the
abstract δ=1 shear child IS the coupled Case-1 step, proven. **BUT it does NOT bypass the WALL** — the child
emits the residual as the strict transform, and to feed the NEXT δ=1 step the fold must maintain `hsupp` (the
child residual is again a center-combination). That maintenance IS `realBranch_appendResidDescent`. Verdict:
- **per-step maintenance: bypassed-to-clean** (`stepInv_delta1_shear_child`, done).
- **the invariant-carry (`hsupp` down the branch = `appendResidDescent`): NOT bypassed** — but it is exactly
  the render's **L-B (the b-chain divisibility absorbing the block-elim cross-terms), rev-render #3-verified
  sound**. So it is render-bounded, Lean-unbuilt — NOT open math.

## 3. B — the genuinely-unbuilt residual (general)
- **B1 `leaf_stepInv_of_path` (the fold-INDUCTION).** Compose `stepInv_delta0/delta1` (clean) + the `hsupp`
  carry (B2) down `buildTree`; subsume→`LastLayerInv` at `S=L` (B4); hand the terminal edge to
  `terminal_bezout` (clean); EMIT a `GeoAtlasData` + `FoldProduced` + `FoldRealizes` + per-chart terminal
  `PrincipalInv`. A genuine CONSTRUCTION (the structural induction + the emit-bookkeeping) — tractable given
  the atoms, but real; the missing statement = the theorem body.
- **B2 `realBranch_appendResidDescent` (the WALL = the `hsupp` invariant-maintenance).** The strict-transform
  child residual stays a center-combination through the coupled-corank≥2 recursion. RENDER-VERIFIED (L-B,
  b-chain, rev-render #3). Lean-unbuilt. The genuinely-hard coupled piece, but render-bounded.
- **B3 `foldResid_case11_mergeBoostSplit_canon` (Case-1(1) merge boost-split).** OPEN QUESTION (to settle in
  the deeper render + rev-render): is it SUPERSEDED by `stepInv_delta1_shear_child` (does the abstract δ=1
  child already cover the Case-1(1) merge), or does the fold still route through it? If superseded, it drops
  from B.
- **B4 `lastLayer_clear_preserves` (S=L clear).** The terminal-layer handling (`LastLayerInv` + conditional
  `GeneratorCleared`) feeding the terminal handoff. Bounded.
- **B5 `leafPath_compactCover` (the coupled `hcover`).** `ball 0 ρ ⊆ ⋃ (gmap''dom)`. UN-PROBED at corank≥2 —
  the highest residual risk (charter §3 + elder gate). The box-geometry (`GeneralGeoAtlas`) mechanisms are
  for a SIMPLER single-term-shear object; the faithful coupled cover is unbuilt. **PROBE decorrelated
  BEFORE committing the full fold** (elder gate ii). Independent of the fold-induction.

## 4. A — proved, swap/wire (scout-verified; NOT the math, the plumbing)
- Swap unprimed L6/L8 `sorry` → `leafPath_chartGeometry'`/`leafPath_realizesExponents'` (clean). Terminal
  handoff (`terminal_bezout` + `terminal_edge_stepInv`), `case2_conjA`, homogeneity twins — clean (some
  consumer-less today). **Blocker:** the import cycle — `exists_coreResolution` lives upstream in
  `LearningCoefficient`, so the in-place `:311` sorry can't consume the primed driver without a
  `coreGen`/`flatDim` reorg OR promoting the primed driver canonical. A wiring task, not math.

## 5. Open questions → the deeper render + rev-render review
- (Q1/B3) Is `foldResid_case11` superseded by `stepInv_delta1_shear_child`, or a distinct merge obligation?
- (Q2/B2) Is `appendResidDescent` EXACTLY the render's L-B (so render-bounded), or does its Lean statement
  carry more than L-B verified (e.g. the `supportAt`/center bookkeeping)?
- (Q3/B5) The corank≥2 `hcover` probe — the un-probed highest risk; decorrelated exact geometry.

**NET (honest, corrected):** the residual is NOT "swap+wire", and NOT "the whole monument unbuilt". It is:
the fold-INDUCTION (B1, a construction over proven atoms) + the `hsupp` invariant-carry (B2 = render-verified
L-B, Lean-unbuilt) + the coupled `hcover` (B5, un-probed = the real risk) + [B3 possibly superseded, B4
bounded] + the A-plumbing/import-cycle. The per-step algebra + the whole delivery pipeline are proven; the
coupled hardness lives in B2 (render-bounded) and B5 (un-probed). The elder gate stands: prototype (B2 at
corank-2, dom-wide two-sided `hideal`) + probe (B5 corank≥2), green-both before the full fold.

## 6. CORRECTION (survey-inv bypass read) — §2's verdict conflated two ENCODINGS; supersede it
My §2 claim "`appendResidDescent` = the render's L-B, render-bounded" is WRONG. The `#print axioms` split is
the discriminator: `case2_conjA` (the IDEAL/divisibility half) is CLEAN; the `sorryAx` is 100% in the
DEGREE-1-SUPPORT maintenance (`Deg1SupportedSlot` → `appendResidDescent`; and `case1_conjA`'s
`foldResid_case11`), which exists ONLY to make the `blockBlowupCoordQuot` SUBSTITUTION (divide-by-pivot =
strict transform) exact. That is the SUBSTITUTION fold's frontier (the RETIRED geometric-fold's) — NOT the
render's L-B (b-chain). The clean `stepInv_delta1_shear_child` itself USES `blockBlowupCoordQuot`, so it is
the SUBSTITUTION per-step (its `hsupp` = the center-combination is what `appendResidDescent` must supply —
the near-circularity I mis-read as "bypass").

**It is a RE-ARCHITECT CHOICE, not a free bypass — same monument, two encodings:**
- **Encoding-S (substitution, the current typed invariant `FoldStepInvAt = StepInv ∧ Deg1SupportedSlot`,
  `foldResid = blockBlowupCoordQuot`):** any fold with this typed invariant STRUCTURALLY owes
  `appendResidDescent` + `foldResid_case11` (the degree-1-support descent). These are the retired
  geometric-fold frontiers (`foldResid_case11` REFUTED-AS-STATED, #69) — NOT render-verified.
- **Encoding-I (ideal-route = OPTION b, charter §1.B):** RE-TYPE the fold — invariant `⟨A⟩=⟨diag b⟩` with
  POLYNOMIAL cofactors, b-chain absorbing cross-terms, NO substitution / NO degree-1-support. It never
  divides by the pivot, so it never needs degree-1 exactness — it BYPASSES `appendResidDescent`/`foldResid_case11`
  as such. Its price: (a) a DIFFERENT `foldResid`/invariant (drop `Deg1SupportedSlot`, carry the
  polynomial-cofactor ideal identity); (b) DIFFERENT one-step leaves = the Schur-clearing polynomial-cofactor
  preservation = **`regionRepresents_of_matrix_mul` general-`d`** (from `canonNormalizationOf` over
  `buildTree`, dom-wide). (a)+(b) IS the render's **L-A/L-B (rev-render-verified sound)** in the matrix
  encoding — render-bounded, Lean-unbuilt.

**CORRECTED residual for option (b) = Encoding-I:**
- Re-type the fold layer (L3/L4/L5 invariant + one-step leaves). **Contained to the fold** — L6′/L8′/L1 +
  `chart_of_collapse` consume `RegionRepresents` (encoding-agnostic) and SURVIVE unchanged. The clean
  `StepInv` children + `terminal_bezout` (divisibility half) serve either encoding.
- Build the general-`d` matrix-identity `hideal` (`regionRepresents_of_matrix_mul` composed over `buildTree`
  from `canonNormalizationOf`, dom-wide) = the render's L-A/L-B, verified sound → **render-bounded, the
  genuine Lean build.** (The corank-2 step exists on `-PROTO`; general-`d` is the residual.)
- + the re-typed fold-INDUCTION + `hcover` (B5, un-probed — unchanged, encoding-independent).

**NET (corrected):** option (b) is NOT "swap the substitution twins" — it is a fold-layer RE-TYPE to the
ideal-identity invariant, building the general-`d` matrix-identity `hideal` (render-verified L-A/L-B) +
`hcover`. The substitution frontiers (`appendResidDescent`/`foldResid_case11`) are the OTHER encoding's, not
option (b)'s path — do NOT "swap" them. The elder gate is unchanged (the corank-2 prototype now = the
matrix-identity `hideal` step, two-sided dom-wide; + the `hcover` probe). rev-render is auditing this
corrected verdict.

## 7. rev-render audit — §6 CONFIRMED (decorrelated + Codex); three sharpenings; scope SETTLED
rev-render (own Lean read + fresh Codex on the wiring files) CONFIRMS §6: the "bypass" via
`stepInv_delta1_shear_child` was an ENCODING conflation (Encoding-S substitution, not the render's ideal
route); `appendResidDescent` is the degree-1-support/substitution frontier, NOT render-bounded L-B.
Sharpenings (all strengthen §6):
- **(a) The substitution atoms are UN-WIRED + fidelity-fragile — do NOT build Encoding-I on them.**
  `stepInv_delta1_shear_child` has NO consumer in the repo (the wired concrete route is
  `foldResid_stepMap_eq_pivot_mul` + `stepInv_child_delta1_append`, Case1Wire:37), AND it needs a MISSING
  concrete-residual bridge (`c(σu)=c(q_u)`; plain `hsupp` doesn't give it — its residual is manufactured,
  not the actual `foldResid` child). So the clean atoms are Encoding-S plumbing, not an Encoding-I brick.
- **(b) Q2 CONFIRMED false: `appendResidDescent` asserts MORE than L-B.** L-B = an IDEAL equality (b-chain,
  invariant under generator changes). `appendResidDescent` = an EXACT POINTWISE decomposition over a PINNED
  coordinate set `supportAt(child)` with continuous coefficients — NOT generator-invariant, fidelity-fragile
  (the cap-escape repair to full `layerCoords(S+1)` is unverified). So "render-bounded" on B2 was genuinely
  false. (Not a concern under Encoding-I, which never owes it.)
- **(c) Q1: B3 `foldResid_case11` is a DISTINCT Encoding-S frontier** (Case-1(1) merge re-factoring; shares
  the refuted-as-stated history) — drops ONLY under Encoding-I. Confirms §6.
- **(d) Q3/B5: the coupled `hcover` risk is the FAITHFUL MULTI-TERM shear** (`canonNormalizationOf` = Schur
  cross-term + Aoyagi's layer-(S±1) recoords); `GeneralGeoAtlas`'s single-term box-geometry does NOT apply.
  (hcover-probe redirected to the multi-term shear.)
- **(e) Circularity: NONE** — clean DAG (`appendResidDescent` takes no child-StepInv hypothesis).

**SETTLED SCOPE — option (b) = Encoding-I (the ideal-route re-type), ranked residual:**
1. **[High] the general-`d` matrix-identity `hideal`** = `regionRepresents_of_matrix_mul` composed over
   `buildTree` from `canonNormalizationOf` (`Q1·C1·Q2=diag(1,Δ)`), dom-wide = the render's L-A/L-B
   (rev-render-verified sound). Corank-2 core exists sorry-free on `-PROTO` (`Corank2Proto.Q1_C1_Q2_eq_diag`)
   → render-bounded; general-`d` is the genuine build. Do NOT route through the substitution B2.
2. **[High] B5 coupled `hcover`** — the faithful MULTI-TERM-shear cover, un-probed (SEAM-2), encoding-
   independent. hcover-probe in flight; probe-before-commit (elder gate ii).
3. **[Medium] the re-typed fold-induction** (B1) + root anchor (inside the sorried L5 fold body).
4. **[none] circularity.**
The clean `StepInv`/`Deg1SupportedSlot` atoms are Encoding-S — NOT Encoding-I bricks. Pipeline (L6′/L8′/L1,
`chart_of_collapse`) is encoding-agnostic → survives the re-type unchanged.

## 8. rev-render R1–R4 audit (2nd round, decorrelated + Codex on the `bChain`/`StepData` code) — SCOPE CONFIRMED
- **R1 VERIFIED:** `regionRepresents_of_matrix_mul` (Corank2Proto:219, sorry-free) turns `M=A·N` (continuous
  cofactors) into `RegionRepresents` (flatten/reindex, no ideal machinery); its corank-2 instances give BOTH
  inclusions via `Q1`/`Q1⁻¹` (from the sorry-free `Q1·C1·Q2=diag(1,Δ)`) = **L-A at one fixed width**. The
  general-`d`, dom-wide, two-sided weighted `diag(b)` composition over `buildTree` = **L-B (render-verified
  rev-render #3, Lean-unbuilt, NO open lemma)**.
- **R2 VERIFIED — GENUINE bypass, not a re-encoded frontier (exact algebra):** `B=diag(b'_p..b'_m)`,
  `b'_i=b'_p·r_i`; clean elim `L=I−∑d''_{ip}E_{ip}`, weighted `P=I−∑ r_i d''_{ip}E_{ip}` satisfy `P·B=B·L`,
  so `P·(B D'' C')=B·(L D'')·C'` — both inclusions (`P⁻¹`=sign-flip). **No residual-support decomposition
  appears**; the only denominator `b'_p` is killed by the b-chain (`b'_i/b'_p=r_i` a monomial). The b-chain
  is **construction-automatic** (`b_i|b_j` for i≤j definitional, ARBITRARY ~t; ~t-correctness matters only
  for exponent bookkeeping), covering the whole lower block, so **corank≥2 is safe via SUCCESSIVE 1×1
  clears** (a simultaneous non-triangular block clear could fail; sequential doesn't). Encoding-S's pinned
  coordinate-support (MonumentAtlas:575) is genuinely NOT owed by Encoding-I — different in kind.
- **R3 VERIFIED — re-type CONTAINED to the fold layer:** zero `Deg1SupportedSlot`/`supportAt`/`FoldStepInv`
  refs in ANY pipeline consumer (`PrincipalInv`/`LeafChartWire`/`LeafGeometryWire`/`ProductResolution`) —
  they consume `RegionRepresents`/`PrincipalInv` (encoding-agnostic). L6′/L8′/L1 + `chart_of_collapse`
  survive unchanged.
- **R4 — coupled `hcover`: THE one un-probed high risk** (multi-term-shear faithful cover; GeneralGeoAtlas
  single-term doesn't apply). Encoding-independent. hcover-probe in flight (redirected to multi-term).

### THE FOUR R2 BUILD GUARDRAILS (hold these during the Encoding-I build — the bypass fails if violated)
1. **`D_J` MUST stay a genuine RUNNING COORDINATE BLOCK** — if `D_{J+1}` is defined as an arbitrary
   pulled-back residual ÷ u, that RECREATES Encoding-S (the divide-by-pivot). This is #1.
2. Never a row-mix with `b'_p ∤ b'_i`, nor a simultaneous non-triangular block op (breaks the 1×1-clear
   safety).
3. **Derive `bExp` from the ~t-formula, NOT an assumed arbitrary chain** — the current `StepData` stores
   `bChain` as a proof field; it should reduce to ONE scalar exponent lemma, not a branchwise support
   invariant.
4. Compose BOTH `RegionRepresents` directions (one-sided = one inclusion; equality needs the unipotent
   `A_k⁻¹`, available but must be built).

### RANKED RESIDUAL (option b = Encoding-I) — rev-render-final
1. **[High, UN-PROBED — probe FIRST] coupled `hcover`** (multi-term-shear faithful cover, SEAM-2). The real
   risk. hcover-probe deciding.
2. **[High verification, bounded, NO open lemma] general-`d` two-sided weighted `hideal` over `buildTree`**
   (= L-B, render-verified). Substantial fidelity-sensitive Lean; NO identified open math — given guardrails.
3. **[Medium] the fold plumbing** (running-coordinate automorphism + case/rollover + dependent-dimension
   pullback composition).
4. **[Low] b-chain divisibility + corank≥2 polynomiality of `P`** — construction-automatic.

**NET (planning phase, settled + doubly rev-render-verified):** the re-architect (Encoding-I, ideal route)
is SOUND, RENDER-BOUNDED (R1: L-A verified corank-2, L-B render-verified), a GENUINE bypass of the
substitution frontier (R2: `PB=BL` exact algebra, b-chain automatic, corank≥2-safe), and CONTAINED to the
fold layer (R3). NO open math lemma remains for the `hideal` (given the four guardrails). The ONE un-probed
high risk is the coupled `hcover` (R4, multi-term shear) — the hcover-probe decides it. Commit to Encoding-I
behind the elder gate (corank-2 matrix-identity `hideal` prototype two-sided dom-wide + the `hcover` probe,
green-both).

## 9. hcover-probe VERDICT (decorrelated exact algebra + Codex) — GREEN on the math + ONE wire condition
The coupled corank≥2 `hcover` (R4/B5, the co-highest risk) is **GREEN on the MATH — no genuine escape
obstruction — with one named, load-bearing WIRE condition** (charter §3's "render-bounded ≠ Lean-inhabited"
bites here, but it is a wire choice, not open math).
- **OBL-1 (per-edge box-containment): FULLY BOUNDED.** The faithful multi-term `canonNormalizationOf` (all
  three supports, corank-3) is a sum of BILINEAR terms (total degree exactly 2), write/read-disjoint ⟹
  `σ⁻¹ = id−φ` EXACT (symbolic). Box clause holds with `f(r)=r+C·r²`, `C = max #bilinear/entry ≤ layer
  width`, **DEPTH-INDEPENDENT** (uniformity from bounded widths — rev-render's criterion (2), CONFIRMED;
  3×10⁵ box points, max residual ≤ 0). The render's one-pivot-per-step deg-2 reset CHECKS OUT (blow-up
  re-coords the deg-2 Schur residual `Δ=A4−A3A2` into fresh deg-1 before the next clear; per-node deg-2 even
  as the COMPOSITE grows ~2^depth, absorbed by the engine's `f^[depth]`, never a global degree bound).
  `f^[depth]1` is an EXACT finite rational (finite since depth ≤ L·maxwidth) — no divergence; leaf boxes
  huge-but-COMPACT, chart maps polynomial + a.e.-injective, sizing `dom_c` that large is legitimate.
  **SEAM-2 (fidelity) CLEARED head-on** (probe Part E, on the FAITHFUL three-support `canonNormalizationOf`
  = Schur cross-term + the layer-(S±1) recoord SUMS, NOT the simpler single-term `outerShear`): (i) order-2
  survives the recoord sums — `fderiv(coPhi)(0)=0` computed EXACTLY (a finite sum of bilinear terms has zero
  Jacobian at 0 ⟹ no linear part ⟹ centers never bite; rank-q vs rank-1 irrelevant to order-2); (ii) `C` =
  recoord-sum length `= width−cleared−1`, so `C ≤ max_ℓ d_ℓ − 1` (WIDTH bound) and it DECREASES as `cleared`
  advances (deeper) — the NO-GO "recoord length that GROWS with depth" provably does not occur. So OBL-1
  holds for the FAITHFUL multi-term chart, retiring BUILD-STATE §CAVEAT's load-bearing SEAM-2 (box-containment
  side); the C-generic-cover side folds into OBL-2/route-(a).
- **OBL-2 (fan-completeness): MATH bounded, but a REAL wire gap.** The full-fan block-atom
  `closedBall_subset_iUnion_blockBlowup_image_radius` is PROVEN `|S|`-general (verified corank |S|=2,3,4);
  coupling only ENLARGES `S`, no new escape — so the FULL fan (all pivots `p∈S`) covers every direction.
  BUT the current atlas is **COL-PINNED** (`IsRealBranch` rule-(b), pivot col = cleared, MonumentAtlas:1071;
  the :1065 comment: "cover uses ROW-fan charts only; the column-orbit is the #86(B) per-step-σ transport,
  sorried"). This is **FALSE-as-pinned** — Codex re-derived the escape: `(4,4,4)` root case-2, direction
  `q=(layer0,row0,col1)` with `|x_q| > (M+1)·max_{col-0}|x_p|` escapes every col-0 chart (a single chart
  escapes 66% of the box). So `leafPath_compactCover` on the col-pinned atlas is FALSE.
- **THE RESIDUAL (the col→full-fan bridge), two routes:**
  - **(a) [RECOMMENDED — unconditionally sound, zero new math]** emit the FULL fan directly (all pivots
    `p∈S`, drop the col-pin for the COVER charts); the block-atom then covers.
  - **(b) [current plan, NOT free]** `#86(B)` column-orbit σ-transport of row-fan charts. Codex caution: "an
    inner shear cannot repair an omitted OUTER blow-up pivot" — the column-fan is an outer blow-up pivot
    choice, so a within-chart relabel may NOT recover it; needs the GL-equivariance (`baseChange`) outer
    symmetry + its own probe. Cheapest discriminating test: does a col-1 full-fan chart occur in the emitted
    `gmap` family for `(4,4,4)`? If not, (b) is false-as-is and (a) is forced.
- **NET:** the coupled `hcover` is GREEN to commit — PROVIDED the atlas realizes the FULL fan (route a), OR
  (b) is separately probed and holds. Recommend route (a). No genuine escape obstruction; the col-pinned
  atlas alone is insufficient (named, load-bearing — NOT a footnote).

## 10. PLANNING PHASE — COMPLETE. Settled scope + recommendation.
Triply-checked (survey-inv inventory + rev-render ×2 [§7 confirm, §8 R1–R4] + hcover-probe [§9]). **NO open
math obstruction remains.** Option (b) = **Encoding-I** (the ideal-route fold re-type):
- **`hideal`:** the general-`d` matrix-identity (= render's L-A/L-B, rev-render-verified; corank-2 sorry-free
  on `-PROTO`) — render-bounded, no open lemma, given the FOUR §8 guardrails.
- **`hcover`:** GREEN-on-math (§9); build via **route (a) full fan** (sound, zero new math) — not the
  col-pinned atlas.
- **contained to the fold layer** (R3); the pipeline (L6′/L8′/L1, `chart_of_collapse`) survives.
- **residual = a genuine-but-BOUNDED Lean build** (the general-`d` matrix-identity `hideal` + the full-fan
  cover + the fold plumbing) — fidelity-sensitive, substantial, but NO identified open mathematics.
- **RECOMMENDATION:** commit to Encoding-I + route-(a) full fan, behind the **elder gate** (corank-2
  matrix-identity `hideal` prototype, two-sided dom-wide, four guardrails held + the full-fan cover atom,
  green-both) → then the full fold. First build unit = the corank-2 Encoding-I `hideal` prototype (the
  gate-2 measurement).
