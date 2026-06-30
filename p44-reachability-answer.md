   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
OpenAI Codex v0.142.4
--------
workdir: /tmp/p44-scope
model: gpt-5-codex
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019f164e-a56c-7c00-98e1-20350edc6700
--------
user
# Scope: is the L2 deepest-point RLCT normal form (#44) reachable via the new §SEL IFT chart?

Decorrelated reachability adjudication. Lean 4 + Mathlib, a DLN RLCT formalisation. Pure
math/architecture reasoning — I want a BOUNDED-via-chart vs RESEARCH-WALL verdict + the route. Be
adversarial and concrete.

## The target (#44, currently a NAMED sorry, ~600–1500 LoC est. via the heavy route)
`deepest_regular_core_normal_form`: at the DEEPEST point of the DLN loss (L=2, layers all rank exactly
`r`; `B = A¹A²`, rank B = r), the local RLCT is
> `rlctAt H (dlnLoss H B) (deepestPoint) = nReg/2 + lambdaCore(H − r)`
where `nReg = r(H0 + H2 − r)` and `lambdaCore(M)` is a CLOSED-FORM combinatorial value
(`½·min_T M(T)` over an admissible cone — NOT defined as an RLCT; it's the recursively-computed core).

The docstring's intended proof: a rank-`r` gauge-slice change of variables `C_s = [[I_r+X_s, Y_s],[Z_s,
T_s]]` (regular coords = output residual blocks P₁₁−I, P₁₂, P₂₁; reduced core = ‖∏C'_s‖² = dlnLoss(H−r) 0),
routed through `rlctAtOn_unit_invariant_aux` + germ-locality (the slice has unit Jacobian, NOT det ±1, so
NOT a measure-preserving change of variables). That's the heavy 600–1500 LoC obligation.

## The NEW machinery (just built, separately): the §SEL general-`v` IFT chart
For a GENERAL optimal `v` (prod v = B, rank B = r), an IFT chart Φ (selected nReg loss-minors + complement
projection, det DΦ ≠ 0 PROVEN) transfers the local RLCT:
> `rlctAt H (dlnLoss H B) v = rlctAtOn (fun (s,y) => ∑ᵢ sᵢ² + ∑ⱼ qⱼ(s,y)²) (0, t0)`
i.e. `nReg` coordinates become exact squares `∑ s²` and the rest is a C¹ residual `q`. Then a banked
quasi-split engine gives `rlctAtOn (∑s² + ∑q²) (0,t0) = nReg/2 + rlctAtOn (∑ q(0,·)²) t0` (the residual's
own RLCT). The deepest point is a SPECIAL CASE of a general optimal `v`.

## THE QUESTION
Is #44 REACHABLE by applying the §SEL chart AT the deepest point (special case), reducing it to:
(A) the chart gives `rlctAt(deepest) = nReg/2 + rlctAtOn(residual q(0,·)²) t0` — mechanical from the
    banked chart + quasi-split, AND
(B) `rlctAtOn(residual q(0,·)² at deepest) = lambdaCore(H − r)` — the residual's RLCT equals the
    closed-form core?
— thereby REPLACING the heavy gauge-slice with {chart + quasi-split + (B)}? Or does (B) itself reopen the
same heavy gauge-slice / recursion, making the chart route no easier?

Sub-questions:
Q1. At the DEEPEST point specifically, is the §SEL residual `q(0,·)` literally (or up to a measure-
    preserving/diffeo reindex) the REDUCED-WIDTH loss `dlnLoss (H−r) 0` (the `∏ C'_s` core in the
    docstring)? I.e. does the selected-minor chart's complement coordinates at the deepest point coincide
    with the reduced-core block `T_s`? If yes, (B) becomes "rlctAtOn(dlnLoss (H−r) 0) 0 = lambdaCore(H−r)"
    — the SAME reduced-loss-RLCT identity the gauge-slice route produces. If the chart's `q` is NOT the
    clean reduced loss (e.g. it's the reduced loss PLUS chart cross-terms), is the difference RLCT-
    irrelevant (germ-locally same zero-set / same Newton polytope) or does it genuinely change the core?
Q2. Is `rlctAtOn(dlnLoss M 0) 0 = lambdaCore M` (the reduced-core identity) ALREADY a separate theorem in
    this development (the recursion / R1 machinery computes lambdaCore), so that the chart route closes
    #44 by CITING it — or is that identity ALSO open / IS effectively #44 at smaller width (so the chart
    just shifts the wall down a level)?
Q3. The chart gives `rlctAt = rlctAtOn(...)` as an EQUALITY (both ≤ and ≥) only if Φ is a genuine local
    diffeo with the residual form holding as a germ identity (f =ᶠ F∘Φ). The §SEL producer was built to
    give the `≥`-leg of a COMPARISON (rlctAt deepest ≤ rlctAt v) CONSUMING #44 as `hDeepest`. Does the
    chart actually yield the ABSOLUTE deepest value as an equality, or only one inequality direction?
    (If only ≤, #44 needs the matching ≥ — is that the hard half?)
Q4. VERDICT: BOUNDED-via-chart (#44 = chart + quasi-split + a CITED reduced-core identity, modest LoC) vs
    RESEARCH-WALL (the chart route reopens the gauge-slice or an open recursion, no easier than the heavy
    route). If bounded, the minimal lemma chain. If wall, the one obstruction that doesn't dissolve.

Adversarial: I suspect the chart elegantly delivers (A) but (B) just renames the heavy content (the
reduced-core RLCT = lambdaCore is the actual mathematical work, and the chart doesn't compute it). Tell me
if that suspicion is right, or if there's a genuine reduction I'm missing (e.g. the deepest residual being
exactly a smaller-width deepest loss makes #44 INDUCTIVE on width via the chart — which WOULD be a real
win). Findings only, no Lean.

warning: Model metadata for `gpt-5-codex` not found. Defaulting to fallback metadata; this can degrade performance and cause issues.
exec
/bin/bash -lc ls in /tmp/p44-scope
 succeeded in 0ms:
AGENTS.md
CLAUDE.md
README.md
ROADMAP.md
TEMPLATE.md
docs
expeditions
lean
p44-reachability-answer.md
p44-reachability-prompt.md
paper-sources
theory
threads

  → Review SEL chart and deepest point assets
  • Check status of reduced-core RLCT results
  • Synthesize verdict with reasoning
exec
/bin/bash -lc 'ls docs' in /tmp/p44-scope
 succeeded in 0ms:
decorrelated-records
expositions
policies

exec
/bin/bash -lc 'rg "SEL"' in /tmp/p44-scope
 succeeded in 124ms:
expeditions/2026-06-18-voigt-discharge/synthesis.md:  **degeneration** (L6.1+L6.2) — the Abeasis–Del Fra theorem the PAPER ITSELF only cites; genuine new content.
expeditions/2026-06-18-voigt-discharge/synthesis.md:theorem the SOURCE PAPER ITSELF cites (Abeasis–Del Fra / Lakshmibai–Magyar) — closes the geometry in modules,
expeditions/2026-06-18-voigt-discharge/synthesis.md:**hA UNBLOCKED** (thread 39, reviewer + decorrelated Codex, commit e2306f0): Codex produced a SELF-COMPILED
expeditions/2026-06-25-theta-components/threads/13-smoothness-S1/codex/jacobian-stdout.log:/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/synthesis.md:938:- **The L2 producer is now at a STABLE, fully-banked checkpoint.** Clean bricks (all axiom-clean): PIN1, PIN2 + the Score squeeze, the rectangular LDU, the germ bridge, E1, the split smooth-affine chart, the Ψ lenses, the abstract diffeo bridge, the triangular-normalizer Core lemma. The producer's remaining sorries are PRECISELY roadmapped as the general-L frontier (the (1a) IsDeepLayers strengthening for the L=2 diffeo + the L≥3 interior). The 12-catch producer-fold push is COMPLETE at this checkpoint — no green-but-wrong.
expeditions/2026-06-25-theta-components/threads/13-smoothness-S1/codex/jacobian-stdout.log:/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/synthesis.md:945:- **CONSOLIDATION — the producer fold reaches a stable, honestly-documented checkpoint.** Clean bricks ALL banked + axiom-clean: PIN1, PIN2 + the Score squeeze (`deepest_loss_squeeze` axiom-clean), the rectangular LDU, the germ bridge, E1, the split smooth-affine chart, the lenses, the abstract diffeo bridge, the triangular normalizer Core lemma. The producer's remaining sorries are PRECISELY roadmapped as the general-L frontier: 2896 (L2-diffeo via the (1a) IsDeepLayers strengthening), 3099/3104 (L≥3 hinterface, Item 19), 3270 (L≥3 hstep2, Item 24). The 12-catch producer-fold push concludes at a clean checkpoint — NOT a green-but-wrong close.
expeditions/2026-06-25-theta-components/threads/13-smoothness-S1/codex/jacobian-stdout.log:/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/r1-route-B-refuted.md:75:PRECISELY FOR the blow-up. A blow-up chart is non-injective with Jacobian vanishing on the exceptional
expeditions/2026-06-20-aoyagi-full/lessons.md:Mathlib gap dissolved. Then pp started writing "R1 is medium" — and CAUGHT ITSELF, pressure-tested R1.6 (the
expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/certificate-decoder-fix.md:   - The pivot `p` maps to ITSELF (`pivotBlowupOn … p`: `if i = p then x p`), scaling the FIXED-1
expeditions/2026-06-20-aoyagi-full/threads/24-r1-hfin-design/hfin-design-certificate.md:drops coords ⟹ `det ≡ 0`, `phi334`'s failure). The pivot blow-up `a = u·â` is PRECISELY what resolves
expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/codex/bcd-prompt.md:  `|x p|^{#E entries}` = `|x p|^{minAdm}`?? But target is `minAdm-1`. The pivot coord x p ITSELF is one of
expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/h2-joint-psi-cert.md:  PRECISELY the E2 solution: compute
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:The constructor leg of the D1 `hchart` (Altitude-B, spec §SEL): from a `C¹` map `Φ : E → E` (`E` a
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:(continuity + `ContinuousAt.eventually_ne` + compact-ball inf/sup). This is the §SEL "denominator-D
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:§SEL selected-minor map) and `F = ∑s² + ∑q²` (the post-chart loss). -/
expeditions/2026-06-23-fibre-codim/threads/26-fibre-dim-fibration/codex/run.log:   singularities). What is the cleanest SELF-CONTAINED argument (Gröbner / standard monomial basis / a
expeditions/2026-06-23-fibre-codim/threads/18-deep-chart-ring/codex/fidelity-review-prompt.md:   inequality be TRUE-BUT-USELESS / reversed?
expeditions/2026-06-20-aoyagi-full/threads/wall2-clean-chart/codex/architecture-prompt.md:   free u's — using `paramsEquivFlat` ITSELF as the reshape so that the "which u goes where" is delegated to
expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/codex/l2wire-hptri-route-prompt.md:2. If (b): state PRECISELY the equality that must hold (Score-via-triangular = Score-via-producer) and
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:The network-free real-analysis lemma the D1 (★) `≥`-leg rests on (spec §SEL, the LIGHTER
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:    spec §SEL): a single mean-value Lipschitz bound `‖q(s,t) − q(0,t)‖ ≤ L·‖s‖` on a ball gives
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:/-- **The slice comparison from one vector Lipschitz bound** (the §SEL vector triangle). For a
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:is the constant comparison, and the §SEL vector triangle gives it from a single Lipschitz bound. -/
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-prompt.md:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:./genfree-strategy-prompt.md:44:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:./genfree-strategy-answer.md:59:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:./genfree-strategy-prompt.md:44:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:./genfree-strategy-answer.md:59:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/codex/r2-frontpivot-answer.md:   columns occupy that corner changes which entries are compared to `1`. The SELECTED expression
expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/hproducer-verdict.md:   columns occupy that corner changes which entries are compared to `1`. The SELECTED expression
expeditions/2026-06-18-voigt-discharge/threads/09-L4d-affine-domain-dim/codex/route-prompt.md:   QUESTION 3 (the catenary worry): does (**) ITSELF secretly need catenary-ness of R beyond what
expeditions/2026-06-20-aoyagi-full/threads/20-r1-route-adjudication/scripts/hnode_geometry_careful.py:The reduced G² must be the (1,4) leaf? No — (1,4) leaf is ITSELF smooth (4 squares),
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:132:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:162:./codex/hfin-prompt.md:49:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:252:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:321:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:351:./codex/hfin-prompt.md:49:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-prompt.md:49:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:132:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:132:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:./codex/hfin-prompt.md:49:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:./codex/hfin-prompt.md:49:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-prompt.md:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/fm3-coord-bridge/codex/readbody-skeleton-prompt.md:(b) the single named gap is PRECISELY the §4 chart obligation (NOT a vacuous `sorry` that smuggles the
expeditions/2026-06-20-aoyagi-full/threads/fm3-coord-bridge/G1-FINAL-build-spec.md:across resumes. Cheaper to either (a) hand it a SELF-CONTAINED task with the current decls inlined, or (b)
expeditions/2026-06-20-aoyagi-full/threads/fm3-coord-bridge/G1-FINAL-build-spec.md:(yes). De-risks the type the general fix-body fills. Built it MYSELF (not via the drift-prone background
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:The §SEL selected-minor IFT-chart producer, WIRED. The banked reductions
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:genuinely-lighter premise the §SEL route identified: the residual is a `C¹` sum of squares
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:(`Foundations.S1IFTProducer`) builds `hF`, `hQ0`, `hR` (definitional) and `hcmp` (the §SEL
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:hypothesis list, replacing them with the single `C¹`-residual premise the §SEL route certified.
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:/-- **The `hAtV` half from a `C¹` first-peel residual** (the §SEL producer wired). At a general
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:/-- **The full D1 per-point `≥` from two `C¹` residuals** (the §SEL producer wired through both
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:  -- the FIRST-peel `hcmp` (the §SEL vector triangle from `q`'s smoothness)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:SELF-maps (`coreAbsorb` an additive translation homeo — global free; `regStraighten` an `E`-straightening,
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverDispatch.lean:banked `routeMCore_box_diverges_clean`), and leaving the not-yet-built branches as PRECISELY-STATED
lean/DLNFibre/DLN/RLCT/AxCheck.lean:-- D1 §SEL producer (Altitude A, network-free) — must be CLEAN-THREE [propext, Classical.choice,
lean/DLNFibre/DLN/RLCT/AxCheck.lean:-- from ANY C¹ residual `q` (the §SEL collapse to `rlct_quasiSplit_ge`, D-INDEPENDENT — no new Mathlib
lean/DLNFibre/DLN/RLCT/AxCheck.lean:-- reviewer + lean-formaliser §QA). The §SEL win: chart-DATA (hF/hQ0/hcmp) removed from the hyp list.
lean/DLNFibre/DLN/RLCT/AxCheck.lean:-- use-site instantiates with the §SEL selected-minor Φ + the H_indep block-invertible f'.
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:that the `Y1'`-definition is PRECISELY the E2 solution holding `P01` fixed:
expeditions/2026-06-23-fibre-codim/threads/21-residual-math-paths/codex/route-prompt.md:   singularities). What is the cleanest SELF-CONTAINED argument (Gröbner / standard monomial basis / a
expeditions/2026-06-23-fibre-codim/threads/21-residual-math-paths/codex/route-answer.md:   singularities). What is the cleanest SELF-CONTAINED argument (Gröbner / standard monomial basis / a
expeditions/2026-06-23-fibre-codim/threads/15-total-ring-presentation/codex/r2-2-verdict-analysis.md:  R2-2 ITSELF — not R2-3. It needs a certified ideal-transport before grinding.
expeditions/2026-06-23-fibre-codim/threads/15-total-ring-presentation/codex/r2-2-presentation-prompt.md:5. REACHABILITY: M-route module estimate (count) + the single hardest sub-step of R2-2 ITSELF (not
expeditions/2026-06-21-perm-invariance/synthesis.md:- **OPERATING MODE (decided):** the controller writes the q-series Lean tides HIMSELF in voigt-discharge with
expeditions/2026-06-21-perm-invariance/synthesis.md:  commit to `pi-build`; SELF-CHECK `git -C <main> status` clean (no leak to aoyagi) before reporting.
expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/mapeq-nonprefix-prompt.md:A SECOND candidate map (call it phi_ach) is a COMPOSITION OF BLOCK SELF-MAPS of the flat coordinate
expeditions/2026-06-20-aoyagi-full/threads/28-hfin-recStep-spec/scripts/L32a_corank_reconcile.py:the {det R = 0} locus, which is ITSELF a lower-corank determinantal core in the R-variables.
expeditions/2026-06-21-perm-invariance/threads/06-durfee-strategy/scratch/durfee_routes.py:#     RHS(a,b) = P_a P_b? no, that's the claim. We test the SELF-recurrence of the RHS sum:
expeditions/2026-06-20-aoyagi-full/threads/28-hfin-recStep-spec/scripts/o2_q4.py:print("So Q4 'does {det Sc=0} diverge the free-box core below threshold' is answered by the IH ITSELF:")
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g123-scripts/g123_field4_L3.py:# or does the resolved form ITSELF contain a smaller chain core needing recursion (field 4)?
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g129-scripts/g130_fidelity_check.py:NOT the Aoyagi λ. => the split would compute a sound equation about the wrong point — USELESS for the
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/r1-route-B-refuted.md:PRECISELY FOR the blow-up. A blow-up chart is non-injective with Jacobian vanishing on the exceptional
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g156-adjudication-scripts/what_collapse_needs.py:print("PRECISELY what does the box-collapse consume? (the value-CLOSING step in GE)")
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/pp2-g161-confirm/g196_decorrelated_check.py:print(f"     NOT raw gauge coords — a raw-coord squeeze would FALSELY see this fibre point as singular.")
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g152-subchart-route-prompt.md:The cert's content (cross-term ∈ ideal(reg), endpoint leak absorbed into ∑E²) reads to me as PRECISELY a
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g156-soundness-adjudication-certificate.md:Includes a SELF-CORRECTION of Addenda 1-4's implicit "deepest_le covers the box directly" reading.
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g156-soundness-adjudication-certificate.md:**SELF-CORRECTION.** Addenda 1-4 spoke of "the ordering `rlctAtOn(F,deepest) ≤ rlctAtOn(F,v)` via
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g152-sub34-finding.md:## ADDENDUM (after reading weightedThreshold_transport / S1.1) — PARTIAL SELF-CORRECTION
p44-reachability-answer.md:# Scope: is the L2 deepest-point RLCT normal form (#44) reachable via the new §SEL IFT chart?
p44-reachability-answer.md:## The NEW machinery (just built, separately): the §SEL general-`v` IFT chart
p44-reachability-answer.md:Is #44 REACHABLE by applying the §SEL chart AT the deepest point (special case), reducing it to:
p44-reachability-answer.md:Q1. At the DEEPEST point specifically, is the §SEL residual `q(0,·)` literally (or up to a measure-
p44-reachability-answer.md:    diffeo with the residual form holding as a germ identity (f =ᶠ F∘Φ). The §SEL producer was built to
p44-reachability-answer.md:  → Review SEL chart and deepest point assets
p44-reachability-answer.md:/bin/bash -lc 'rg "SEL"' in /tmp/p44-scope
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/frame-factor-target-answer.md:./expeditions/2026-06-20-aoyagi-full/lessons.md:365:Mathlib gap dissolved. Then pp started writing "R1 is medium" — and CAUGHT ITSELF, pressure-tested R1.6 (the
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/frame-factor-target-answer.md:SELF-maps (`coreAbsorb` an additive translation homeo — global free; `regStraighten` an `E`-straightening,

exec
/bin/bash -lc "sed -n '1,160p' CLAUDE.md" in /tmp/p44-scope
 succeeded in 0ms:
# geometry-of-dln-fibre

AI-assisted math-research + Lean-formalisation harness for **digesting and formalising** the paper
*"Geometry of the fibers of the multiplication map of deep linear neural networks"* (Simon Pepin
Lehalleur & Richárd Rimányi, 2024; `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).
Orientation is in [`README.md`](README.md); this file is the disposition and the working discipline.
The process harness (disposition + policies + roles + skills + the markdown→Lean pipeline) is ported
from the `ai-research-assistant` harness and is **domain-agnostic** — see [`TEMPLATE.md`](TEMPLATE.md)
to instantiate it for another paper.

## Disposition

The work here is research. Not coding, not ticking off a support ticket, not shipping a product. 
The stance: 
- careful, conscientious, objective as a scientist.
- meticulous in calculation as Euler, bold as Grothendieck. 
- methodical as Sherlock Holmes. Observe before theorising. Distinguish data from interpretation. 
- update like a Bayesian; do not collapse to the mode. 


- **Resist the move-fast-and-ship-it instinct.** Stackable, solid progress is the goal; the trap is
  *visible* progress raced ahead of it — a clean doc or confident headline that travels far while leaving
  holes behind. When you reach for a confident headline, that is the moment to look for the confound. Each
  layer should be solid and hole-free before the next stands on it.
- **Fill the layer — completion is your strength.** *The sea rises inexorably, but not in spikes*
  ([`docs/policies/bedrock.md`](docs/policies/bedrock.md)): within a boundary already staked, close the holes
  — the generality a statement promised, the cases it already claims, fidelity to the definition and the
  underlying spirit it invokes — rather than defer them. Such hardening is high-value, and it is where your
  **comparative advantage** lies: your bottleneck is scoping, taste, and direction, not the patient completion
  of well-scoped work — so do not treat that completion capacity, which is *abundant*, as if it were *scarce*.
  **Just do it!** Don't file it as a "chore" (an *unprobed* difficulty claim, not a defer). Surface to move the
  *boundary* — but an **earned** taste-judgment that a gap is the *right* extension is itself direction:
  **Just Do It** if within reach, else **roadmap** it; only a *bare, unargued* extension waits for the operator.
- **Name results for what they are.** A result's name and statement denote exactly what is proven — no more;
  reaching for an impressive name (or "done") is the visible-progress instinct in disguise. Separate Proved /
  Assumed / Cited / Deferred. See [`docs/policies/precision.md`](docs/policies/precision.md). (Here the
  recurring trap: a `rlct_…`-named result that in fact proves only a *codimension* — the `rlct = ½·codim`
  reading needs the cited Aoyagi equality.)
- **Build to bedrock.** A sorry-free build defeats *technical* slop; it never defeats *conceptual* slop —
  "technically correct but subtly wrong, not The Way." **Bedrock is the rock the rising sea rises over**: build
  the theory so the next result can stand on it without re-opening it. Where short feedback loops fail, **beauty
  is the instrument** — a vacuous, mis-scoped, or overclaiming result is *ugly*, and the ugliness is
  information. The **controller holds this taste and judges against it**; a green build is necessary, never
  sufficient. See [`docs/policies/bedrock.md`](docs/policies/bedrock.md).
- **Caveats live next to claims, not in footnotes.** An assumed hypothesis or a cited interface goes in the
  same paragraph as any claim that depends on it.
- **Write to figure out the truth, not to persuade.** Concise and fact-based.
- **Elementary, precisely.** Build explanations up from precise but simple well-chunked objects, established locally in the
  document. "Elementary" does not mean imprecise or dumbed-down or toy analogies: every step stays
  mathematically precise. Introduce the objects you use before you use them; prefer a chain of small exact
  statements over one dense one. Resist over-naming things to do chunking. Reach for an analogy only when it is exact and load-bearing. See
  [`docs/policies/writing-style.md`](docs/policies/writing-style.md).

## Writing and communication discipline (object-level focus)
In writing or in communication, focus on object-level. Resist meta-level pull. 
Remove authorial self-reassurance: `honestly`, `fundamentally`, `this is the whole point`, `this is loadbearing`, `of course`, `simply`, `just`, and selling phrasing.
The full list and the review function that enforces it are in [`docs/policies/review.md`](docs/policies/review.md).

## How research runs here

- **Expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)) are the unit: a central
  question, a controller delegating to thread teammates (explore / formalisation / infra), reviewers, and a
  synthesis at close. Run on the Agent Teams substrate (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`); launch with
  cwd = this repo root.
- **Pipeline: markdown → Lean.** Theory develops in markdown (`theory/`, expedition notes). A stable claim is
  formalised in Lean (`lean/`, library `DLNFibre`). The reader-facing digest/expositions live in
  `docs/expositions/`.
  - *Scholium* is a **viewer** (renders these markdown docs with KaTeX + callouts), not an editor; write to its
    conventions in [`docs/policies/scholium-writing-format.md`](docs/policies/scholium-writing-format.md). The
    recurring trap: display math `$$…$$` needs a **blank line before and after**, fences on their own lines
    (indented inside `!!!`/`???` callouts) — packed against text it falls through to markdown and the `_`
    subscripts render as emphasis. A second trap: **fenced code does not render inside a callout** — use an
    indented code block (8-space indent) there; top-level fenced code is fine.
- **Claims** carry kill-conditions; new claims are stress-tested, established/cited results verified against
  source ([`docs/policies/claims.md`](docs/policies/claims.md)).
- **Codex** is the independent second model for strategy and review
  ([`docs/policies/codex-consultation.md`](docs/policies/codex-consultation.md)).

## Team structure

Roles are documented under [`.agent-team/roles/`](.agent-team/roles/):
- `controller` — this lead session: meta-planning, delegation, integration.
- `scout` — explore / reconnaissance threads: map the terrain (Mathlib, the paper, possibility spaces), compute / derive / claims.
- `pen-and-paper` — a specialised `scout`: design-space math adjudicating a truth-value (`witness` / `obstruction` seats), exact algebra, decorrelated Codex; hands a certificate to the formaliser. No Lean.
- `formaliser` — formalisation (tide) threads.
- `reviewer` — controller-spawned independent audit (soundness / fidelity).
- `hardener` — independent principles / taste reviewer (precision, bedrock).

If dispatched into a role, read its role file and agent definition first.

## Branch discipline

- **One remote: `origin = git@github.com:edmund-ukaisi/geometry-of-dln-fibre.git`.** All work lives here.
- **`dev` is the integration branch.** Feature and expedition branches branch off `dev` and PR back into
  `dev`. `master` is the **release** branch — promoted from `dev` deliberately by the operator, never pushed
  to directly.
- Use a **feature branch** for any non-trivial unit of work; you can push here; don't commit to `dev` or `master` directly. One
  expedition runs on one branch (`expedition/<slug>`); PR at close behind signal-and-wait.
- **Pushing feature/expedition branches to `origin` is pre-authorized** (operator standing instruction,
  2026-06-12) — push freely to bank and share work. **Opening/merging PRs and the `dev → master` promotion
  remain operator-gated** (signal-and-wait); the operator performs those. Always confirm the push target is
  `origin`, never a non-`origin` remote.

## Memory

Persistent context lives **in-repo**: this file, the policies in `docs/policies/`, the expedition docs
(`synthesis.md` / statement cards / `thread.md`), `ROADMAP.md`, and `lean/CLAUDE.md`. Save conventions and
decisions there.

**Do NOT write to global Claude memory (`~/.claude/**/memory/`).** It pollutes other workspaces and is
invisible to collaborators reading the repo. This binds the controller **and every teammate** — the harness
may prompt you to save a memory there; do not. If a teammate writes one, the controller deletes it and
re-homes the content in-repo. (Agent-Teams *runtime* state under `~/.claude/teams/` and `~/.claude/tasks/` is
fine — that's the substrate, not persistent context.)

## The destination, plainly

We want, in honest Lean, the paper's results about the **fibres of matrix multiplication** for deep linear
networks:

- the space $\operatorname{Rep}_{\underline d}$ of composable matrix tuples, the multiplication map
  $\operatorname{mult}$, the zero-product / rank-$r$ loci, and the fibres $\operatorname{mult}^{-1}(B)$;
- via the **type-A quiver** translation (orbits ↔ Kostant partitions ↔ rank patterns, Gabriel, orbit-closure
  order, the `Ext` codimension): the codimension $C$ and the number $\theta$ of top-dimensional components,
  in the paper's three forms (Poincaré series, a quadratic integer program, an explicit formula), and the
  surprising **permutation invariance** of $(C,\theta)$;
- the payoff: the real log-canonical threshold of the square-Frobenius loss is $C/2$ — DLNs are "mildly
  singular". The geometric codimension is the new content; the Aoyagi `rlct = ½·codim` **equality** is
  **Cited** (Watanabe's universal `rlct ≤ ½·codim` + Aoyagi's exact DLN computation — the formal
  `RlctInterface.cited_aoyagi_dln` is the equality, which the payoff needs).

The reusable **engine** (everything before "the payoff") is network-free and lives in `DLNFibre.Core`; the
DLN/RLCT **application** lives in `DLNFibre.DLN`. See [`ROADMAP.md`](ROADMAP.md) for the formalisation ladder.

## Pointers

- [`README.md`](README.md) — orientation, how to launch an expedition, Lean build.
- [`ROADMAP.md`](ROADMAP.md) — the result-map + the Core/DLN formalisation-target ladder.
- [`docs/policies/`](docs/policies/) — expedition, claims, review, precision, bedrock, codex-consultation, statement-cards, writing-style (+ the reader-facing exposition trio).
- [`docs/expositions/`](docs/expositions/) — the curated reader-facing digest (starts with `paper-digest/high-level-overview.md`).
- [`.claude/skills/`](.claude/skills/) — lean-formalisation, local-codex-consult.
- [`lean/CLAUDE.md`](lean/CLAUDE.md) — Lean build + Mathlib conventions; the Core/DLN split.
- [`theory/`](theory/) — markdown theory workspace.
- [`TEMPLATE.md`](TEMPLATE.md) — how to instantiate this harness for a new paper.

exec
/bin/bash -lc 'rg "deepest_regular_core_normal_form" -n' in /tmp/p44-scope
 succeeded in 0ms:
p44-reachability-prompt.md:8:`deepest_regular_core_normal_form`: at the DEEPEST point of the DLN loss (L=2, layers all rank exactly
p44-reachability-answer.md:22:`deepest_regular_core_normal_form`: at the DEEPEST point of the DLN loss (L=2, layers all rank exactly
theory/aoyagi-2023-reproduction/verify-l2-gauge-architecture.md:9:`deepest_regular_core_normal_form` + `reg_shift_add_core_eq_aoyagiLambda` (arithmetic). So the L2
theory/aoyagi-2023-reproduction/verify-l2-gauge-architecture.md:12:`deepest_regular_core_normal_form` (Skeleton:1124, `hL : 1 ≤ L`, ONE sorry):
theory/aoyagi-2023-reproduction/verify-l2-gauge-architecture.md:17:i.e. `regular-block/2 + core`. For `2 ≤ L` this is filled by `deepest_regular_core_normal_form_of`
theory/aoyagi-2023-reproduction/verify-l2-gauge-architecture.md:38:**Case-split `deepest_regular_core_normal_form`:**
theory/aoyagi-2023-reproduction/verify-l2-gauge-architecture.md:45:- **`2 ≤ L` (the gauge chart).** `deepest_regular_core_normal_form_of` — restrict the whole gauge-chart
theory/aoyagi-2023-reproduction/verify-l2-gauge-architecture.md:47:  `deepest_regular_core_normal_form_of`) to `2 ≤ L`. The boundary-frame-triviality then holds (distinct
theory/aoyagi-2023-reproduction/verify-l2-gauge-architecture.md:63:4. **Add the `L=1` base case** to `deepest_regular_core_normal_form` (direct smooth proof, step's
theory/aoyagi-2023-reproduction/verify-l2-gauge-architecture.md:66:   then `deepest_regular_core_normal_form` closes → `product_reduction` (already proven modulo it) →
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:90:`nReg/2 + ofReal(lambdaCore M)` — the Skeleton `deepest_regular_core_normal_form` target. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:31:canonical `DLNFibre.lean` is reconciled at operator promotion. `deepest_regular_core_normal_form_of` (the
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1033:`deepest_regular_core_normal_form` (Skeleton.lean:1124) wants `nReg/2 + ofReal(lambdaCore M)`. The
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1038:`exact deepest_regular_core_normal_form_of … hcore hGne` into the Skeleton sorry once R1's value
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1045:`deepest_regular_core_normal_form` conclusion. Proof: `deepest_regular_core_reduces` (value-free,
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1047:theorem deepest_regular_core_normal_form_of (H : Fin (L + 1) → ℕ) (r : ℕ)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:40:(sub-3,4) is the g150-cert-backed block algebra (#44c). The Skeleton `deepest_regular_core_normal_form`
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:6:The Skeleton `deepest_regular_core_normal_form` (the **value-form** of the L2 reduction) is the
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:25:The conclusion is the Skeleton `deepest_regular_core_normal_form` value-form verbatim:
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:41:closed-form value `nReg/2 + ofReal(lambdaCore M)` — the Skeleton `deepest_regular_core_normal_form`
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:46:at `deepest_regular_core_normal_form` collapses to `exact deepest_normal_form_of_value … hGne hRValue`
expeditions/2026-06-25-theta-components/threads/01-theta-adjudication/codex/consult-stdout.log:1280:./lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:238:`deepest_regular_core_normal_form`: the local RLCT of the deep-linear loss at the deepest point of
expeditions/2026-06-25-theta-components/threads/01-theta-adjudication/codex/consult-stdout.log:4621:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/frame-factor-target-answer.md:7754:lean/DLNFibre/DLN/RLCT/Skeleton.lean:1138:`deepestPoint` to the closed form. **WIRING (crux2 #41):** `deepest_regular_core_normal_form` (the heavy
expeditions/2026-06-25-theta-components/threads/01-theta-adjudication/codex/consult-stdout.log: WARNING: stopped searching binary file after match (found "\0" byte around offset 1114095)
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:21:hypotheses, mirroring the conditional-bridge pattern of `deepest_regular_core_normal_form_of`.
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:95:the deepest-side equality `hDeepest` (banked via `deepest_regular_core_normal_form`, #44) and the
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:10:The `L = 1` specialization of `deepest_regular_core_normal_form` (`Skeleton.lean`), proven
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:25:`0 < H (Fin.last 1)`; the parent `deepest_regular_core_normal_form` (Skeleton:1124) carries the same
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:238:`deepest_regular_core_normal_form`: the local RLCT of the deep-linear loss at the deepest point of
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:244:theorem deepest_regular_core_normal_form_L1 (H : Fin (1 + 1) → ℕ) (r : ℕ)
lean/DLNFibre/DLN/RLCT/Validate/RRR.lean:26:  normal form `deepest_regular_core_normal_form` (#44) and the fibre-monotonicity
lean/DLNFibre/DLN/RLCT/Validate/RRR.lean:87:two named open obligations transitively (`deepest_regular_core_normal_form`,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:40:(`deepest_regular_core_normal_form`) stays the existing tracked Skeleton sorry — consumed as a
expeditions/2026-06-25-theta-components/threads/03-theta-h1-h2/codex/order-vs-components-stdout.log:1158:./expeditions/2026-06-20-aoyagi-full/synthesis.md:254:  modulo `deepest_regular_core_normal_form` (the gate sorry, Skeleton:1124 = regular/2 + lambdaCore(H−r)).
expeditions/2026-06-25-theta-components/threads/03-theta-h1-h2/codex/order-vs-components-stdout.log:2786:./expeditions/2026-06-25-theta-components/threads/01-theta-adjudication/codex/consult-stdout.log:1280:./lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:238:`deepest_regular_core_normal_form`: the local RLCT of the deep-linear loss at the deepest point of
expeditions/2026-06-25-theta-components/threads/03-theta-h1-h2/codex/order-vs-components-stdout.log: WARNING: stopped searching binary file after match (found "\0" byte around offset 1105137)
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1124:theorem deepest_regular_core_normal_form (H : Fin (L + 1) → ℕ) (r : ℕ)
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1139:`deepestPoint` to the closed form. **WIRING (crux2 #41):** `deepest_regular_core_normal_form` (the heavy
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1147:  rw [deepest_regular_core_normal_form H r B hB hr hL hpos, reg_shift_add_core_eq_aoyagiLambda H r hr hL]
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1169:SAME constant-rank chart machinery as `deepest_regular_core_normal_form` (#44) — both are
expeditions/2026-06-20-aoyagi-full/discuss-at-close.md:167:chart (product_reduction → deepest_regular_core_normal_form, 2≤L), so the L2 value-fold is required either way;
expeditions/2026-06-20-aoyagi-full/discuss-at-close.md:188:The L=1 base tide caught (Codex-corroborated) that `deepest_regular_core_normal_form` — hence `product_reduction`,
expeditions/2026-06-20-aoyagi-full/discuss-at-close.md:205:finite — `deepest_regular_core_normal_form`'s split is FALSE there. Strengthened `hpos` to `r < H s` (subsumes
expeditions/2026-06-20-aoyagi-full/discuss-at-close.md:206:`0 < H s`) across `deepest_regular_core_normal_form` / `product_reduction` / `aoyagi_learning_coefficient` /
expeditions/2026-06-20-aoyagi-full/discuss-at-close.md:751:is a SINGLE bare sorry `deepest_regular_core_normal_form` (Skeleton:1131), not the elaborate
expeditions/2026-06-20-aoyagi-full/discuss-at-close.md:797:UPPER], **1131 `deepest_regular_core_normal_form` (L2)** [staffed: genm-l2 KC1 + the producer #102], **1177
expeditions/2026-06-20-aoyagi-full/discuss-at-close.md:804:gauge-slice / Morse-with-parameters machinery* as L2's `deepest_regular_core_normal_form` (#44/1131). So D1(a) is
expeditions/2026-06-20-aoyagi-full/discuss-at-close.md:861:axiom-clean) and recon'd the L2 producer. **Finding:** the headline's L2 obligation (1131 `deepest_regular_core_normal_form`)
expeditions/2026-06-20-aoyagi-full/discuss-at-close.md:1469:D1's REDUCTIONS are all banked clean-three in canonical (PART a `rlctAt_ge_nReg_add_slice`, `hCore_slice_residual_eq`, the producer `deepest_le_of_optimal_chart`, and the general-v reduction `deepest_le_of_optimal_of_chart_certificate`). But afd7ea2d's verify-first (+ 2 Codex consults) recalibrated the ACTUAL geometric obligations UPWARD: building the general-v IFT chart (`GeneralVChartL2` instance) = the **constant-rank quadratic split (Morse–Bott/Gromoll–Meyer) at a general v, which Mathlib v4.29 LACKS** — a major multi-tide build (rung-1-scale, wall-free but substantial, strictly harder than the deepest analog). So D1's heavy remaining = the charts (#44 `deepest_regular_core_normal_form` + the general-v Morse–Bott chart), a CANDIDATE NEW LONG POLE for the L=2 ∀M headline. This corrects the controller's earlier "(i) within-reach mechanical" framing (UPDATE-392/395) — my optimism was too high; afd7ea2d's investigation is the honest read.
expeditions/2026-06-20-aoyagi-full/synthesis.md:13:**Headline status (honest; CORRECTED by l2-scope 2026-06-28, source-verified).** The GENERAL `aoyagi_learning_coefficient` is NOT clean. Its ACTUAL L2 `sorryAx` is the single BARE sorry `deepest_regular_core_normal_form` (Skeleton:1131) — closeable by the UNWIRED bridge `deepest_normal_form_of_value` (DeepestNormalFormWiring:48); the elaborate producer chain (`deepest_gauge_squeeze_exists` :403 [itself a bare sorry] → `deepest_gauge_construction`, 4 active sorries 2915/3118/3123/3289) is currently DISCONNECTED + unimported, so those 4 are NOT in the headline term today. The headline ALSO carries the D1 ≥-leg bare sorry `rlctAt_deepest_le_of_optimal` (Skeleton:1177). **Clean BOUNDED L=2 headline = wiring (Skeleton:1131 + 3 imports) + the (1a)/2915 strengthening only** — at L=2 the L≥3 sorries (3118/3123/3289) are VACUOUS. **3289 (L≥3 grouped recursive diffeo) is a genuine RESEARCH-RISK** (the one place the (A) "no walls" premise is least secure — scope LAST). NO `monomial_rlct` beyond the cited Aoyagi axiom.
expeditions/2026-06-20-aoyagi-full/synthesis.md:31:- **R-A STRUCTURAL MOVE LANDED GREEN (genm-l2wire2 @4dba9fbe, controller-verified):** deepest_gauge_construction + deepest_gauge_chart_construct + deepest_regular_core_normal_form_of MOVED from DeepestGaugeConstruction UP into DeepestL2Wiring (above the import cycle); the OLD `deepest_diffeo_bridge_L2` sorry DELETED from the gauge file (verified absent); DeepestNormalFormFrontPivot re-wired (`import DeepestL2Wiring`, no cycle); continuous_Mw de-privatised. All green. **The risky refactor (cross-file move + downstream re-wire) is DONE** — remaining = ONLY the L=2 discharge. **J-TIE subtlety (genm-l2wire, controller-confirmed):** switching the body's Pf/Qf to the triangular bundle needs hJfront (about the OLD bundle's `.choose`) to align with the triangular J (opaque post-`obtain`) → resolution (a) [restate the triangular bundle to thread the front-pivot J as a parameter] — confirmed the right call (cleaner than exposing .choose). Bounded. **PRECISION GATE (controller-flagged):** DeepestL2Wiring now also carries the L≥3/gate-4 sorries (≈296/301/465 = 3118/3123/3289, travelled with deepest_gauge_construction, roadmapped/out-of-L=2-scope). So the bridge-close clean-three check is NOT a whole-file sorry count — it must be forced #print axioms on (i) deepest_diffeo_bridge_L2_wired + (ii) the L=2 headline path, confirming the L≥3 sorries do NOT leak into the L=2 term (else route the L=2 path around them). genm-l2wire continuing: J-tie restate → hsub3reg/hsub4core discharge → bridge-close with the (i)+(ii) axiom output.
expeditions/2026-06-20-aoyagi-full/synthesis.md:287:- #44 is NOT a D1 blocker: D1's ≥-leg consumes only the VALUE-free coreDeepest (= rlctAtOn core₀ t0, done at L=2 via deepest_regular_core_reduces + the done rung 1/5 deepest_gauge_construction_L2), NOT the lambdaCore closed form. #44 = value-free-deepest-reduction (done) ▸ the R1 core-VALUE (lambdaCore, R1's lane, the conditional wire deepest_regular_core_normal_form_of @DeepestL2Wiring:1047). So #44's hard half is R1's, not a D1 obligation.
expeditions/2026-06-20-aoyagi-full/synthesis.md:299:- ★ RECALIBRATION (corrects UPDATE-392/395's "(i) within-reach mechanical"): afd7ea2d's verify-first + 2 Codex consults found that BUILDING the GeneralVChartL2 instance at the real DLN loss = the **constant-rank quadratic split (Morse-Bott/Gromoll-Meyer) at a general v, which Mathlib v4.29 LACKS** — "a major multi-tide build, rung-1-SCALE, wall-free but SUBSTANTIAL, strictly harder than the still-open deepest analog deepest_gauge_squeeze_exists (which carries sorries)." + a zero-core/terminal-v case caveat (needs a separate coreless route, documented in-file). So D1's reductions are all banked clean-three (PART a + hCore + the producer + the general-v reduction), but the actual CHART CONSTRUCTIONS are the heavy remaining geometric obligations: #44 (deepest_regular_core_normal_form, Skeleton:1124, existing sorry) + (i) the general-v chart (HARDER, Morse-Bott, Mathlib-lacking). This is a CANDIDATE NEW LONG POLE for the L=2 ∀M headline.
expeditions/2026-06-20-aoyagi-full/synthesis.md:321:- hCore INTEGRATED (canonical @3b931d7f): `hCore_slice_residual_eq` (D1ChartProducer.lean, file-only re-grab from genm-d1producer @fadb4e8d, PURE addition — the 2 PART-a theorems unchanged) — the slice residual R = (core₀∘fst)∘Φ for the G1 bounded-unit local diffeo Φ:(T,g)↦((T₁,(I+G)·T₂),g) ⟹ rlctAtOn R = rlctAtOn core₀ (diffeo transfer + spectator peel). Bedrock-glance PASS (clean conditional interface, faithful, non-vacuous). Verified CLEAN-THREE in canonical (all 3 D1 theorems), green 8581. **D1 (rung 2/5) now = obligation (i) IFT-chart producer [BUILDING] + (ii) #44 (existing Skeleton sorry deepest_regular_core_normal_form) — hCore + PART(a) DONE.**
expeditions/2026-06-20-aoyagi-full/synthesis.md:329:- D1 (rung 2/5) NOW = THREE pieces, all bounded, none R1-coupled: (i) the IFT-chart producer — a GENUINE bounded sub-build (rung-1-comparable, the IsDeepLayers-generalization of deepest_gauge_construction at a general optimal v; reuses ofExactGerm/deepest_regular_smooth_split/paramsEquivFlat/gauge-slice), the LAST D1 obligation, INDEPENDENT of hCore; (ii) #44 = the existing Skeleton sorry deepest_regular_core_normal_form (Skeleton:1124), no new work; (iii) hCore = the abstract diffeo lemma, a6e7758f BANKING IT NOW conditional clean-three on its branch → controller integrates file-only (D1ChartProducer pattern) when green+clean-three.
expeditions/2026-06-20-aoyagi-full/synthesis.md:575:- **Skeleton.lean open sorries (scoped this tick):** (1131) `deepest_regular_core_normal_form` = L2 gauge-slice geometry; (1177) `product_reduction` = L2; (1234) `resolution_charts` = R1; (1707) headline area. Maps cleanly to the live fronts: **L2** (product_reduction + normal form) ← genm-l2fin's `deepest_diffeo_bridge_L2` (ρ-gated); **R1** (resolution_charts) ← interior genm-detalpha + smeared ac8083da; **D1** (`deepest_point_reduction` #107) + headline ← both L2-GATED.
expeditions/2026-06-20-aoyagi-full/synthesis.md:899:- **genm-l2wire's spec-first report → gated (#149).** TWO decisions: **(1)** an IMPORT CYCLE (DeepestDiffeoBridgeL2 imports DeepestGaugeConstruction, so the bridge `deepest_diffeo_bridge_L2` at gauge:2853 can't call `_impl` in the higher file) → **R-A** approved: new top file `DeepestL2Wiring` importing both; move 2853 + consumers (2925/3296/3344) there; 2853 = thin `exact _impl` + the 4-hyp discharge (preserves engine/app split, makes the currently-DEAD `_impl` live). Working-branch aggregator only; canonical DLNFibre.lean reconciles at promotion; keep deepest_regular_core_normal_form_of Skeleton-importable. **(2)** hPtri/hQtri NOT provable for the producer's raw frame → **construct block-triangular frames** via blockLower/blockUpper normalizers ([Inv A11] from hNF=deepestPoint_frame_normal); hPtri/hQtri by construction; Score via them (reg+singular co-framed, RLCT gauge-invariant). genm-l2wire Codex-confirming (2) in parallel.
expeditions/2026-06-20-aoyagi-full/synthesis.md:1050:  - **1131 — L2** `deepest_regular_core_normal_form` (the λ-headline's L2 rung): IN FLIGHT. Closure chain = genm-l2subs (the 2 S6 subs) → my final-wiring (`deepest_diffeo_bridge_L2 → _impl`, the 7-frame-hyp discharge) → `deepest_normal_form_of_value` → wire into 1131.
expeditions/2026-06-20-aoyagi-full/synthesis.md:1654:  modulo `deepest_regular_core_normal_form` (the gate sorry, Skeleton:1124 = regular/2 + lambdaCore(H−r)).
expeditions/2026-06-20-aoyagi-full/synthesis.md:1875:- **L=1 BASE parallelized (`l2-base-L1`, ac2db524):** the OTHER arm of deepest_regular_core_normal_form (the L=1
expeditions/2026-06-20-aoyagi-full/synthesis.md:1920:- **L=1 base @173557a6:** `deepest_regular_core_normal_form_L1` PROVEN sorry-free + axiom-clean
expeditions/2026-06-20-aoyagi-full/synthesis.md:1924:  deepest_regular_core_normal_form is DONE; the Skeleton:1124 case-split (L=1→this / 2≤L→gauge) is the later wire.
expeditions/2026-06-20-aoyagi-full/synthesis.md:1926:  `deepest_regular_core_normal_form` — hence `product_reduction`, `aoyagi_learning_coefficient`, `aoyagi_rrr` —
expeditions/2026-06-20-aoyagi-full/synthesis.md:2181:  remaining L2 gauge-chart sorry.** Then: the L=1/2≤L case-split wire (Skeleton:1131 deepest_regular_core_normal_form,
expeditions/2026-06-20-aoyagi-full/synthesis.md:2196:  B-normalisation + core_comparability_squeeze. Closing it closes the L2 gauge chart (deepest_regular_core_normal_form_of,
expeditions/2026-06-20-aoyagi-full/synthesis.md:2256:  comparability-invariant (the squeeze is built for it), so `deepest_regular_core_normal_form_of`'s VALUE is unaffected.
expeditions/2026-06-20-aoyagi-full/synthesis.md:2362:- **The remaining L2 = the gauge-slice PRODUCER (`deepest_gauge_construction`).** Confirmed from the chain: headline sorry 1131 (`deepest_regular_core_normal_form`) = "the ONE open geometric obligation of L2" — the rank-r gauge-slice CoV (g146, non-measure-preserving, via `rlctAtOn_unit_invariant_aux`+germ-locality, ~600–1500 lines, task #44); wired 1131 ← `deepest_normal_form_of_value` ← `deepest_gauge_squeeze_exists` ← the producer. So the producer IS the heavy L2 core on the headline critical path — AND the lynchpin for D1's 1177(a) (the shared gauge-slice, per UPDATE-196). KC1 discharges the producer's 2915 [Invertible A11] sub-obligation; the gauge-slice geometry (g146) + 3099/3104 is the larger unit.
expeditions/2026-06-20-aoyagi-full/synthesis.md:2440:- **Goal-distance map (verified against Skeleton).** The headline `aoyagi_learning_coefficient` (1725) rests on exactly 4 named sorries: **1234 `resolution_charts` (R1)** ← genm-boundary (LOWER ∀M) + genm-c3wire (corank-3) / genm-recstep (general scaffold) (UPPER); **1131 `deepest_regular_core_normal_form` (L2)** ← genm-l2 (KC1) + producer #102; **1177 `rlctAt_deepest_le_of_optimal` (D1)** ← UNSTAFFED (L2-coupled, see below); **1707 `aoyagiTheta_eq` (A2/θ)** ← secondary, off the λ path. **A1 `lambdaCore_eq_clean` (4246) = PROVED** — the "headline arithmetic" (½·minAdm ↔ Aoyagi closed form) is NOT an open piece (assessed as a candidate 5th front, retired). λ-critical sorry count = 3 (R1/L2/D1), all either staffed or gated.
expeditions/2026-06-20-aoyagi-full/synthesis.md:2548:- **Scout's key inversions (all source-verified + Codex-xhigh):** (1) the 4 construction sorries do NOT feed the headline today — the producer `deepest_gauge_squeeze_exists`(:403) is a disconnected bare sorry + the 3 modules aren't imported into DLNFibre.lean; (2) the headline's REAL L2 gap is the single bare sorry `deepest_regular_core_normal_form` (Skeleton:1131), closeable by the unwired bridge `deepest_normal_form_of_value`; (3) my "20 sorries" was a grep artifact — 4 active (the "3099/3104" were docstring headers). **Clean L=2 headline = wiring + (1a)/2915 only (3118/3123/3289 VACUOUS at L=2).**
expeditions/2026-06-20-aoyagi-full/synthesis.md:3768:  1. `deepest_regular_core_normal_form` (Skeleton:1016) — the L2 VALUE-form = the CONVERGENCE NODE, fanning into
expeditions/2026-06-25-theta-components/threads/13-smoothness-S1/codex/jacobian-stdout.log:577:/home/ubuntu/workspace/geometry-of-dln-fibre/theory/aoyagi-2023-reproduction/verify-l2-gauge-architecture.md:63:4. **Add the `L=1` base case** to `deepest_regular_core_normal_form` (direct smooth proof, step's
expeditions/2026-06-20-aoyagi-full/threads/integration-recon.md:60:- Owns: `RankNormalForm.lean`, `PolynomialZeroSet.lean`, `CoreShearMP.lean`, `DeepestSplitHaar.lean`, `S1NonMPTransport.lean`, `S1Spectator.lean`, `DeepestCoreNonvanishing.lean`, `DeepestFrame.lean` (147 lines), `DeepestGaugeChart.lean` (591 lines, 2 sorries in `deepest_gauge_squeeze_exists` + `deepest_regular_core_normal_form`), `DeepestMinRlct.lean`, `DeepestNormalFormWiring.lean` (3 sorries), `DeepestSplitReindex.lean`, `GeneralR1Recursion.lean` (1 sorry, older version), `ResolutionAtlas.lean` (3 sorries).
expeditions/2026-06-20-aoyagi-full/threads/integration-recon.md:61:- Adds `deepest_regular_core_normal_form` named sorry to Skeleton.lean (+1 sorry, total 4 in Skeleton but the L2 gate is now explicitly named).
expeditions/2026-06-20-aoyagi-full/threads/integration-recon.md:130:| **L2** `product_reduction` | `crux2/fold3-close` (then `fm/deriv-frame-resume-cont`) | `deepest_regular_core_normal_form` | still sorry | `DeepestGaugeConstruction`: 2 code sorries; `DeepestTelescoping`: 0 sorries (endpoint_telescoping PROVEN); `DeepestGaugeChart`: 1 sorry (`deepest_gauge_squeeze_exists`) |
expeditions/2026-06-20-aoyagi-full/threads/integration-recon.md:210:- L2 `product_reduction`: still sorry (gated on `deepest_regular_core_normal_form`, which needs `deepest_gauge_squeeze_exists` = the IFT wall; 1 sorry in DeepestGaugeChart).
expeditions/2026-06-20-aoyagi-full/threads/l2-frontier-scope/l2-frontier-scope.md:20:   `deepest_regular_core_normal_form` (`Skeleton.lean:1131`). `aoyagi_learning_coefficient` →
expeditions/2026-06-20-aoyagi-full/threads/l2-frontier-scope/l2-frontier-scope.md:62:       └ rw deepest_regular_core_normal_form    Skeleton.lean:1124  ← BARE SORRY at :1131  (THE L2 GAP)
expeditions/2026-06-20-aoyagi-full/threads/l2-frontier-scope/l2-frontier-scope.md:80:(D1 ≥-leg, Skeleton:1177 — not this mission) and `deepest_regular_core_normal_form` (Skeleton:1131
expeditions/2026-06-20-aoyagi-full/threads/l2-frontier-scope/l2-frontier-scope.md:150:- `deepest_regular_core_normal_form` (Skeleton:1131) — THE L2 value-form gap the headline actually
expeditions/2026-06-20-aoyagi-full/threads/l2-frontier-scope/l2-frontier-scope.md:176:    `deepest_regular_core_normal_form_L1` (`DeepestBaseL1.lean:244`). Build the `DeepestGaugeChart`
expeditions/2026-06-20-aoyagi-full/threads/l2-frontier-scope/l2-frontier-scope.md:186:(`deepest_regular_core_normal_form`) with
expeditions/2026-06-20-aoyagi-full/threads/17-rrr-deliverable/statement-card.md:34:  sorries: `deepest_regular_core_normal_form` (the gauge-slice normal form, #44) and
expeditions/2026-06-20-aoyagi-full/threads/l2-frontier-scope/codex/voi-answer.md:2:AGREE. ASSUMING your trace is accurate: the construction sorries are not on the headline proof path unless some imported theorem actually references them. The load-bearing point is Lean’s dependency graph: imported files do not matter by themselves; only constants used in the proof term do. Your most plausible miss is an indirect import or duplicate/reexported symbol where `deepest_gauge_squeeze_exists` or `deepest_regular_core_normal_form` is already defined/wired elsewhere. To verify, I’d need `Skeleton.lean`, `DeepestGaugeChart.lean`, `DeepestNormalFormWiring.lean`, `DLNFibre.lean`, and `#print axioms aoyagi_learning_coefficient`.
expeditions/2026-06-20-aoyagi-full/threads/l2-frontier-scope/codex/voi-prompt.md:13:- `product_reduction` (Skeleton:1142) calls `deepest_regular_core_normal_form` (Skeleton:1124),
expeditions/2026-06-20-aoyagi-full/threads/l2-frontier-scope/codex/voi-prompt.md:37: (a) the headline's L2 gap is the bare sorry at Skeleton:1131 (deepest_regular_core_normal_form),
expeditions/2026-06-20-aoyagi-full/threads/d1-chart-producer/statement-card.md:95:>   `deepest_regular_core_normal_form`, the tracked Skeleton sorry) + the §5 interface value;
expeditions/2026-06-20-aoyagi-full/threads/d1-chart-producer/spec.md:22:inputs: `hDeepest` (= #44, the existing Skeleton sorry `deepest_regular_core_normal_form`), the chart
expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/h2-score-rederive.md:43:  REDUCED-CHAIN `M = H−r` loss. The headline `deepest_regular_core_normal_form` (Skeleton:1124) computes
expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/h2-score-rederive.md:55:`deepest_regular_core_normal_form` core-bridge (the framed-Schur Score vs the frame-free coreΦ, the
expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/h2-score-rederive.md:85:  `deepest_regular_core_normal_form` (the headline core = deepestCoreF = reduced loss),
expeditions/2026-06-20-aoyagi-full/threads/23-l2-pin1-design/thread.md:108:cert. `deepest_gauge_chart_construct` and `deepest_regular_core_normal_form_of` are downstream of the
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g147-normalform-skeleton-prompt.md:3:`deepest_regular_core_normal_form` (~600-1500 lines per a prior estimate). ROUTE-FIRST (controller
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g147-normalform-skeleton-prompt.md:9:  deepest_regular_core_normal_form (H : Fin (L+1)→ℕ) (r) (B) (hB : B.rank = r) (hr : ∀ s, r ≤ H s) (hL : 1≤L) :
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g147-normalform-skeleton-prompt.md:35:  1. The SUB-LEMMA SKELETON: ~4-8 named sub-obligations decomposing deepest_regular_core_normal_form, IN
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/frame-factor-target-answer.md:7754:lean/DLNFibre/DLN/RLCT/Skeleton.lean:1138:`deepestPoint` to the closed form. **WIRING (crux2 #41):** `deepest_regular_core_normal_form` (the heavy
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/frame-factor-target-answer.md:8075:(sub-3,4) is the g150-cert-backed block algebra (#44c). The Skeleton `deepest_regular_core_normal_form`

exec
/bin/bash -lc 'rg "rlctAtOn" lean/DLNFibre/DLN -g"*.lean"' in /tmp/p44-scope
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/AxCheck.lean:#print axioms rlctAtOn_myF222_le
lean/DLNFibre/DLN/RLCT/AxCheck.lean:#print axioms rlctAtOn_myF222_ge'
lean/DLNFibre/DLN/RLCT/AxCheck.lean:#print axioms rlctAtOn_myF222_eq
lean/DLNFibre/DLN/RLCT/AxCheck.lean:-- factor) ⟹ `rlctAtOn R = rlctAtOn core₀` (diffeo transfer + spectator peel). Conditional on the
lean/DLNFibre/DLN/RLCT/AxCheck.lean:-- Quot.sound], no `sorryAx`: `rlctAtOn_quasiSplit_ge_of_contDiff_residual` CONSTRUCTS the engine's hcmp
lean/DLNFibre/DLN/RLCT/AxCheck.lean:#print axioms rlctAtOn_quasiSplit_ge_of_contDiff_residual
lean/DLNFibre/DLN/RLCT/AxCheck.lean:-- `rlctAtOn_eq_of_contDiff_chart` chains it with the chart-transfer atom = the general chart-transfer.
lean/DLNFibre/DLN/RLCT/AxCheck.lean:#print axioms rlctAtOn_eq_of_contDiff_chart
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:    rlctAtOn f wstar = rlctAtOn F wstar.
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:This is the thin combination of a germ-congruence (`rlctAtOn` is a germ at `wstar`) with the banked
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:`rlctAtOn_boundedUnit_localHomeomorph` (which strips the bounded-unit chart). The DLN use-site supplies
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:/-- **`rlctAtOn` germ-congruence** (public form of `S1NonMPTransport`'s private
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:`weightedThreshold_congr_germ_one`). If `f =ᶠ[𝓝 wstar] g`, they have the same local RLCT — `rlctAtOn`
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:theorem rlctAtOn_congr_germ {M : Type*} [MeasureSpace M] [TopologicalSpace M]
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:    rlctAtOn f wstar = rlctAtOn g wstar := by
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:(the raw-data `rlctAtOn_boundedUnit_localHomeomorph` package), then `rlctAtOn f wstar = rlctAtOn F
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:theorem rlctAtOn_eq_of_boundedUnit_chart {M : Type*}
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:    rlctAtOn f wstar = rlctAtOn F wstar := by
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:  rw [rlctAtOn_congr_germ f (fun w => F (Ψ w)) wstar hgerm]
lean/DLNFibre/DLN/RLCT/Foundations/S1ChartTransfer.lean:  exact rlctAtOn_boundedUnit_localHomeomorph F wstar Ψ Ψsymm DΨ DΨsymm V
lean/DLNFibre/DLN/RLCT/Foundations/S1BoxProductMin.lean:The threshold VALUE `min{(e+1)/2, rlctAtOn K 0}` is already proved at the point
lean/DLNFibre/DLN/RLCT/Foundations/S1BoxProductMin.lean:`c' < min{(e+1)/2, rlctAtOn K 0}` ⟹ each chart summand finite. -/
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverGE.lean:`boxpm_integrableOn_of_lt` hypothesis. Hence `∫_U |F|^{−c'} < ⊤`, so (via `rlctAtOn_ge_of_integral_lt`)
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverGE.lean:`min{mk/2, (the c' admitted by the core boxes)} ≤ rlctAtOn F 0`.
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverGE.lean:recursion one dimension down. **The atom is NOT a clean point-min `rlctAtOn node = min{mk/2, n/2 +
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverGE.lean:rlctAtOn child}`; it threads the child's FULL-BOX integrability** (the (2,2,2) `resolved_residual_lt_top`
lean/DLNFibre/DLN/RLCT/Foundations/Rlct.lean:noncomputable def rlctAtOn {M : Type*} [MeasureSpace M] [TopologicalSpace M]
lean/DLNFibre/DLN/RLCT/Foundations/Rlct.lean:/-- On `Params`, `rlctAtOn` is `rlctAt` (both are `θ(F, 1, {w*})`). -/
lean/DLNFibre/DLN/RLCT/Foundations/Rlct.lean:theorem rlctAtOn_eq_rlctAt (H : Fin (L + 1) → ℕ) (F : Params H → ℝ) (wstar : Params H) :
lean/DLNFibre/DLN/RLCT/Foundations/Rlct.lean:    rlctAtOn F wstar = rlctAt H F wstar :=
lean/DLNFibre/DLN/RLCT/Foundations/S1BoxSqueeze.lean:`rlctAtOn_squeeze`: where `rlctAtOn_squeeze` (GeneralR1Recursion) lifts the squeeze to the point RLCT,
lean/DLNFibre/DLN/RLCT/Foundations/S1BoxSqueeze.lean:stripped (`|c₁·Φ|^{−c'} = c₁^{−c'}·|Φ|^{−c'}`). The box analog of `rlctAtOn_squeeze`'s mono leg. -/
lean/DLNFibre/DLN/RLCT/Foundations/CoreShearMP.lean:STANDALONE here so cobuild-sub34 wires them into `coreAbsorb_rlct` (`rlctAtOn_comp_homeomorph` on the
lean/DLNFibre/DLN/RLCT/Foundations/CoreShearMP.lean:Consumed by `coreAbsorb_rlct` via `rlctAtOn_comp_homeomorph` on the `coreShearHomeo`. -/
lean/DLNFibre/DLN/RLCT/Foundations/LossContinuity.lean:`rlctAtOn_ge_of_integral_lt` needs a bounded witness; `univ` breaks it). Anchoring-independent: the box
lean/DLNFibre/DLN/RLCT/Foundations/LossContinuity.lean:`≥`-direction needs (`univ` would break `rlctAtOn_ge_of_integral_lt`). -/
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:`rlctAtOn myF222 0` (on `Fin 8 → ℝ`), we need a **measure-preserving** equivalence
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:/-! ## The `rlctAtOn` transport (the seam's payload)
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:`continuous_paramsEquivFlat`) AND measure-preserving, so `rlctAtOn` transports across it via
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:`rlctAtOn_comp_homeomorph`. Given the loss-identity `dlnLoss H222 0 = myF ∘ e222` (the consumer
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:(`e222_deepest`), giving `rlctAtOn (dlnLoss H222 0) deepest222 = rlctAtOn myF 0`. -/
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:the origin — by `rlctAtOn_comp_homeomorph` (measure-preserving homeomorph `e222`) + `e222 deepest =
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:0`. The cover assembly then evaluates `rlctAtOn myF 0 = 3/2`. -/
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:theorem rlctAtOn_dlnLoss222_transport (myF : (Fin 8 → ℝ) → ℝ)
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:    rlctAtOn (dlnLoss H222 0) deepest222 = rlctAtOn myF 0 := by
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:  have key := rlctAtOn_comp_homeomorph eHom222 hmp hemb myF deepest222
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:# `DLNFibre.DLN.RLCT.Foundations.S1Cover` — the cover → `rlctAtOn` connection
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:- **`rlctAtOn_ge_of_integral_lt`** (the `≥` half) — if the threshold integral over a fixed open
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:  `U ∋ 0` is finite for every `c' < t`, then `rlctAtOn F 0 ≥ t` (each such `c'` is admissible with
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:- **`rlctAtOn_le_of_adm_le`** (the `≤` reduction) — `rlctAtOn F 0 ≤ t` reduces to: every admissible
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:`c' < t`, then `t ≤ rlctAtOn F 0`. Each such `c'` is admissible (integrable on `U` via
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:theorem rlctAtOn_ge_of_integral_lt {E : Type*} [MeasureSpace E] [TopologicalSpace E] [Zero E]
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:    t ≤ rlctAtOn F 0 := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:/-- **The `≤` reduction.** `rlctAtOn F 0 ≤ t` reduces to: every admissible `c'` (integrable on some
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:theorem rlctAtOn_le_of_adm_le {E : Type*} [MeasureSpace E] [TopologicalSpace E] [Zero E]
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:    rlctAtOn F 0 ≤ t := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:`rlctAtOn_le_of_adm_le` reduces `rlctAtOn F 0 ≤ t` to: every `c'` integrable on *some* open `Ω ∋ 0`
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:quantifier over *all* `Ω` is genuinely extra content (NOT discharged by `rlctAtOn_comp_homeomorph`:
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:`rlctAtOn_le_of_box_diverges` packages steps 1+3 (proven here — the abstract localisation is pure
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:/-- **The `≤`-direction localisation (the nbhd-quantifier discharge).** `rlctAtOn F 0 ≤ t` from a
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:contradicting the hypothesis), so `rlctAtOn F 0 ≤ t`. This is the abstract packaging of the crux —
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:theorem rlctAtOn_le_of_box_diverges {N : ℕ} (F : (Fin N → ℝ) → ℝ) (t : ℝ≥0∞)
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:    rlctAtOn F (0 : Fin N → ℝ) ≤ t := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:  apply rlctAtOn_le_of_adm_le F t
lean/DLNFibre/DLN/RLCT/Foundations/DeepestSplitHaar.lean:`#72` (`rlctAtOn_boundedUnit_localHomeomorph`) needs `(volume).IsAddHaarMeasure` on the ambient
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:`rlctAtOn (fun p => (∑ i, p.1 i ^ 2) + G p.2 ^ 2) (0, y0) = n/2 + rlctAtOn (fun y => G y ^ 2) y0`.
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:   not integrable on a finite-`volume` nbhd either when `volume Y` is infinite) and `rlctAtOn (G²)
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:   open set; so `rlctAtOn (G²) y0 = ⊤` (proven below as `rlctAtOn_zero_eq_top`). Then RHS `= n/2 + ⊤
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:   `rlctAtOn_zero_eq_top` half is Lean-proven, the LHS-finite half is the standard radial bound). So
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:   near `y0` (`rlctAtOn (G²) y0 < ⊤`) **and** real-analyticity (the general measurable additivity
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:* `rlctAtOn_zero_eq_top` — the `≡0`-loss convention fact (the witness for gap 2), reusable.
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:The general-`n` smooth block `rlctAtOn (fun x : Fin n → ℝ => ∑ i, x i ^ 2) 0 = n/2` (for `n ≥ 1`;
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:/-! ## The `≡0`-loss convention: `rlctAtOn` of the zero function is `⊤` (gap-2 witness) -/
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:/-- **The `≡0`-loss convention (gap-2 witness).** On any measure/topological space, `rlctAtOn` of
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:theorem rlctAtOn_zero_eq_top {M : Type*} [MeasureSpace M] [TopologicalSpace M] (w : M) :
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:    rlctAtOn (fun _ : M => (0 : ℝ)) w = ⊤ := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:form of `rlctAtOn`. -/
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:/-- **The smooth block, `n = 1`.** `rlctAtOn (fun x : ℝ => x²) 0 = 1/2`: the regular-coordinate RLCT
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:theorem smoothBlock1D_rlct : rlctAtOn (fun x : ℝ => x ^ 2) (0 : ℝ) = (1 / 2 : ℝ≥0∞) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:`rlctAt(loss) v ≥ nReg/2 + rlctAtOn(core)(v−core)` (`Validate.DeepestMinRlct`, the
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:  * `rlctAtOn G ≤ rlctAtOn (f∘Φ⁻¹)`        [`rlctAtOn_mono` + constant-scale invariance]
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:  * `m/2 + rlctAtOn R 0 ≤ rlctAtOn G`      [iterate `step_rlct_ge` over the `m` regular coords]
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:  * `rlctAtOn (f∘Φ⁻¹) v = rlctAtOn f v`    [`rlctAtOn_boundedUnit_localHomeomorph`, the IFT chart]
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:giving (★): `m/2 + rlctAtOn R 0 ≤ rlctAtOn f v`. The residual core `R = ∑ q_α(0,·)²` is the
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:  `f∘Φ⁻¹ = ∑s² + Q`); the chart transfer is the banked `rlctAtOn_boundedUnit_localHomeomorph`.
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:    (m : ℝ≥0∞)/2 + rlctAtOn R y0
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:      ≤ rlctAtOn (fun p : (Fin m → ℝ) × Y => (∑ i, p.1 i ^ 2) + R p.2) (0, y0).
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:    (m : ℝ≥0∞) / 2 + rlctAtOn R y0
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:      ≤ rlctAtOn (fun p : (Fin m → ℝ) × Y => (∑ i, p.1 i ^ 2) + R p.2) (0, y0) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:    have hrhs : (↑(0 : ℕ) : ℝ≥0∞) / 2 + rlctAtOn R y0 = rlctAtOn R y0 := by simp
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:    have hkey := rlctAtOn_comp_homeomorph e hMP e.measurableEmbedding
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:    have hkey := rlctAtOn_comp_homeomorph (chartN k Y).symm hMP
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:    have hsplit : ((k + 1 : ℕ) : ℝ≥0∞) / 2 + rlctAtOn R y0
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:        = (1 / 2 : ℝ≥0∞) + ((k : ℝ≥0∞) / 2 + rlctAtOn R y0) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:`rlctAtOn_boundedUnit_localHomeomorph` (applied at the D1 use site). -/
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:Then `m/2 + rlctAtOn R t0 ≤ rlctAtOn F (0,t0)`. (`C⁻¹·G ≤ F` ⟹ `rlctAtOn G ≤ rlctAtOn F` by
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:`rlctAtOn_mono` + constant-scale invariance, with `G = ∑s² + R`; then `rlct_smooth_block_ge`.) -/
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:    (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAtOn F ((0 : Fin m → ℝ), t0) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:  have hblock : (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAtOn G ((0 : Fin m → ℝ), t0) :=
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:  -- (2) `rlctAtOn G ≤ rlctAtOn F`: scale `G` by `1/C`, then dominate `(1/C)·G ≤ F`.
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:  -- constant-scale invariance: `rlctAtOn G = rlctAtOn ((1/C)·G)`.
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:  have hscale : rlctAtOn G ((0 : Fin m → ℝ), t0)
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:      = rlctAtOn (fun p => (1 / C) * G p) ((0 : Fin m → ℝ), t0) :=
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:    (rlctAtOn_unit_invariant_aux G (fun _ => 1 / C) ((0 : Fin m → ℝ), t0) (1 / C) (1 / C)
lean/DLNFibre/DLN/RLCT/Foundations/S1QuasiSplit.lean:  refine rlctAtOn_mono F (fun p => (1 / C) * G p) ((0 : Fin m → ℝ), t0) hFmeas
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:**minimum** of the block RLCTs: `rlctAtOn (G·H) (0,0) = min (rlctAtOn G 0) (rlctAtOn H 0)`. The L2
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:finite — i.e. `c < rlctAtOn G ∧ c < rlctAtOn H` — so `sSup{adm} = min`. (Contrast S1.5's `F²+G²`
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:-- the ≤ direction (one side): rlctAtOn F (0,0) ≤ rlctAtOn G 0, given H-positivity.
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:    rlctAtOn (fun p : X × Y => G p.1 * H p.2) (0, 0) ≤ rlctAtOn G 0 := by
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:-- mirror: rlctAtOn F (0,0) ≤ rlctAtOn H 0, via G-positivity.
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:    rlctAtOn (fun p : X × Y => G p.1 * H p.2) (0, 0) ≤ rlctAtOn H 0 := by
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:-- ≥ direction: min(rlctAtOn G, rlctAtOn H) ≤ rlctAtOn F.
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:-- for q < min: q < rlctAtOn G ⟹ G-adm (down-set), q < rlctAtOn H ⟹ H-adm; product finite ⟹
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:-- need a down-set extractor: q < rlctAtOn G 0 (q:NNReal) ⟹ ∃ U open ∋0, IntegrableOn |G|^{-q} U.
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:    (hdown : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn G 0 →
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:    (hdownH : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn H 0 →
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:    min (rlctAtOn G 0) (rlctAtOn H 0) ≤ rlctAtOn (fun p : X × Y => G p.1 * H p.2) (0,0) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:    (hdown : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn G 0 →
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:    (hdownH : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn H 0 →
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:    rlctAtOn (fun p : X × Y => G p.1 * H p.2) (0,0)
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:      = min (rlctAtOn G 0) (rlctAtOn H 0) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:`rlctAtOn (G·H) (0,0) = min (rlctAtOn G 0) (rlctAtOn H 0)`. The single call-site interface for the
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:    rlctAtOn (fun p : A × B => G p.1 * H p.2) (0, 0)
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean:      = min (rlctAtOn G 0) (rlctAtOn H 0) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Spectator.lean:    rlctAtOn (fun p : X × Y => F p.1) (x0, y0) = rlctAtOn F x0.
lean/DLNFibre/DLN/RLCT/Foundations/S1Spectator.lean:theorem rlctAtOn_spectator_peel
lean/DLNFibre/DLN/RLCT/Foundations/S1Spectator.lean:    rlctAtOn (fun p : X × Y => F p.1) (x0, y0) = rlctAtOn F x0 := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Spectator.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:      `= min (weightedThreshold (fun y => y²) (fun y => |y|^e) {0}) (rlctAtOn K 0)`
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:      `= min ((e+1)/2) (rlctAtOn K 0)`           (the `y₀`-side value below; `e = mk−1`).
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:This file states the lemma against the EXISTING `weightedThreshold` / `rlctAtOn` (`Rlct.lean`) — the
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:-- ≤ right: joint ≤ rlctAtOn H 0, given X-side weighted positivity.
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:      ≤ rlctAtOn H 0 := by
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:    (hdownH : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn H 0 →
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:    min (weightedThreshold G ρ {0}) (rlctAtOn H 0)
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:the `X`-side weighted threshold and the `Y`-side `rlctAtOn`. Takes the four discharged-at-use-site
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:    (hdownH : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn H 0 →
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:      = min (weightedThreshold G ρ {0}) (rlctAtOn H 0) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:  `weightedThreshold (fun p => p.1² · K p.2) (fun p => |p.1|^e) {(0,0)} = min ((e+1)/2) (rlctAtOn K 0)`.
lean/DLNFibre/DLN/RLCT/Foundations/S1WeightedProductMin.lean:      = min (((e : ℝ≥0∞) + 1) / 2) (rlctAtOn K 0) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:diffeo data the `rlctAtOn_boundedUnit_localHomeomorph` / `rlctAtOn_eq_of_boundedUnit_chart` consume.
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:`rlctAtOn_eq_of_boundedUnit_chart` consumes:
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:RLCT transfer `rlctAtOn f wstar = rlctAtOn F wstar`. This is the network-free `hchart` the DLN
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:the post-chart form `F ∘ Φ` on a neighbourhood of `wstar` (`hgerm`), then `rlctAtOn f wstar =
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:rlctAtOn F wstar`. The IFT chart `Ψ` (= `Φ` on its source) is a bounded-unit local diffeo (`det ≠ 0`
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:theorem rlctAtOn_eq_of_contDiff_chart {E : Type*}
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:    rlctAtOn f wstar = rlctAtOn F wstar := by
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:  exact rlctAtOn_eq_of_boundedUnit_chart f F wstar Ψ Ψsymm DΨ DΨsymm V hVopen hwV hΨfix
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:landing `m/2 + rlctAtOn R t0 ≤ rlctAt f v` — exactly the D1 `hAtV` shape.
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:    (m : ℝ≥0∞)/2 + rlctAtOn R t0 ≤ rlctAtOn F ((0 : Fin m → ℝ), t0).
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:to `rlctAt (loss) v` is the SEPARATE banked `rlctAtOn_boundedUnit_localHomeomorph` (use site). -/
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:theorem rlctAtOn_quasiSplit_ge_of_contDiff_residual {m n : ℕ} {Y : Type*}
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:        + rlctAtOn (fun t : Y => ∑ i, q ((0 : Fin m → ℝ), t) i ^ 2) t0
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:      ≤ rlctAtOn (fun p : (Fin m → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2))
lean/DLNFibre/DLN/RLCT/Foundations/S1SmoothBlock.lean:/-- **The smooth block, general `n = m+1 ≥ 1`.** `rlctAtOn (fun x : EuclideanSpace ℝ (Fin (m+1)) =>
lean/DLNFibre/DLN/RLCT/Foundations/S1SmoothBlock.lean:    rlctAtOn (fun x : EuclideanSpace ℝ (Fin (m+1)) => ∑ i, x i ^ 2)
lean/DLNFibre/DLN/RLCT/Foundations/S1SmoothBlock.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:`rlctAtOn` is unchanged by precomposition with a measure-preserving homeomorphism `e`: the
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:preserving (a `MeasurableEmbedding`), `rlctAtOn (F ∘ e) w0 = rlctAtOn F (e w0)`. The admissible sets
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:theorem rlctAtOn_comp_homeomorph {M M' : Type*} [MeasureSpace M] [TopologicalSpace M]
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:    rlctAtOn (fun w => F (e w)) w0 = rlctAtOn F (e w0) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:neighbourhood. This is what turns `b' < rlctAtOn H w0` into "`b'` is admissible" inside the lift. -/
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:/-- **Below-threshold ⟹ admissible.** If `(b : ℝ≥0∞) < rlctAtOn H y0` then `b` is an admissible core
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:    (hb : (b : ℝ≥0∞) < rlctAtOn H y0) :
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:  unfold rlctAtOn weightedThreshold at hb
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:Assembling the integral `≥` engine into the RLCT inequality `½ + λ_H ≤ rlctAtOn(x² + H)`. The core
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:/-- **The threshold-lift, `≥` direction.** `½ + rlctAtOn H y0 ≤ rlctAtOn (x² + H) (0, y0)`. By
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:    (1 / 2 : ℝ≥0∞) + rlctAtOn H y0 ≤ rlctAtOn (fun p : ℝ × Y => p.1 ^ 2 + H p.2) (0, y0) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:  set lamH := rlctAtOn H y0 with hlamH
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:      q ≤ rlctAtOn (fun p : ℝ × Y => p.1 ^ 2 + H p.2) (0, y0) := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:    unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:/-- **The threshold-lift, `≤` direction.** `rlctAtOn (x² + H) (0, y0) ≤ ½ + rlctAtOn H y0`. By
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:    rlctAtOn (fun p : ℝ × Y => p.1 ^ 2 + H p.2) (0, y0) ≤ (1 / 2 : ℝ≥0∞) + rlctAtOn H y0 := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:  rw [show rlctAtOn (fun p : ℝ × Y => p.1 ^ 2 + H p.2) (0, y0)
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:    have hble : (bN : ℝ≥0∞) ≤ rlctAtOn H y0 := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:      unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:`rlctAtOn (x² + H) (0, y0) = 1/2 + rlctAtOn H y0`. The `le_antisymm` of the integrability (`≥`) and
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:    rlctAtOn (fun p : ℝ × Y => p.1 ^ 2 + H p.2) (0, y0) = (1 / 2 : ℝ≥0∞) + rlctAtOn H y0 :=
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:transports along `chartN m Y` (measure-preserving, `rlctAtOn_comp_homeomorph`), peels one `xᵢ²` off
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:Result: `rlctAtOn (∑ᵢ xᵢ² + G²) (0, y0) = n/2 + rlctAtOn (G²) y0` — the S1.5 wire-in target. -/
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:    rlctAtOn (fun p : (Fin n → ℝ) × Y => (∑ i, p.1 i ^ 2) + G p.2 ^ 2) (0, y0)
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:      = (n : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) y0 := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:    have hrhs : (↑(0:ℕ) : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) y0
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:        = rlctAtOn (fun y => G y ^ 2) y0 := by simp
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:    have hkey := rlctAtOn_comp_homeomorph e hMP e.measurableEmbedding
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean:    have hkey := rlctAtOn_comp_homeomorph (chartN m Y).symm hMP
lean/DLNFibre/DLN/RLCT/Skeleton.lean:on `rlctAtOn` (general singular block `Y`; the regular block is `Fin n → ℝ` at the origin).
lean/DLNFibre/DLN/RLCT/Skeleton.lean:`n/2 + ⊤ = ⊤` while the joint side need not be — `rlctAtOn_zero_eq_top`). Guarded by `hGmeas`
lean/DLNFibre/DLN/RLCT/Skeleton.lean:    rlctAtOn (fun p : (Fin n → ℝ) × Y => (∑ i, p.1 i ^ 2) + G p.2 ^ 2) (0, y0)
lean/DLNFibre/DLN/RLCT/Skeleton.lean:      = (n : ENNReal) / 2 + rlctAtOn (fun y => G y ^ 2) y0 :=
lean/DLNFibre/DLN/RLCT/Skeleton.lean:(unit Jacobian, not `det ±1`), so it routes through `rlctAtOn_unit_invariant_aux` + germ-locality, NOT
lean/DLNFibre/DLN/RLCT/Skeleton.lean:`rlctAtOn_comp_homeomorph` — its own substantial lemma (Codex g146; ~600–1500 lines; consult-gated, task
lean/DLNFibre/DLN/RLCT/Skeleton.lean:`rlctAtOn(core) 0`; the chart exponents realise `½·min_t Mval(t)`. This is **NOT** a chart↔`Adm`
lean/DLNFibre/DLN/RLCT/Skeleton.lean:`prod ≡ 0` again. Either way the core `dlnLoss M 0 ≡ 0`, so `rlctAtOn = ⊤`, while the right side
lean/DLNFibre/DLN/RLCT/Skeleton.lean:      rlctAtOn (fun A : Params M =>
lean/DLNFibre/DLN/RLCT/Skeleton.lean:reduced core `dlnLoss M 0` degenerates — `prod M ≡ 0`, so its local RLCT is `⊤` (`rlctAtOn_zero_eq_top`)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:the **reduced singular core** `rlctAtOn (dlnLoss M 0) 0` on the reduced widths `M = H−r`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:`rlctAtOn (dlnLoss M 0) 0`, the core RLCT at its deepest point — NOT on the closed form
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:`ofReal(lambdaCore M)`. Folding the core value `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` is
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:(`rlctAtOn_squeeze`), not the
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:* `coreAbsorb_rlct`: the MP route — `measurePreserving_coreShear` (`#83`) ⟹ `rlctAtOn_comp_homeomorph`
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:* `regAbsorb_rlct`: the LOCAL route — `rlctAtOn_boundedUnit_localHomeomorph` (`#72`), which takes
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:honest gauge geometry is local). `rlctAtOn` is local, so the squeeze (`rlctAtOn_squeeze`) is the right
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:  via `measurePreserving_coreShear` ⟹ `rlctAtOn_comp_homeomorph` (NO derivative/Jacobian bookkeeping —
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:  continuous function keeps GLOBAL measurability (so `loss_squeeze`/`rlctAtOn_squeeze` are unaffected);
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:  `rlctAtOn_boundedUnit_localHomeomorph`, crux2 #72, which takes `π/πsymm` as bare functions + `Dπ` + an
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:  `rlctAtOn_boundedUnit_localHomeomorph` (crux2 #72): `regStraighten` is a local diffeo on an open `V ∋ 0`
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:  this field from it via `rlctAtOn_squeeze` (⟹ `rlctAtOn(Sreg+Score)`) + the analytic-unit diffeo bridge
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:  `rlctAtOn(Sreg+Score) = rlctAtOn(Sreg+coreΦ)` (`Ψ : S1 ↦ (I−K)·S1`, `rlctAtOn_comp_localDiffeo`). RLCT
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:    -- two-sided `c₁ = c₂ = 1` bound, then `rlctAtOn_squeeze` + the Params→flat transport (the SAME chain
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:    rw [← rlctAtOn_eq_rlctAt]
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:    have htrans := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:    refine rlctAtOn_squeeze (fun x => dlnLoss H B ((paramsEquivFlat H).symm x)) Φ wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:`rlctAt (dlnLoss H B) deepest = rlctAtOn Φ wstar`, where `Φ = ∑ regular² + dlnLoss M 0 (core)` and
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:`wstar = (paramsEquivFlat H) deepest`. Chain: `rlctAtOn_eq_rlctAt` (Params), Params→flat MP transport
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:(`rlctAtOn_comp_homeomorph` on `paramsEquivFlat H`), then `rlctAtOn_squeeze` consuming `loss_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:  -- refuted pointwise `coreΦ` sandwich to the RLCT-equality form — the `rlctAtOn_squeeze` + Params→flat
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:coordinates has the same RLCT as on `Params M`: `rlctAtOn (dlnLoss M 0 ∘ (paramsEquivFlat M).symm) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:= rlctAtOn (dlnLoss M 0) (fun _ => 0)`. Transport along the measure-preserving flattening
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:      = rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:  have key := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:core)` has RLCT `nReg/2 + rlctAtOn (dlnLoss M 0) 0`: the `nReg` nondegenerate quadratic directions
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:via `dlnLoss_nonneg`), the loss-independent gauge spectators peel off (`rlctAtOn_spectator_peel`),
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:and the reduced block's RLCT is `rlctAtOn (dlnLoss M 0) 0` (sub-7).
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:        + rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:  have hstep1 := rlctAtOn_comp_homeomorph Γ.split Γ.split_mp Γ.split.measurableEmbedding
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:  -- Step 3: spectator-peel `rlctAtOn (G²) (0,0) = rlctAtOn coreF 0` then sub-7.
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:    rlctAtOn_spectator_peel coreF (0 : Fin (flatDim M) → ℝ) (0 : Fin Γ.nGauge → ℝ)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:singular **core RLCT** `rlctAtOn (dlnLoss M 0) 0` on the reduced widths `M = H−r`. This is the gauge
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:chart's full content: it carries NO `lambdaCore` (R1's value `rlctAtOn (dlnLoss M 0) 0 =
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:        + rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:    nReg/2 + rlctAtOn(core)(deepest-core) ≤ rlctAt (dlnLoss H B) v   (at a general optimal `v`)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:producer's outputs as hypotheses (the chart transfer `rlctAt (dlnLoss H B) v = rlctAtOn F (0,t0)`,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:banked `rlctAtOn_boundedUnit_localHomeomorph` discharges it; the post-chart sum-of-squares form
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:comparison `∑s² + R ≤ C·F` near `(0,t0)`), the engine gives `nReg/2 + rlctAtOn R t0 ≤
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:`coreV := rlctAtOn R t0`. Mechanical: reuses the banked engine + the chart-transfer equality.
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:Setting `coreV := rlctAtOn R t0` (NOT a separate `v−core` map) makes `hAtV` the engine output; the
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:SOLE remaining obligation is `hCore : coreDeepest ≤ rlctAtOn R t0`, i.e. `rlctAtOn R 0 ≥
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:rlctAtOn (core) 0`.
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:factorization is FALSE here. BUT the D1 INEQUALITY STILL HOLDS: `rlctAtOn R 0 = coreDeepest = 3/2`
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:delivers `(★)`'s `hAtV` side: `nReg/2 + rlctAtOn R t0 ≤ rlctAt (dlnLoss H B) v`, with
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:`coreV := rlctAtOn R t0`. The hypotheses are EXACTLY the producer obligations:
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:  * `hchart` — the chart transfer (banked `rlctAtOn_boundedUnit_localHomeomorph` at the producer;
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:After this, the remaining D1 obligation is `hCore : coreDeepest ≤ rlctAtOn R t0` (PART (b)). -/
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), t0))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:    (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:leading-form comparison `hCore : coreDeepest ≤ rlctAtOn R t0` (PART (b)), the deepest point has
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), t0))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:    (hCore : coreDeepest ≤ rlctAtOn R t0) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:  have hAtV : (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v :=
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:    (rlctAt H (dlnLoss H B) v) m coreDeepest (rlctAtOn R t0) hDeepest hAtV hCore
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:germ-changing perturbation — so the identification is `r`-independent and TIGHT (`rlctAtOn R 0 =
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:`(t0, g0)`, i.e. `R = (core₀ ∘ fst) ∘ Φ` (`hRform`). Then `rlctAtOn R (t0,g0) = rlctAtOn core₀ t0`:
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:the diffeo transfer (`rlctAtOn_boundedUnit_localHomeomorph`) strips `Φ`, the spectator peel
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:(`rlctAtOn_spectator_peel`) drops the gauge factor. In particular `coreDeepest = rlctAtOn core₀ t0`
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:discharges the D1 `hCore : coreDeepest ≤ rlctAtOn R (t0,g0)` with EQUALITY (the G1 tightness).
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:Jacobian on an open `V ∋ (t0,g0)` (the raw-data `rlctAtOn_boundedUnit_localHomeomorph` form —
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:fire. `hCore : coreDeepest ≤ rlctAtOn R t0` STILL HOLDS at such `v` (verified EXACT:
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:`rlctAtOn R 0 = coreDeepest = 3/2` at that point — the `extra = nReg_v − nReg` Morse halves exactly
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:GENERAL `v`, `hCore` is discharged at the VALUE level (`rlctAtOn R 0 ≥ coreDeepest`), an open
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:    rlctAtOn R (t0, g0) = rlctAtOn core₀ t0 := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:  rw [rlctAtOn_boundedUnit_localHomeomorph (fun p : Reduced × Gauge => core₀ p.1) (t0, g0)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:  exact rlctAtOn_spectator_peel core₀ t0 g0 hG
lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitSmooth.lean:part. (Used at `wstar` to feed `rlctAtOn_comp_localDiffeo`, but holds at every base point.) -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:The general per-node mechanism's value step (g138 §5(5)): `rlctAtOn (core) 0 = ⨅ᵢ monomialThreshold`,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:`rlctAtOn F 0 = ⨅ᵢ monomialThreshold (d i)(k i)(h i)`. `le_antisymm`: (≤) any admissible `c'` has
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:give `∫⁻_U < ⊤` (`rlctAtOn_ge_of_integral_lt`). Mechanism-independent. `⨅ = ofReal(lambdaCore M)` is
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:theorem routeM_rlctAtOn_eq_iInf {N : ℕ} (F : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:    rlctAtOn F (0 : Fin N → ℝ) = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:  · apply rlctAtOn_le_of_adm_le F t
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:  · apply rlctAtOn_ge_of_integral_lt F hcover.Fmeas U hcover.Uopen hcover.Umem t
lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean:`hloss` hypothesis of `rlctAtOn_dlnLoss222_transport`.
lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean:the `hloss` hypothesis of `rlctAtOn_dlnLoss222_transport`, closing the seam end-to-end. Via
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  `rlctAtOn F (t • v) = rlctAtOn F v`. The germ at `t·v` pulls back under the scaling diffeo `w = t·w'`
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  (`rlctAtOn_comp_homeomorph`) to `t^D · (germ at v)`; the constant `t^D` is a unit
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  (`rlctAtOn_unit_invariant_aux`). Reachable from green primitives + the homogeneity hypothesis.
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  primitive" overestimate). `rlctAtOn F 0 ≤ rlctAtOn F v`: by `sSup_le` over admissible `c'` at `0`,
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  admissible at `s•v` ⟹ `c' ≤ rlctAtOn (s•v) = rlctAtOn v` (L1-a). NO Fatou / Varchenko / general
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:constant along the punctured ray: `rlctAtOn F (t • v) = rlctAtOn F v`. The scaling `σ_t : w ↦ t • w` is
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:peeled by `rlctAtOn_unit_invariant_aux`. (ii) DIRECT admissible-set bijection: `Ω ∋ t•v` admissible ⟺
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:(homogeneity), both finite-nonzero, so finiteness is preserved) — like `rlctAtOn_spectator_peel`'s
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:theorem rlctAtOn_ray_scaling_invariant
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:    rlctAtOn F (t • v) = rlctAtOn F v := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  -- assemble: `rlctAtOn F (t•v) = wThr F 1 {t•v} = wThr (F∘σ) (t^N) {v} = wThr (F∘σ) 1 {v}`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  rw [rlctAtOn, htrans, hpeel]
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  have := rlctAtOn_unit_invariant_aux F (fun _ : Fin N → ℝ => t ^ D) v (t ^ D) (t ^ D)
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  rw [rlctAtOn, weightedThreshold] at this ⊢
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:point `0 = lim_{s→0} s • v` has RLCT `≤` the (ray-constant) RLCT at `v`: `rlctAtOn F 0 ≤ rlctAtOn F v`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:**Proof = nbhd-monotonicity of `rlctAtOn`, ~10 lines from the `sSup`/`∃Ω∋·` def:** for each admissible
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:is a nbhd of `s • v` too ⟹ `c'` admissible at `s • v` ⟹ `c' ≤ rlctAtOn F (s•v) = rlctAtOn F v` (L1-a);
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:theorem rlctAtOn_lsc_at_origin
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:    rlctAtOn F (0 : Fin N → ℝ) ≤ rlctAtOn F v := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  have hle_sv : (c' : ℝ≥0∞) ≤ rlctAtOn F (s • v) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:    rw [rlctAtOn, weightedThreshold]; exact le_sSup hadm_sv
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  rw [rlctAtOn_ray_scaling_invariant F v D s hspos hFmeas hhomog] at hle_sv
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:deepest point `0` has the minimal local RLCT over all `v`: `rlctAtOn F 0 ≤ rlctAtOn F v`. This is
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:exactly `rlctAtOn_lsc_at_origin` — the assembly point where L1-a (ray-constancy) + L1-b (semicontinuity
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:    rlctAtOn F (0 : Fin N → ℝ) ≤ rlctAtOn F v :=
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  rlctAtOn_lsc_at_origin F v D hFmeas hhomog
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  `rlctAt(dlnLoss H B) deepest = nReg/2 + rlctAtOn(core) (deepest-core)`   [L2 at deepest, PROVEN]
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  `rlctAt(dlnLoss H B) v       = nReg/2 + rlctAtOn(core) (v-core)`          [L2-at-`v`, the open piece]
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:  `rlctAtOn(core) (deepest-core) ≤ rlctAtOn(core) (v-core)`                 [CORE-P1, PROVEN]
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:`descentStep : rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss (1,1,2) 0) 0 = 2/2 + rlctAtOn(child)`.
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:NUMERICALLY equals the committed `case222_rlctAtOn_eq` (`Case222Rlct`); this is a value coincidence — the
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:file does NOT prove `rlctAtOn flatCore (0,0) = rlctAtOn (dlnLoss H222 0) deepest222` (that is exactly the
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:/-- The `(2,2,2)`-node `ReducedTransport` (the det-1 MP descent closing `rlctAtOn (G²) 0 = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:/-- **The per-node descent step** for the `(2,2,2)` anchor: `rlctAtOn flatCore (0,0) = 2/2 + rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:    rlctAtOn routeMNodeDescent222.flatCore (0, 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:      = (2 : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss (schurState M222route M222_hlo).red 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:NUMERICALLY equals the committed `(2,2,2)` RLCT `case222_rlctAtOn_eq = 3/2` — a coincidence, NOT an
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:identification: this proves `rlctAtOn flatCore222 (0,0) = 3/2`, not `rlctAtOn (dlnLoss H222 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:    (hred : rlctAtOn (dlnLoss (schurState M222route M222_hlo).red 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:    rlctAtOn routeMNodeDescent222.flatCore (0, 0) = 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:The two `⊤`s the oscillation conflated are DIFFERENT objects: (i) the GEOMETRIC `rlctAtOn (dlnLoss M 0) = ⊤`
lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:(root `rlctAtOn = ½·minAdm`) is the COVER's job (`IsRouteMCover`, #104), NOT `foldFamily`. ANCHORED:
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverBridge.lean:descending to the child's box — NOT a point-RLCT. The clean point-min `rlctAtOn (dlnLoss M 0) 0 =
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverBridge.lean:min{mk/2, rlctAtOn core 0}` is a true VALUE identity (the NUMBER matches the point threshold), but the
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverBridge.lean:`hKint`), which `rlctAtOn K 0` (the point) does NOT supply — the divisor-vs-point gap (the (2,2,2)
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverBridge.lean:threshold `rlctAtOn K 0`: the antecedent is the point number, the consequent is the full-box obligation.
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverBridge.lean:`BoxThresholdBridge K`: for every bounded measurable box `Vz` and every `c' < rlctAtOn K 0`, the
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverBridge.lean:integrable on EVERY bounded box: for bounded measurable `Vz` and `c' < rlctAtOn K 0`, `|K|^{−c'}` is
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverBridge.lean:point `0` is the global-min-RLCT point, so the point threshold `rlctAtOn K 0` governs the whole box —
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverBridge.lean:  ∀ (c' : NNReal), (c' : ℝ≥0∞) < rlctAtOn K 0 →
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverBridge.lean:/-- **The bridge discharges the per-chart `hKint`.** Given `BoxThresholdBridge K` and `c' < rlctAtOn
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverBridge.lean:    (hc'core : (c' : ℝ≥0∞) < rlctAtOn K 0)
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:genuine `≃L` (block upper-triangular, invertible diagonal). `regAbsorb`/`rlctAtOn_comp_localDiffeo`
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCover.lean:  The PROVEN general machinery is instead the per-node SQUEEZE `rlctAtOn = nReg/2 + rlctAtOn(reduced)`
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCover.lean:  (`schur_recursion_step_squeeze` + `rlctAtOn_layerReduced_transport`) — but that computes `rlctAtOn`
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCover.lean:  The squeeze is the wrong SHAPE for this field: lifting `rlctAtOn`-divergence to box-integral divergence
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:value `rlctAtOn myF222 0 = 3/2`, where `myF222 = ‖A·B‖²` in the explicit `a00=0..b11=7` flat order
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:(the seam's `dlnLoss ∘ e222.symm`). The cover→`rlctAtOn` spine is `Foundations.S1Cover`; the
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:box divergence (the `≤`-direction's analytic atom, fed to `rlctAtOn_le_of_box_diverges`) and — to
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:come — the concrete 3-deep chart cover and the final `rlctAtOn myF222 0 = 3/2`. The per-axis 1-D
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:For the `≤` direction (`rlctAtOn_le_of_box_diverges`), a leaf integrand at-or-above its threshold
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:`rlctAtOn_le_of_box_diverges`). Proof: lower-bound by the open box `(0, ε)^d` (`lintegral_mono_set`),
lean/DLNFibre/DLN/RLCT/Validate/RRR.lean:    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:  its transport lemmas (`rlctAtOn_reduced_transport`, `schur_recursion_step_sound`/`_squeeze`), and the
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:crux2's banked `rlctAtOn_reduced_transport` datum (det-1 measure-preserving reindex) closing the descent:
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0` at the child's deepest point. `Y` is the post-blow-up
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) (fun _ => 0)`. Consumes crux2's banked
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:`rlctAtOn_reduced_transport` (det-1 MP); the bundled datum + the anchored `hzero` give the
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:    rlctAtOn (fun y => rt.G y ^ 2) (0 : Y)
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:      = rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:  rlctAtOn_reduced_transport S rt.G rt.redEmbed rt.hmp rt.hemb _ rt.hzero rt.hredCore
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:(the chart family always has ≥1 leaf) — `routeM_rlctAtOn_eq_iInf` needs `[Nonempty ι]` for the achiever-side
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:    --   • `rlctAtOn_layerReduced_transport` — the descent cert generalised to `dlnLoss (redChain t M)`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:`[Nonempty ι]` `routeM_rlctAtOn_eq_iInf` needs for the achiever-side `iInf_le` (crux2's bridge catch). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMCoverLemmas.lean:  divergence `∫⁻_{[−ε,ε]^N} |F|^{−c'} = ⊤` (the same content as `rlctAtOn_le_of_box_diverges`'s
lean/DLNFibre/DLN/RLCT/Validate/RouteMCoverLemmas.lean:of `rlctAtOn_le_of_box_diverges` (the `≤`-direction localisation), repackaged to the `¬ IntegrableOn`
lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean:(det `±1`, NOT a blow-up — so it transports `rlctAtOn` by `rlctAtOn_comp_homeomorph`, the genuine
lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean:via `rlctAtOn_comp_homeomorph`.
lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean:for transporting `rlctAtOn` via `rlctAtOn_comp_homeomorph`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean:cover assembly feeds to `rlctAtOn_comp_homeomorph`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:`rlctAtOn_squeeze` downstream needs the absorbed `Φ` GLOBALLY measurable — a local diffeo breaks it).
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:`rlctAtOn` is a germ at `0` and the loss-squeeze is local, the germ-at-`0` agreement is all that is
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:agreement PIN 2's loss-squeeze consumes (`rlctAtOn`/the squeeze are local). -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:`rlctAtOn_regAbsorb_reduce` needs. Abstract over `Ereg` (the concrete general-L residual + its
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:/-- **The reg-output is core-independent** (`hra_regdep` for `rlctAtOn_regAbsorb_reduce`): the reg
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:- the cover value `rlctAtOn myF222 0 = 3/2` (`rlctAtOn_myF222_eq`, `Case222CoverGETail`: the geometric
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:  `≥`-cover — clean-three, S2-free — antisymmetric with the cited `≤`-half `rlctAtOn_myF222_le`);
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:- the measure-preserving transport `rlctAtOn (dlnLoss H222 0) deepest222 = rlctAtOn myF222 0`
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:  (`rlctAtOn_dlnLoss222_transport`, `ParamsFlat222`).
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:/-- **The `(2,2,2)` core RLCT (on `Params`).** `rlctAtOn (dlnLoss H222 0) deepest222 = 3/2`: the
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:(`rlctAtOn_dlnLoss222_transport`) carry the cover value (`rlctAtOn_myF222_eq`) from `Fin 8 → ℝ` to the
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:theorem case222_rlctAtOn_eq : rlctAtOn (dlnLoss H222 0) deepest222 = 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:  rw [rlctAtOn_dlnLoss222_transport myF222 dlnLoss222_eq_myF222, rlctAtOn_myF222_eq]
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:(`rlctAtOn_myF222_ge'`) is axiom-clean (S2-free); the value rests on the cited `≤`-bound (`monomial_rlct`,
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:Aoyagi/Watanabe) via `rlctAtOn_myF222_le`. Mirror of `case111_rlct`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:  rw [← rlctAtOn_eq_rlctAt, case222_rlctAtOn_eq]
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:`resolution_charts` (core form): `rlctAtOn (dlnLoss M 0) deepest = ⨅ monomialThreshold (d i)(k i)(h i)`.
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:      rlctAtOn (fun A : Params H222 =>
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:          case222_rlctAtOn_eq, iInf_unique, case222_unit_leaf_threshold]⟩
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:**Scope: core-only** (`rlctAtOn(dlnLoss M 0) 0`, `M = H − r`). The regular `[−r²+r(H⁰+Hᴸ)]/2` shift is
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSmooth.lean:`rlctAtOn_comp_localDiffeo` consumer uses global continuity for the absorbed map's global measurability).
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:- The PROVEN squeeze (`rlctAtOn_squeeze`, `schur_recursion_step_squeeze`) computes the POINT
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:  RLCT `rlctAtOn (routeMCore M) 0` additively along the achiever path, giving the upper bound
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:  `rlctAtOn (routeMCore M) 0 ≤ ½·minAdm M`. That is STRICTLY WEAKER than this atom: `rlctAtOn ≤ t`
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:  `rlctAtOn ≤ t` would be the forbidden value-correct-germ-degenerate fill — the trap; NOT done.)
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:This gives the lower bound `rlctAtOn (routeMCore M) 0 ≤ ½·minAdm M` (`cover_ge_div`, via
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:`rlctAtOn ≤ ½·minAdm M`, strictly weaker than this BOUNDARY box-divergence; the route is the
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:* Step Θ (`rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb`): `rlctAtOn(reg²+coreF∘bareAbsorb) =
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:  rlctAtOn(reg²+coreF∘conjAbsorb)` at `0`, via the MP core-shear `Θ = coreShearHomeo (schurCutoffShiftConj
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:  − schurCutoffShift)` (det-1, basepoint-fixing, reg-fixing; `rlctAtOn_comp_homeomorph`, NO derivative).
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:fixing the reg slot, so `rlctAtOn_comp_homeomorph` peels it — `rlctAtOn(reg²+coreF∘bareAbsorb) =
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:rlctAtOn(reg²+coreF∘conjAbsorb)` with NO derivative bookkeeping (atom-free). -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:the reg slot with `bareAbsorb ∘ Θ = conjAbsorb`, so `rlctAtOn_comp_homeomorph` peels it. Atom-free. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:theorem rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb (H : Fin (L + 1) → ℕ) (r : ℕ)
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:  have hkey := rlctAtOn_comp_homeomorph Θ hΘmp Θ.measurableEmbedding G 0
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:(`core₀ = rlctAtOn`-equal to the deepest core, so `coreDeepest = rlctAtOn core₀ t0`).
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:  /-- The IFT chart transfer: `rlctAt (dlnLoss H B) v = rlctAtOn F (0, (t0,g0))`. -/
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:  hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), (t0, g0))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:  hcoreDeepest : coreDeepest = rlctAtOn core₀ t0
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), (t0, g0)))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:    (hcoreDeepest : coreDeepest = rlctAtOn core₀ t0)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:      = rlctAtOn (fun p : (Fin 0 → ℝ) × (Reduced × Gauge) => (∑ i, p.1 i ^ 2) + 1)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:      (rlctAtOn (fun _ : Reduced => (1 : ℝ)) t0)) :=
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:  ⟨GeneralVChartL2.ofExactGerm H B v (rlctAtOn (fun _ : Reduced => (1 : ℝ)) t0)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:  have hCoreEq : rlctAtOn Γ.R (Γ.t0, Γ.g0) = rlctAtOn Γ.core₀ Γ.t0 :=
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:  -- Step 2: `hCore : coreDeepest ≤ rlctAtOn R (t0,g0)` — equality from `hcoreDeepest` + `hCoreEq`.
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:  have hCore : coreDeepest ≤ rlctAtOn Γ.R (Γ.t0, Γ.g0) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescentBuild.lean:    rlctAtOn (RouteMNodeDescent.ofNodePresentation transport flatCore T bcol SΓ
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescentBuild.lean:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean:/-! ## S1.3 on a general domain — `rlctAtOn` unit-invariance
lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean:chart-local reduction lives on `rlctAtOn` over a PRODUCT domain `(Fin n → ℝ) × Params M'`, not on
lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean:`rlctAtOn` level over a general `[MeasureSpace] [TopologicalSpace] [OpensMeasurableSpace]` source —
lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean:/-- **S1.3 (general domain).** The RLCT threshold `rlctAtOn` is invariant under multiplying the
lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean:`rlctAtOn (u·F) w* = rlctAtOn F w*`. The general-domain twin of `rlct_unit_invariant_aux` (drops the
lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean:`rlctAtOn_eq_rlctAt`. -/
lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean:theorem rlctAtOn_unit_invariant_aux {M : Type*} [MeasureSpace M] [TopologicalSpace M]
lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean:    rlctAtOn (fun w => u w * F w) wstar = rlctAtOn F wstar := by
lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:`rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`, with `Φscore` carrying the matrix-Schur `Score` and
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:Given those two, `rlctAtOn_diffeo_bridge_of` discharges `hstep2` by germ-locality
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:(`rlctAtOn_germ_local`) + RLCT-invariance under a local diffeo (`rlctAtOn_comp_localDiffeo`). The proof
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:`wstar`, then `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`. Proof: germ-locality replaces `Φscore`
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:by `Φcore ∘ Psi`, and `rlctAtOn_comp_localDiffeo` strips `Psi`. This is the exact shape `hstep2`
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:theorem rlctAtOn_diffeo_bridge_of {M : Type*}
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:    rlctAtOn Φscore wstar = rlctAtOn Φcore wstar := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:  rw [← rlctAtOn_germ_local (fun x => Φcore (Psi x)) Φscore wstar hcomp]
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:  exact rlctAtOn_comp_localDiffeo Φcore wstar Psi e hcontdiff hderiv hfix
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:`rlctOf := fun M => rlctAtOn (dlnLoss M 0) (deepest)`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:`H¹ = 0`: there the loss is an empty sum `≡ 0`, so `rlctAt = ⊤` (`rlctAtOn_zero_eq_top`), while the
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:`rlctAtOn (∑ᵢ xᵢ²) 0 = (m+1)/2` on the product Lebesgue measure, bridged from
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:measure-preserving homeomorph `toLp`. Generalises `Case212.rlctAtOn_blockG_eq_one` (`m = 1`). -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:theorem sumSq_rlctAtOn_finN (m : ℕ) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:    rlctAtOn (fun x : Fin (m + 1) → ℝ => ∑ i, x i ^ 2) (0 : Fin (m + 1) → ℝ)
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:  have key := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:theorem sumSq_rlctAtOn_finN_pos (n : ℕ) (hn : 0 < n) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:    rlctAtOn (fun x : Fin n → ℝ => ∑ i, x i ^ 2) (0 : Fin n → ℝ) = ((n : ℕ) / 2 : ℝ≥0∞) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:  exact sumSq_rlctAtOn_finN m
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:(`Homeomorph.addRight`), and apply `sumSq_rlctAtOn_finN`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:  -- Step 1: rlctAt = rlctAtOn (loss ∘ p.symm) at c (flatten via the homeomorph p.symm)
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:  rw [← rlctAtOn_eq_rlctAt]
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:  have hstep1 := rlctAtOn_comp_homeomorph p.symm hpmp hpemb (dlnLoss H B) c
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:  have hstep2 := rlctAtOn_comp_homeomorph τ hτmp hτemb (fun x => dlnLoss H B (p.symm x)) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:  rw [hcomp, sumSq_rlctAtOn_finN_pos n hnpos]
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:`rlctAtOn (dlnLoss M 0) (chart (0,0)) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` from a measure-preserving
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:Composes `dlnLoss_chart_squeeze_descent` (chart transport via `rlctAtOn_comp_homeomorph` + the chart-free
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:the chart image `χ (0,0)` splits: `rlctAtOn (dlnLoss M 0) (χ (0,0)) = nReg/2 + rlctAtOn (G²) 0`. Composes
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:`rlctAtOn_comp_homeomorph` (transport `dlnLoss` to the chart source) with `schur_recursion_step_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:    rlctAtOn (dlnLoss M 0) (chart (0, 0))
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:  -- transport `dlnLoss M 0` to the chart source: `rlctAtOn (dlnLoss M 0) (χ (0,0)) = rlctAtOn (dlnLoss ∘ χ) (0,0)`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:  rw [← rlctAtOn_comp_homeomorph chart hmp hemb (dlnLoss M 0) (0, 0)]
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:`rlctAtOn (dlnLoss M 0) (χ (0,0)) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`. Composes
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:`dlnLoss_chart_squeeze_descent` (chart + squeeze → `nReg/2 + rlctAtOn (G²) 0`, `G = transport.G`) with
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:`ReducedTransport.descent` (`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`); the two legs share the SAME
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:    rlctAtOn (dlnLoss M 0) (chart (0, 0))
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) := by
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:The `(2,2,2)` value `rlctAtOn (dlnLoss H222 0) deepest222 = 3/2` routed through the **general**
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:`IsRouteMCover` / `routeM_rlctAtOn_eq_iInf` engine (the path that generalizes to all rank patterns),
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:rather than through the concrete `rlctAtOn_myF222_eq` of `Case222Rlct`.
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:end-to-end in `Case222Rlct` (`case222_rlctAtOn_eq` / `case222_rlct`), via the concrete geometric
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:`≥`-cover (`rlctAtOn_myF222_eq`, clean-three, S2-free) antisymmetric with the cited `≤`-half
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:value through the general abstraction — exercising `IsRouteMCover` + `routeM_rlctAtOn_eq_iInf`
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:* `routeM_rlctAtOn_eq_iInf` gives `rlctAtOn myF222 0 = ⨅ i, monomialThreshold (…) = 3/2`
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:* `rlctAtOn_dlnLoss222_transport` (the `e222` measure-preserving reindex, via `dlnLoss222_eq_myF222`)
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:/-- **The `(2,2,2)` cover value through the general engine.** `rlctAtOn myF222 0 = 3/2`, derived by
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:feeding `isRouteMCover_222` to the GENERAL `routeM_rlctAtOn_eq_iInf` (`= ⨅ monomialThreshold`) and
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:`rlctAtOn_myF222_eq`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:theorem rlctAtOn_myF222_eq_routeM : rlctAtOn myF222 (0 : Fin 8 → ℝ) = 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:  rw [routeM_rlctAtOn_eq_iInf myF222 openBox (Fin 1) routeM222D routeM222K routeM222H
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:/-- **The `(2,2,2)` R1 leg through the general engine** (the milestone). `rlctAtOn (dlnLoss H222 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:deepest222 = 3/2`, derived through the general `IsRouteMCover` / `routeM_rlctAtOn_eq_iInf` path:
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:transport the loss to `myF222` (`rlctAtOn_dlnLoss222_transport` + `dlnLoss222_eq_myF222`), then read
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:off the general-engine cover value (`rlctAtOn_myF222_eq_routeM`). Reproduces `Case222Rlct`'s
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:`case222_rlctAtOn_eq` (which goes through the concrete cover) via the GENERAL abstraction — the
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:theorem case222_rlctAtOn_eq_routeM :
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:    rlctAtOn (dlnLoss H222 0) deepest222 = 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:  rw [rlctAtOn_dlnLoss222_transport myF222 dlnLoss222_eq_myF222, rlctAtOn_myF222_eq_routeM]
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:reduced singular core RLCT `rlctAtOn (dlnLoss M 0) 0`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:        + rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:`rlctAtOn myF222 0 = ⨅ᵢ monomialThreshold (dᵢ)(kᵢ)(hᵢ)` (the cover-form; `fm`'s `⨅ = 3/2` wraps it).
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:integral, never an `rlctAtOn` transport). The `≤` direction needs only ONE binding leaf chart
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:(`rlctAtOn_le_of_box_diverges` + `monomialIntegrand_lintegral_box_eq_top`); the `≥` direction needs
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:cover computes; the seam (`rlctAtOn_dlnLoss222_transport`) identifies `dlnLoss H222 0 = myF222 ∘ e222`.
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:NOT an `rlctAtOn` transport). -/
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:The `≤` direction (`rlctAtOn_le_of_box_diverges`) needs ONE binding leaf chart `φ` whose pulled-back
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:/-! ## The `≤`-direction (`rlctAtOn myF222 0 ≤ 3/2`)
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:`monomialIntegrand · Uval^{−c'}`. Discharges `rlctAtOn_le_of_box_diverges`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:/-- **The `≤`-direction.** `rlctAtOn myF222 0 ≤ 3/2`. For every `c' > 3/2`, `ε > 0`, the cube threshold
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:`coordZero_null`), diverge (`leaf_box_div`). Then `rlctAtOn_le_of_box_diverges`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:theorem rlctAtOn_myF222_le : rlctAtOn myF222 0 ≤ 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:  apply rlctAtOn_le_of_box_diverges myF222 (3 / 2)
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:family in EXACTLY the `(ι, d, k, h)`-tuple shape `routeM_rlctAtOn_eq_iInf`/`resolution_charts`
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:`resolution_charts` is `rlctAtOn(core) = ⨅ monomialThreshold` — an equality whose VALUE is this
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:lane (`= ½·minAdm = lambdaCore`) but whose `rlctAtOn = ⨅` content is the ANALYTIC COVER: the two
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:`routeM_rlctAtOn_eq_iInf` and the gate `resolution_charts` consume the SPLIT tuple `(d, k, h)`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:`resolution_charts` is `rlctAtOn(core) = ⨅ monomialThreshold`. The VALUE (`= ½·minAdm = lambdaCore`)
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:is the lane above; the `rlctAtOn = ⨅` content is the ANALYTIC COVER (`IsRouteMCover`'s two legs).
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:`⨅ monomialThreshold` is the core RLCT at the deepest point. Via `routeM_rlctAtOn_eq_iInf` (the
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:bridge) ∘ `rlctAtOn_routeMCore_transport` (flat ↔ params). The residual `hcover` is the ONLY missing
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:      rlctAtOn (fun A : Params M =>
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:  have hbridge := routeM_rlctAtOn_eq_iInf (routeMCore M) (routeMBaseNbhd M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:  rw [← rlctAtOn_routeMCore_transport M]
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:/-- **The `(2,2,2)` `≥`-direction headline** (downstream restatement). `rlctAtOn myF222 0 ≥ 3/2` via
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:`rlctAtOn_ge_of_integral_lt` on `openBox ∋ 0` (`myF222_threshold_lt_top'`). -/
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:theorem rlctAtOn_myF222_ge' : (3 : ℝ≥0∞) / 2 ≤ rlctAtOn myF222 0 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:  apply rlctAtOn_ge_of_integral_lt myF222 ?_ openBox isOpen_openBox mem_openBox_zero (3 / 2)
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:/-- **The `(2,2,2)` resolution value (`#80`): `rlctAtOn myF222 0 = 3/2`.** `le_antisymm` of the gated
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:`≤`-half (`rlctAtOn_myF222_le`, `Case222Resolution` @dd40c45) and the `≥`-half proven here
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:(`rlctAtOn_myF222_ge'`). Every leaf threshold is `3/2` (`Case222Value`), so this is the `⨅`-value. The
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:theorem rlctAtOn_myF222_eq : rlctAtOn myF222 0 = 3 / 2 :=
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:  le_antisymm rlctAtOn_myF222_le rlctAtOn_myF222_ge'
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotRowWLOG.lean:`rlctAtOn_comp_homeomorph`). So the infimum is preserved — the row dual of the colPerm lemma. -/
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotRowWLOG.lean:    have htrans := rlctAtOn_comp_homeomorph τ hmp hemb (dlnLoss H Bp) w
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotRowWLOG.lean:    rw [hcomp, rlctAtOn_eq_rlctAt, rlctAtOn_eq_rlctAt] at htrans
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:off the WHOLE sum (`rlctAtOn_comp_homeomorph` + `bareAbsorb_thetaConj_eq_conjAbsorb`): the bare absorbed-core
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:  have hkey := rlctAtOn_comp_homeomorph Θ hΘmp Θ.measurableEmbedding
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:`rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb` (@439) converts bare↔conj with NO drag (`Θ` fixes `q.1`) — and
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:lifting back via the `rlctAtOn_regAbsorb_reduce2` (π̃ option-D) LOCAL-DIFFEO reg-absorb (which preserves zero
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:`rlctAtOn_comp_localDiffeo` + the `DeepestL2ConjSmooth` `hTilde` lemmas (the conj one rides the value-fold
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:/-- **π̃ reg-absorb peel, CONJ side (LANDED).** The `hpeel` input `rlctAtOn_regAbsorb_reduce2` needs for
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:annihilates), then `rlctAtOn_comp_localDiffeo` peels it. The conj analogue of the wire's bare `hTilde`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:  have hkey := rlctAtOn_comp_localDiffeo
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:  have hkey := rlctAtOn_comp_localDiffeo
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:/-- **The gauge-reg reg-absorb (CONJ), via `rlctAtOn_regAbsorb_reduce2` + `regAbsorbPeel_conj`.** Straightens
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:  rlctAtOn_regAbsorb_reduce2 (deepestCoreAbsorbConj H r B hB hr hL hDA)
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:/-- **The gauge-reg reg-absorb (BARE), via `rlctAtOn_regAbsorb_reduce2` + `regAbsorbPeel_bare`.** -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:  rlctAtOn_regAbsorb_reduce2 (deepestCoreAbsorb H r hr hL)
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:`rlctAtOn_comp_localDiffeo` + the `DeepestL2ConjSmooth` `hTilde` lemmas. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:  -- Rewrite `(regStraighten q).1` to `deepestEFull q` (hregval) under both `rlctAtOn` binders.
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:    ← rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb H r B hB hr hL hDA hbdy,
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:`split` (`rlctAtOn_comp_homeomorph`, `split wstar = 0`). `rlctAtOn(R'∘split + coreF∘conjAbsorb∘split) wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:= rlctAtOn(R'∘split + coreF∘bareAbsorb∘split) wstar`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:  -- Transport the `0`-form LINK2 to flat `wstar` via `rlctAtOn_comp_homeomorph split` (both sides).
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:  have hconj := rlctAtOn_comp_homeomorph split hsplit_mp split.measurableEmbedding
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:  have hbare := rlctAtOn_comp_homeomorph split hsplit_mp split.measurableEmbedding
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:    rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:producer / `hfin`: purely `dlnLoss` + the column permutation + the banked `rlctAtOn`-MP-invariance.
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:   `rlctAtOn_comp_homeomorph` + an `iInf`-over-bijection congruence).
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:`rlctAtOn_comp_homeomorph`). So the infimum is preserved — choice-independent, through the
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:    have htrans := rlctAtOn_comp_homeomorph τ hmp hemb (dlnLoss H Bp) w
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:    rw [hcomp, rlctAtOn_eq_rlctAt, rlctAtOn_eq_rlctAt] at htrans
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:The `≥` half of the `(2,2,2)` resolution value: `rlctAtOn myF222 0 ≥ 3/2`. Together with the gated
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:`≤`-half (`rlctAtOn_myF222_le`, `Case222Resolution`) this pins `rlctAtOn myF222 0 = 3/2 = ⨅`.
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:## The reduction (gated `rlctAtOn_ge_of_integral_lt`) — on a BOUNDED open box
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:`rlctAtOn_ge_of_integral_lt` reduces `3/2 ≤ rlctAtOn myF222 0` to the threshold-integral finiteness
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:SPECIFY stage: `rlctAtOn_myF222_ge` headline verified (reduces to `hfin` over `openBox`); `hfin`
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:(`rlctAtOn_myF222_ge'`, `rlctAtOn_myF222_eq`), where `p0_summand_via_tail` (the `p = 0` chain) and the
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:(`aPivotSummand_lt_top` / `myF222_threshold_lintegral_lt_top` / `rlctAtOn_myF222_ge`) were superseded by
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      -- `DeepestGaugeChart.loss_squeeze` field): `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:  -- field is the RLCT-EQUALITY `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`. We prove it from the TRUE
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:  -- Score-sandwich `hsq` (`deepest_loss_squeeze`, axiom-clean) via `rlctAtOn_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:  -- (⟹ `rlctAtOn(Sreg_E + Score)`) + the analytic-unit diffeo bridge `rlctAtOn(Sreg_E + Score) =
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:  -- rlctAtOn(Sreg_E + coreΦ)` (`Ψ : S1 ↦ (I−K)·S1`). `Score = frobSqMat(Rcore)` (the `hscore`/`hScoreDef`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:  -- **ROUTE-B CLOSE (2026-06-25).** Target: `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)` (the migrated
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:  -- field). TWO steps: (1) `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + Score)` — the TRUE Score-sandwich `hsq`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:  -- fed to `rlctAtOn_squeeze` after the Params→flat MP transport; (2) the diffeo bridge
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:  -- `rlctAtOn(Sreg_E + Score) = rlctAtOn(Sreg_E + coreΦ)` via `Ψ : S1 ↦ (I−K)·S1` (`rlctAtOn_comp_localDiffeo`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:  -- **Step 1: `rlctAt(dlnLoss) = rlctAtOn Φscore wstar`** (Params→flat MP transport + `rlctAtOn_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      = rlctAtOn Φscore wstar := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    rw [← rlctAtOn_eq_rlctAt]
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    have htrans := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    refine rlctAtOn_squeeze (fun x => dlnLoss H B ((paramsEquivFlat H).symm x)) Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:  have hstep2 : rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      -- `DeepestGaugeChart.loss_squeeze` field): `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    -- field is the RLCT-EQUALITY `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`. We prove it from the TRUE
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    -- Score-sandwich `hsq` (`deepest_loss_squeeze`, axiom-clean) via `rlctAtOn_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    -- (⟹ `rlctAtOn(Sreg_E + Score)`) + the analytic-unit diffeo bridge `rlctAtOn(Sreg_E + Score) =
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    -- rlctAtOn(Sreg_E + coreΦ)` (`Ψ : S1 ↦ (I−K)·S1`). `Score = frobSqMat(Rcore)` (the `hscore`/`hScoreDef`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    -- **ROUTE-B CLOSE (2026-06-25).** Target: `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)` (the migrated
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    -- field). TWO steps: (1) `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + Score)` — the TRUE Score-sandwich `hsq`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    -- fed to `rlctAtOn_squeeze` after the Params→flat MP transport; (2) the diffeo bridge
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    -- `rlctAtOn(Sreg_E + Score) = rlctAtOn(Sreg_E + coreΦ)` via `Ψ : S1 ↦ (I−K)·S1` (`rlctAtOn_comp_localDiffeo`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    -- **Step 1: `rlctAt(dlnLoss) = rlctAtOn Φscore wstar`** (Params→flat MP transport + `rlctAtOn_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:        = rlctAtOn Φscore wstar := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      rw [← rlctAtOn_eq_rlctAt]
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      have htrans := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:      refine rlctAtOn_squeeze (fun x => dlnLoss H B ((paramsEquivFlat H).symm x)) Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    have hstep2 : rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:`nReg/2 + rlctAtOn (dlnLoss M 0) 0` — the CORE RLCT, NOT its closed form. The Skeleton's
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:gap is exactly the **R1 core-value** `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:R1 core-value `hcore : rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's lane) and the
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:    (hcore : rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`; it makes NO codim claim. When G-b's
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:- `IsSchurStraightenSqueeze` — the squeeze giving `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0`
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:- `ReducedTransport S Y` — the det-1 MP reindex closing `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:Composed: `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` — the per-node DESCENT STEP that
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:compacts `volume` — the squeeze's `rlctAtOn` measure hygiene; the `MeasureSpace` / `TopologicalSpace` / `Zero`
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:ONLY: `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` must NOT be iterated INTO a
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:degenerate leaf (`isLeafNode M ↔ ∃ s, M s = 0`, where `dlnLoss ≡ 0` so `rlctAtOn = ⊤` and
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:  /-- The det-1 MP descent transport (closes `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`); its `G` is
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:  /-- The #134 ONE-datum squeeze: `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0`, with `G` and
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0)`. Composes the banked
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:`schur_straighten_squeeze_of_data` (the `nReg/2 + rlctAtOn (G²) 0` split, with `G = transport.G`) with
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:`ReducedTransport.descent` (`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`). The two legs share the SAME
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:    rlctAtOn nd.flatCore (0, 0)
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:(`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`) and recurses on `S.red` (the
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:    rlctAtOn nd.flatCore (0, 0)
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:    rlctAtOn (fun q => ∑ (regAbsorb q).1² + deepestCoreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      = rlctAtOn (fun q => ∑ q.1²         + deepestCoreF (coreAbsorb q).2.1) 0.
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:`coreAbsorb.symm` (RLCT-invariant, `rlctAtOn_comp_homeomorph`), which collapses the core term to
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:The remaining genuinely-analytic atom — the decoupled peel `rlctAtOn (G ∘ regAbsorb) 0 = rlctAtOn G
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:bounded-unit Jacobian via `rlctAtOn_boundedUnit_localHomeomorph`, which needs the concrete `E` map).
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:    rlctAtOn (fun q => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      = rlctAtOn (fun q => regF q.1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:    rlctAtOn (fun q => regF (regAbsorb q).1 + coreF q.2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      = rlctAtOn (fun q => regF q.1 + coreF q.2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:theorem rlctAtOn_regAbsorb_reduce
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF q.2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:        = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:    rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:  have hL : rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      = rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF q.2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:  have hR : rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:`0` and the peel (`rlctAtOn_comp_localDiffeo`) applies. No core-block-zero needed (invertibility of a
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:theorem rlctAtOn_regAbsorb_reduce2
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      rlctAtOn (fun q : R × (C × S) => regF (E (coreAbsorb.symm q)) + coreF q.2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:        = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:    rlctAtOn (fun q : R × (C × S) => regF (E q) + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:  have hL : rlctAtOn (fun q : R × (C × S) => regF (E q) + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      = rlctAtOn (fun q : R × (C × S) => regF (E (coreAbsorb.symm q)) + coreF q.2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:  have hR : rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:The decoupled peel `rlctAtOn (fun q => regF (regStraighten q).1 + coreF q.2.1) 0 = rlctAtOn (fun q =>
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:theorem rlctAtOn_regStraighten_peel
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:    rlctAtOn (fun q : R × (C × S) => regF (regStraighten q).1 + coreF q.2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:  have hkey := rlctAtOn_boundedUnit_localHomeomorph
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:/-! ## The IFT → #72 adapter (`rlctAtOn_comp_localDiffeo`)
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:`rlctAtOn (F ∘ f) wstar = rlctAtOn F wstar`. The implicit-function-theorem
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:theorem rlctAtOn_comp_localDiffeo {M : Type*}
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:    rlctAtOn (fun w => F (f w)) wstar = rlctAtOn F wstar := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:  have hkey := rlctAtOn_boundedUnit_localHomeomorph F wstar f g
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:`rlctAtOn_regAbsorb_reduce`): two points with the same reg AND spec slots have the same reg output. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:`rlctAtOn_comp_localDiffeo` consumes (it needs the derivative as a `≃L`, not a bare `→L`). The
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:is the unitriangular invertible shear `[[I, Σ],[0, I]]` (det 1), which `rlctAtOn_comp_localDiffeo`
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:invertible `e` `rlctAtOn_comp_localDiffeo` consumes — decoupled from HOW `D_E`'s reg-block is `id`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:`rlctAtOn_regAbsorb_reduce` is then `q = q'` at both reg + carried slots, so trivially equal). -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:abstract `rlctAtOn_comp_localDiffeo` + `rlctAtOn_germ_local`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:assembly, every body `sorry`. Typechecks against the banked `rlctAtOn_comp_localDiffeo` interface.
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:Assembles via the banked abstract bridge `rlctAtOn_diffeo_bridge_of`: S6 comp-identity (germ) +
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:    rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:  exact rlctAtOn_diffeo_bridge_of Φscore Φcore wstar (psiL2 H r B hB hr hL J Pf Qf)
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:  `rlctAt H (dlnLoss H B) deepestPoint = nReg/2 + rlctAtOn(dlnLoss M 0) 0` (core RLCT, NOT `lambdaCore`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:- **`hRValue`** — R1's value `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)` (= `resolution_charts`
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:(`rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`), the local RLCT at the deepest point IS the
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:target. Proof: `deepest_regular_core_reduces` (value-free, `nReg/2 + rlctAtOn(core) 0`) ▸ `hRValue`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/RouteMNReg.lean:(`schur_node_loss_presentation`). The per-node RLCT splits `nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:/-- **Step Ψ_conj — the L=2 CONJUGATED diffeo bridge** (`rlctAtOn Φscore = rlctAtOn Φcore_conj`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:`rlctAtOn_diffeo_bridge_of` from S6 (`comp_identity_L2_conj`, germ) + S2 (`psiL2Conj_contDiff`) + S4
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:Step Θ (`rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb`) closes the atom-free `hstep2 = Θ ∘ Ψ_conj`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:    rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:  exact rlctAtOn_diffeo_bridge_of Φscore Φcore wstar
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMCover.lean:  `rlctAtOn_myF222_le`'s `≤`-leg, at-and-above the threshold).
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMCover.lean:`dlnLoss H222 0` RLCT statement requires transporting across `e222` (`rlctAtOn_dlnLoss222_transport`,
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMCover.lean:`[−ε, ε]^8` is `⊤`. This is the `(2,2,2)` `≤`-direction analytic content (`rlctAtOn_myF222_le`'s calc),
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMCover.lean:(unlike the `> 3/2` `rlctAtOn_myF222_le`), as `cover_ge_div`'s `monomialThreshold ≤ c'` premise needs. -/
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:`Q = ‖q‖²`. The network-free producer `rlctAtOn_quasiSplit_ge_of_contDiff_residual`
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:the bounded-unit chart TRANSFER `hchart : rlctAt (dlnLoss H B) v = rlctAtOn F (0,t0)` (the banked
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:`rlctAtOn_boundedUnit_localHomeomorph` applied to the actual `Params H → flat` IFT chart at `v` —
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:    `nReg/2 + rlctAtOn R t0 ≤ rlctAt (dlnLoss H B) v`, with `F`, `R` built from `q` (no bare
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:    two `C¹` residuals; only `hchart`/`hchart₂` (the two `rlctAtOn`-equality transfers), `hDeepest`
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:    (m : ℝ≥0∞)/2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v.
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:network-free `rlctAtOn_quasiSplit_ge_of_contDiff_residual`. (The regular-block count `m` is FREE in
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:        = rlctAtOn (fun p : (Fin m → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2))
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:    (m : ℝ≥0∞) / 2 + rlctAtOn (fun t : Y => ∑ i, q ((0 : Fin m → ℝ), t) i ^ 2) t0
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:  exact rlctAtOn_quasiSplit_ge_of_contDiff_residual q hq t0 hRne
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:`rlctAtOn`-equality transfers, `hDeepest`, and the R1 interface stay hypotheses.
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:        = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2))
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:    (hchart₂ : rlctAtOn (fun t : Y => ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:        = rlctAtOn (fun p : (Fin (extraCount m a b) → ℝ) × Y₂ =>
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:    (hDegraded : rlctAtOn (fun t : Y₂ => ∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), t) i ^ 2) t0₂
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:origin, `rlctAtOn(core)(0) = ⨅ monomialThreshold`. For the trivial network `M = (1,1,1)` the core IS
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:(`iInf_unique`), `rlctAtOn = rlctAt` on `Params`, to the proven bridge
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:      rlctAtOn (fun A : Params (![1, 1, 1] : Fin 3 → ℕ) =>
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:          rlctAtOn_eq_rlctAt, case111_rlct_eq_monomialThreshold, iInf_unique]⟩
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:(`schur_recursion_step_squeeze`, banked) and the det-1 MP reindex (`rlctAtOn_comp_homeomorph`, banked) are
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:`rlctAtOn_reduced_transport`). If the post-blow-up reduced core `G` pulls back the COLLAPSED chain loss
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:anchored at the deepest point, then `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss (redChain t M) 0) redZero`. The
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:(`rlctAtOn_comp_homeomorph`), so the same proof transports to the one-fewer-arity chain. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:theorem rlctAtOn_layerReduced_transport (t : ℕ) (M : Fin (L + 1 + 1 + 1) → ℕ)
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:    rlctAtOn (fun y => G y ^ 2) (0 : Y) = rlctAtOn (dlnLoss (redChain t M) 0) redZero := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:  rw [hpull, rlctAtOn_comp_homeomorph redEmbed hmp hemb (dlnLoss (redChain t M) 0) 0, hzero]
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:`routeM_rlctAtOn_eq_iInf` target value, delivered by the LAYER-COLLAPSING atlas: every leaf's single
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean:g161): the bounded-unit-Jacobian data that crux2's `rlctAtOn_boundedUnit_localHomeomorph` (#72)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean:/-- **The bounded-unit Jacobian datum** (the `hbdd` of crux2's `rlctAtOn_boundedUnit_localHomeomorph`,
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:  order — transporting `dlnLoss` to `blockG·blockH` via `rlctAtOn_comp_homeomorph`;
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:- `rlctAtOn_blockG_eq_one`: the `EuclideanSpace ℝ (Fin 2)` ↔ `Fin 2 → ℝ` bridge for
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:- `rlctAtOn_product_blocks`: the `product_min_rlct_of_ne` (#57) discharge (`block_ne_ae`).
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:`rlctAtOn` via `rlctAtOn_comp_homeomorph`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:(`measurePreserving_eME212`); transport via `rlctAtOn_comp_homeomorph` (`S1Fubini`), with
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:theorem rlctAtOn_case212_eq_product :
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:      = rlctAtOn (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => blockG p.1 * blockH p.2) (0, 0) := by
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:  have key := rlctAtOn_comp_homeomorph eHom212 hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:/-- **Each block has RLCT 1.** `rlctAtOn blockG 0 = 1` (and likewise `blockH`): `blockG = Σᵢ aᵢ²` on
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:theorem rlctAtOn_blockG_eq_one : rlctAtOn blockG (0 : Fin 2 → ℝ) = 1 := by
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:  have key := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:theorem rlctAtOn_blockH_eq_one : rlctAtOn blockH (0 : Fin 2 → ℝ) = 1 :=
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:  rlctAtOn_blockG_eq_one
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:/-- **product-MIN for the two blocks.** `rlctAtOn (G·H)(0,0) = min (rlctAtOn G 0)(rlctAtOn H 0)`
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:theorem rlctAtOn_product_blocks :
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:    rlctAtOn (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => blockG p.1 * blockH p.2) (0, 0)
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:      = min (rlctAtOn blockG 0) (rlctAtOn blockH 0) := by
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:closed form `aoyagiLambda (2,1,2) 0 = 1`. Assembled: loss = `G·H` (`rlctAtOn_case212_eq_product`) ⟹
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:`min` (`rlctAtOn_product_blocks`) of the block RLCTs (`= 1` each), `min(1,1) = 1 = aoyagiLambda`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:  rw [rlctAtOn_case212_eq_product, rlctAtOn_product_blocks,
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:    rlctAtOn_blockG_eq_one, rlctAtOn_blockH_eq_one, min_self]
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:abstract Route-M bridge `routeM_rlctAtOn_eq_iInf` (which consumes `F : (Fin N → ℝ) → ℝ`, `U`, `ι d k h`).
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:The KEYSTONE (`rlctAtOn_routeMCore_transport`): the bridge concludes about `rlctAtOn (routeMCore M) 0`;
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:this transports it to the genuine `rlctAtOn (dlnLoss M 0) (fun _ => 0)` at the deepest point, via the
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:measure-preserving homeomorphism `paramsEquivFlat M` (`rlctAtOn_comp_homeomorph`, S1Fubini) + the
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:`rlctAtOn_dlnLoss222_transport` (ParamsFlat222, the (2,2,2) seam).
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:family (gated). So this banks the headline plumbing the route to `routeM_rlctAtOn_eq_iInf` rests on.
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:deepest point: `rlctAtOn (routeMCore M) 0 = rlctAtOn (dlnLoss M 0) (fun _ => 0)`. Via
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:`rlctAtOn_comp_homeomorph` (the measure-preserving homeomorphism `paramsEquivFlat M`) + the
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:zero-preserving `paramsEquivFlat_deepest`. The general-M analog of `rlctAtOn_dlnLoss222_transport`; this is
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:what carries crux2's bridge conclusion `rlctAtOn (routeMCore M) 0 = ⨅ …` back to the headline's
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:`rlctAtOn (dlnLoss M 0) (deepest)`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:theorem rlctAtOn_routeMCore_transport (M : Fin (L + 1) → ℕ) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:    rlctAtOn (routeMCore M) (0 : Fin (routeMAmbient M) → ℝ)
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:      = rlctAtOn (dlnLoss M 0) (fun _ => 0 : Params M) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:  have key := rlctAtOn_comp_homeomorph (paramsEquivFlatHomeo M) hmp hemb (routeMCore M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:  -- `key : rlctAtOn (routeMCore M ∘ e) deepest = rlctAtOn (routeMCore M) (e deepest)`
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:the RLCT — the NON-MP companion to `rlctAtOn_comp_homeomorph` (which needs measure preservation,
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:    rlctAtOn (F ∘ π) (π⁻¹ wstar) = rlctAtOn F wstar.
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:companion of `rlctAtOn_unit_invariant_aux` (which strips a unit on the *function*): here the bounded
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:`rlctAtOn G ≤ rlctAtOn F` (a more-singular `F` has a larger threshold). The `weightedThreshold`
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:S1 primitive — used by `rlctAtOn_squeeze` here and the D1≥ two-point domination. -/
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:theorem rlctAtOn_mono (F G : M → ℝ) (wstar : M) (hFmeas : Measurable F)
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:    rlctAtOn G wstar ≤ rlctAtOn F wstar := by
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:with `0 < c₁, c₂`, then `rlctAtOn F wstar = rlctAtOn Φ wstar`. The positive constants `c₁, c₂` are units
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:stripped by `rlctAtOn_unit_invariant_aux`; the two inequalities give `rlctAtOn_mono` both ways (the
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:theorem rlctAtOn_squeeze (F Φ : M → ℝ) (wstar : M) (hFmeas : Measurable F) (hΦmeas : Measurable Φ)
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:    rlctAtOn F wstar = rlctAtOn Φ wstar := by
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:  · rw [show rlctAtOn Φ wstar = rlctAtOn (fun w => c₂ * Φ w) wstar from
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:      (rlctAtOn_unit_invariant_aux Φ (fun _ => c₂) wstar c₂ c₂ hc₂ (by fun_prop)
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:    refine rlctAtOn_mono (fun w => c₂ * Φ w) F wstar (by fun_prop) ⟨U, hU, fun w hw => ?_⟩
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:  · rw [show rlctAtOn Φ wstar = rlctAtOn (fun w => c₁ * Φ w) wstar from
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:      (rlctAtOn_unit_invariant_aux Φ (fun _ => c₁) wstar c₁ c₁ hc₁ (by fun_prop)
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:    refine rlctAtOn_mono F (fun w => c₁ * Φ w) wstar hFmeas ⟨U, hU, fun w hw => ?_⟩
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:`rlctAtOn_comp_homeomorph`, generalising `rlctAtOn_ray_scaling_invariant` off the scaling map). For a
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:    rlctAtOn (F ∘ π) wstar = rlctAtOn F wstar.
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:The `det ≠ ±1` is exactly the distinction from the measure-preserving `rlctAtOn_comp_homeomorph`. Two
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:neighbourhood (e.g. an IFT `OpenPartialHomeomorph`), use `rlctAtOn_boundedUnit_localHomeomorph`
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:theorem rlctAtOn_boundedUnit_homeomorph {M : Type*}
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:    rlctAtOn (fun w => F (π w)) wstar = rlctAtOn F wstar := by
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:  -- `rlctAtOn (F∘π) = wThr (F∘π) 1 = wThr (F∘π) |det| [hpeel.symm] = wThr F 1 [htrans.symm] = rlctAtOn F`.
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:  rw [rlctAtOn, rlctAtOn, ← hpeel, ← htrans]
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:`rlctAtOn_germ_local` (which lives downstream); inlined here to avoid the import cycle. -/
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:`rlctAtOn_boundedUnit_homeomorph`, for a diffeomorphism defined only NEAR the basepoint). `rlctAtOn` is
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:    rlctAtOn (F ∘ π) wstar = rlctAtOn F wstar.
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:theorem rlctAtOn_boundedUnit_localHomeomorph {M : Type*}
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:    rlctAtOn (fun w => F (π w)) wstar = rlctAtOn F wstar := by
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:  -- FORWARD: `rlctAtOn F = wThr F 1 ≤ wThr (F∘π) |det Dπ| = wThr (F∘π) 1 = rlctAtOn (F∘π)`.
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:  -- assemble: `rlctAtOn (F∘π) = wThr (F∘π) 1`, `rlctAtOn F = wThr F 1`; le_antisymm of hrev/hfwd.
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:  rw [rlctAtOn, rlctAtOn]
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:  shear is `det = 1`) ⟹ `rlctAtOn_comp_homeomorph` (NO Jacobian/weight bookkeeping; #61/g156 corrected
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:`rlctAtOn_comp_homeomorph`, det = 1 — NOT the abstract #71 bounded-unit peel) are wired directly. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:stays globally measurable for `rlctAtOn_squeeze`). The `regAbsorb_rlct` peel is discharged by
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:`rlctAtOn_regAbsorb_reduce` (the `coreAbsorb.symm` conjugation stripping `coreAbsorb` from the core
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:term) composed with `rlctAtOn_comp_localDiffeo` (the IFT → `#72` adapter): `E_pivot` need only be
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:      rlctAtOn (fun q : DeepestSplit H r nGauge =>
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:        = rlctAtOn (fun q : DeepestSplit H r nGauge =>
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:    have hkey := rlctAtOn_comp_localDiffeo
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:  exact rlctAtOn_regAbsorb_reduce2 coreAbsorb E_full
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:peels the RLCT via `rlctAtOn_comp_homeomorph` (NO derivative bookkeeping). The two MP helpers
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:(`measurePreserving_coreShear`) ⟹ `rlctAtOn_comp_homeomorph`. The concrete Schur shift is plugged in
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:  -- `coreAbsorb_rlct`: the shear is MP ⟹ `rlctAtOn_comp_homeomorph`, then `coreAbsorb 0 = 0`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:  have hkey := rlctAtOn_comp_homeomorph (coreShearHomeo shift hshift) hmp
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:Threaded into PIN 1's `regAbsorb_rlct` (`rlctAtOn_regAbsorb_reduce` needs `coreAbsorb` MP for the
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:`coreShear_satisfies_coreAbsorb` (`rlctAtOn_comp_homeomorph` on the det-1 shear). The concrete shift
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurSmooth.lean:GLOBALLY plus an invertible strict derivative. The consumer `rlctAtOn_comp_localDiffeo` demands GLOBAL
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:    rlctAtOn R 0 = extra/2 + lambdaCore(M'),   extra = m(a+b) − ab,  M' = (m−a, m−a−b, m−b),
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:and produces `coreDeepest ≤ rlctAtOn R t0`.
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:    extra/2 + rlctAtOn R₂ t0₂ ≤ rlctAtOn R t0,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:and the §5 R1-resolution-at-`M'` interface (`hDegraded`) supplies `rlctAtOn R₂ t0₂ =
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:and `coreDeepest = ofReal(lambdaCore (square m))`, this gives `coreDeepest ≤ rlctAtOn R t0` — the
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:data `a + b ≤ m`: given the second-peel chart transfer (`hchart₂ : rlctAtOn R t0 = rlctAtOn F₂
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:degraded-core value `hDegraded : rlctAtOn R₂ t0₂ = ofReal(lambdaCore M')` (the §5 interface
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:the D1 `hCore` holds: `coreDeepest ≤ rlctAtOn R t0`. The `extra` Morse squares peeled in the SECOND
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:    (hchart₂ : rlctAtOn R t0 = rlctAtOn F₂ ((0 : Fin (extraCount m a b) → ℝ), t0₂))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:    (hDegraded : rlctAtOn R₂ t0₂ = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:    coreDeepest ≤ rlctAtOn R t0 := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:  have hpeel : (extraCount m a b : ℝ≥0∞) / 2 + rlctAtOn R₂ t0₂
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:      ≤ rlctAtOn F₂ ((0 : Fin (extraCount m a b) → ℝ), t0₂) :=
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:    rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last 2))) ℝ) A)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:    rlctAtOn (fun A : Params (MprimeWidths m a b) =>
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin (nRegL2 H r) → ℝ), t0))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:    (hchart₂ : rlctAtOn R t0 = rlctAtOn F₂ ((0 : Fin (extraCount m a b) → ℝ), t0₂))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:    (hDegraded : rlctAtOn R₂ t0₂ = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:  -- discharge `hCore : coreDeepest ≤ rlctAtOn R t0` from the SECOND peel + the interface
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:  have hCore : coreDeepest ≤ rlctAtOn R t0 :=
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:RECURSION route to `rlctAtOn (dlnLoss M 0) 0 = ofReal (lambdaCore M)` (`= ½·minAdm`), iterating the
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:- `hstep` (O1, the NON-degenerate-child step): `rlctAtOn (dlnLoss M 0) 0 = ofReal (nReg M / 2) +
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:  rlctAtOn (dlnLoss (redOf M) 0) 0`. Sound only when the child `redOf M` is non-degenerate (the
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:  `dlnLoss (redOf M) ≡ 0`, geometric `rlctAtOn = ⊤`), DON'T recurse — `rlctAtOn (dlnLoss M 0) 0 =
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:state contributing `0`), the binding R1 core identity holds: `rlctAtOn (dlnLoss M 0) 0 = ofReal
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  RLCT splits as `nReg/2 + rlctAtOn(G²)`. (Transport `rlctAtOn_comp_homeomorph` + germ-rewrite
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  `rlctAtOn_germ_local` + unit-strip `rlctAtOn_unit_invariant_aux` + smooth-block `S1.5`.)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:- `rlctAtOn_germ_local` — general-domain `rlctAtOn` germ-locality (reusable bedrock).
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:SOUNDNESS NOTE (the (C2) finding): the *clean* `rlctAtOn(dlnLoss M 0) 0 = nReg/2 + rlctAtOn(Mred) 0`
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:/-! The general-domain `rlctAtOn` unit-invariance (the prereq) now lives in `Foundations/S1Local.lean`
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:as `rlctAtOn_unit_invariant_aux` (beside `rlct_unit_invariant_aux`), reachable transitively via the
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:The clean `rlctAtOn(dlnLoss M 0) 0 = nReg/2 + rlctAtOn(dlnLoss Mred 0) 0` (no chart hypothesis) is
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:RLCT splits as `nReg/2 + rlctAtOn(G²)`. The unit `u` is stripped by `rlctAtOn_unit_invariant_aux`; the
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:smooth block by `rlct_additive_smooth_block` (S1.5); the chart transport by `rlctAtOn_comp_homeomorph`
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:/-- **`rlctAtOn` germ-locality (general domain).** The RLCT threshold depends only on the germ of the
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:integrand at the base point: `F =ᶠ[𝓝 w0] G ⟹ rlctAtOn F w0 = rlctAtOn G w0`. The general-domain twin
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:home is `S1Local.lean` beside `rlctAtOn_unit_invariant_aux`.) -/
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:theorem rlctAtOn_germ_local {N : Type*} [MeasureSpace N] [TopologicalSpace N]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:    rlctAtOn F w0 = rlctAtOn G w0 := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:identity misread as a loss-VALUE identity. So the per-node `rlctAtOn` does NOT resolve by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:`rlctAtOn_comp_homeomorph` (a change of variables); it resolves by the SQUEEZE (same as L2/g128): the
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:`|G| ≤ |F|` and `G` vanishes only where `F` does, then `rlctAtOn G wstar ≤ rlctAtOn F wstar` — a
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:theorem rlctAtOn_mono {M : Type*} [MeasureSpace M] [TopologicalSpace M] [OpensMeasurableSpace M]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:    rlctAtOn G wstar ≤ rlctAtOn F wstar := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:and `c₁·Φ ≤ F ≤ c₂·Φ` with `0 < c₁`, `0 < c₂`, then `rlctAtOn F wstar = rlctAtOn Φ wstar`. The
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:constant multiples `c₁, c₂` are positive units stripped by `rlctAtOn_unit_invariant_aux`; the two
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:inequalities give `rlctAtOn_mono` both ways (the `F=0 ⟺ Φ=0` vanishing from the two-sided bound with
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:theorem rlctAtOn_squeeze {M : Type*} [MeasureSpace M] [TopologicalSpace M] [OpensMeasurableSpace M]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:    rlctAtOn F wstar = rlctAtOn Φ wstar := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  · rw [show rlctAtOn Φ wstar = rlctAtOn (fun w => c₂ * Φ w) wstar from
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:      (rlctAtOn_unit_invariant_aux Φ (fun _ => c₂) wstar c₂ c₂ hc₂ (by fun_prop)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:    refine rlctAtOn_mono (fun w => c₂ * Φ w) F wstar (by fun_prop) ⟨U, hU, fun w hw => ?_⟩
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  · rw [show rlctAtOn Φ wstar = rlctAtOn (fun w => c₁ * Φ w) wstar from
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:      (rlctAtOn_unit_invariant_aux Φ (fun _ => c₁) wstar c₁ c₁ hc₁ (by fun_prop)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:    refine rlctAtOn_mono F (fun w => c₁ * Φ w) wstar hFmeas ⟨U, hU, fun w hw => ?_⟩
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:`rlctAtOn (dlnLoss M 0) (χ 0) = nReg/2 + rlctAtOn (G²) 0`. Transport (`rlctAtOn_comp_homeomorph`,
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:needs `χ` measure-preserving) → germ-rewrite (`rlctAtOn_germ_local`) → unit-strip
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:(`rlctAtOn_unit_invariant_aux`) → smooth-block split (`rlct_additive_smooth_block`, S1.5). The det-1
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:    rlctAtOn (dlnLoss M 0) (chart (0, 0))
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  rw [← rlctAtOn_comp_homeomorph chart hmp hemb (dlnLoss M 0) (0, 0)]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  rw [rlctAtOn_germ_local _ (fun p => u p * smoothBlockSplitForm G p) _ hfactor]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  rw [rlctAtOn_unit_invariant_aux (smoothBlockSplitForm G) u (0, 0) a b ha humeas hu]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0`. Chain: `rlctAtOn_squeeze` (the two-sided
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:`rlctAtOn_mono` + positive-unit strip — NO chart, NO measure Jacobian) → `rlct_additive_smooth_block`
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:    rlctAtOn flatCore ((0, 0) : (Fin nReg → ℝ) × Y)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  rw [rlctAtOn_squeeze flatCore (smoothBlockSplitForm G) _ hFmeas hΦmeas c₁ c₂ hc₁ hc₂ hsq]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  the deepest point. No chart map; the anchor is the basepoint of `rlctAtOn … (0,0)`.
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  `rlctAtOn_unit_invariant_aux`'s `a > 0` needs. NOT an abstract `Measurable u` (which could vanish).
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0` — the regular smooth block plus the reduced-chain
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:(the g128/L2 chain: `rlctAtOn_squeeze` + `rlct_additive_smooth_block`). The recursion step the structural
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:    rlctAtOn flatCore ((0, 0) : (Fin nReg → ℝ) × Y)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) :=
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) …`. This supplies the transport: if `redEmbed` is a
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) redZero` (`rlctAtOn_comp_homeomorph`). The basepoint
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:theorem rlctAtOn_reduced_transport {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:    rlctAtOn (fun y => G y ^ 2) (0 : Y) = rlctAtOn (dlnLoss S.red 0) redZero := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:  rw [hpull, rlctAtOn_comp_homeomorph redEmbed hmp hemb (dlnLoss S.red 0) 0, hzero]

exec
/bin/bash -lc "sed -n '1,200p' lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean" in /tmp/p44-scope
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Foundations.S1QuasiSplit
import DLNFibre.DLN.RLCT.Foundations.S1Spectator
import DLNFibre.DLN.RLCT.Validate.DeepestMinRlct

/-!
# `DLNFibre.DLN.RLCT.Validate.D1ChartProducer` — the D1 (★) chart-producer skeleton (L = 2)

Use-site for the banked quasi-splitting engine `rlct_quasiSplit_ge` (`Foundations.S1QuasiSplit`).
Goal: the D1 obligation (★)

    nReg/2 + rlctAtOn(core)(deepest-core) ≤ rlctAt (dlnLoss H B) v   (at a general optimal `v`)

which feeds the banked `deepest_le_of_optimal_via_L2_ge` (`DeepestMinRlct`) ⟹
`rlctAt_deepest_le_of_optimal` ⟹ D1 (rung 2/5). The loss `dlnLoss H B A = ∑ᵢⱼ ((prod A−B)ᵢⱼ)²` is
a sum of squares of the smooth entries `g_{ij}(A) = (prod A − B)_{ij}` — exactly the
`f = ∑ g_k²` shape the engine targets, `m = nReg = r(H⁰+Hᴸ−r)` the count of independent gradients.

## What this banks (PART (a)) and what it surfaces (PART (b))

**PART (a) — `rlctAt_ge_nReg_add_slice` (the (★)-as-`hAtV` reduction, BANKED).** Given the IFT-chart
producer's outputs as hypotheses (the chart transfer `rlctAt (dlnLoss H B) v = rlctAtOn F (0,t0)`,
banked `rlctAtOn_boundedUnit_localHomeomorph` discharges it; the post-chart sum-of-squares form
`F = ∑s² + Q`, `Q ≥ 0`; the slice residual `R = Q(0,·)`, measurable a.e.-nonzero; the constant
comparison `∑s² + R ≤ C·F` near `(0,t0)`), the engine gives `nReg/2 + rlctAtOn R t0 ≤
rlctAt (dlnLoss H B) v` — the `hAtV` shape `deepest_le_of_optimal_via_L2_ge` consumes, with
`coreV := rlctAtOn R t0`. Mechanical: reuses the banked engine + the chart-transfer equality.

**PART (b) — the residual-core comparison (VERIFY-FIRST, decorrelated pen-and-paper, 2026-06-29).**
Setting `coreV := rlctAtOn R t0` (NOT a separate `v−core` map) makes `hAtV` the engine output; the
SOLE remaining obligation is `hCore : coreDeepest ≤ rlctAtOn R t0`, i.e. `rlctAtOn R 0 ≥
rlctAtOn (core) 0`.

**DEEPEST-TYPE points (`nReg_v = nReg`).** G1 verify-first (exact algebra, L=2, r∈{1,2,3}) found
`R = ‖T₁·(I_{M₁}+G)·T₂‖²_F` (`G` gauge-only, `G(0)=0`, min-degree 2), so `R = (core∘fst)∘Φ` for the
LOCAL DIFFEO `Φ : (T,g) ↦ ((T₁,(I+G(g))·T₂),g)` fixing the origin (`det DΦ(0)=(det(I+G(0)))^{M₂}=1`,
bounded-unit). The r≥2 coupling `Z₁·Y₂` is ABSORBED into the invertible inner factor `I+G`. `hCore`
is discharged WITH EQUALITY by `hCore_slice_residual_eq` below, routing through the SAME banked
machinery #44 uses — DECOUPLED from R1.

**MIDDLE-STRATUM points (`nReg_v > nReg`), the KILL-CONDITION (adjudication a97332/a591012b).** At a
genuinely-NON-trivial-core middle-stratum `v` — `(3,3,3)/r=1`, `A₁=diag(1,1,0)`, `A₂=diag(1,0,0)`,
`nReg_v=7 > nReg=5`, deg-4 core `dlnLoss(2,2,2)0` NONTRIVIAL — peeling exactly the CONSTANT `nReg=5`
(NOT the maximal `nReg_v=7`; peeling `nReg_v` = the FORBIDDEN Aoyagi-Thm-2 maximal Morse split)
leaves `R` with a degree-2 Morse part (`det DΦ(0) ≠ 1`, a DIFFERENT germ) — so the `_eq` form's
factorization is FALSE here. BUT the D1 INEQUALITY STILL HOLDS: `rlctAtOn R 0 = coreDeepest = 3/2`
EXACT (the `extra = nReg_v−nReg` Morse halves exactly offset the degraded core), via a
Morse-WITH-PARAMETERS VALUE argument (RLCT-additivity over disjoint groups). So the route is
NOT killed — the VALUE `hCore` survives — but its general-`v` discharge is VALUE-level, NOT
the germ factorization. This is the residual gap surfaced to the controller (the general-`v`
`hCore` obligation; the `_eq` factorization is the deepest-sub-locus special case).

Scope L = 2 (general-L = wall #120). This file BANKS the PART (a) reduction + the
PART (b) `hCore`-interface (factorization form, deepest-type); the remaining D1 obligations are the
IFT-chart producer (obligation (i)) + its general-`v` value-level `hCore` (the kill residual);
#44 is the already-tracked Skeleton sorry the deepest side `hDeepest` consumes. -/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **PART (a): the (★)-as-`hAtV` reduction** (mechanical; the chart producer's wiring). Given the
IFT-chart producer's outputs at a general optimal `v`, packaged on the flat product space
`(Fin m → ℝ) × Y` (the `Params H`-flattening the producer supplies), the engine `rlct_quasiSplit_ge`
delivers `(★)`'s `hAtV` side: `nReg/2 + rlctAtOn R t0 ≤ rlctAt (dlnLoss H B) v`, with
`coreV := rlctAtOn R t0`. The hypotheses are EXACTLY the producer obligations:

  * `hchart` — the chart transfer (banked `rlctAtOn_boundedUnit_localHomeomorph` at the producer;
    IFT chart `Φ` fixing the flat origin, bounded-unit Jacobian);
  * `hF` — the post-chart sum-of-squares form (the `g_{ij}`-built chart; the `nReg` active functions
    become the coordinates `sᵢ`);
  * `hR`/`hRne` — the slice residual `R = Q(0,·)`, measurable, a.e.-nonzero near `t0`;
  * `hcmp` — the constant comparison (`C¹` Lipschitz quasi-split, `coupled_controls_slice` summed
    over the inactive index).

After this, the remaining D1 obligation is `hCore : coreDeepest ≤ rlctAtOn R t0` (PART (b)). -/
theorem rlctAt_ge_nReg_add_slice {L m : ℕ} {Y : Type*}
    [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y]
    (H : Fin (L + 1) → ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H)
    (F : (Fin m → ℝ) × Y → ℝ) (Q : (Fin m → ℝ) × Y → ℝ) (R : Y → ℝ) (t0 : Y)
    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), t0))
    (hF : ∀ p, F p = (∑ i, p.1 i ^ 2) + Q p)
    (hQ0 : ∀ p, 0 ≤ Q p) (hFmeas : Measurable F)
    (hR : ∀ t, R t = Q (0, t)) (hRmeas : Measurable R)
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U), R z ≠ 0)
    (C : ℝ) (hC : 0 < C)
    (hcmp : ∃ U ∈ 𝓝 ((0 : Fin m → ℝ), t0), ∀ p ∈ U,
        (∑ i, p.1 i ^ 2) + R p.2 ≤ C * F p) :
    (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v := by
  rw [hchart]
  exact rlct_quasiSplit_ge F Q R t0 hF hQ0 hFmeas hR hRmeas hRne C hC hcmp

/-- **PART (a) → D1 per-point `≥`** (the (★) close MODULO the two producer obligations). Wiring
`rlctAt_ge_nReg_add_slice` (the `hAtV` side) through banked `deepest_le_of_optimal_via_L2_ge`: with
the deepest-side equality `hDeepest` (banked via `deepest_regular_core_normal_form`, #44) and the
leading-form comparison `hCore : coreDeepest ≤ rlctAtOn R t0` (PART (b)), the deepest point has
`≤` local RLCT than `v`: `rlctAt (dlnLoss H B) deepest ≤ rlctAt (dlnLoss H B) v`. This is the
`rlctAt_deepest_le_of_optimal` per-point conclusion, reduced to EXACTLY: (i) the IFT-chart producer,
(ii) `hDeepest` (= #44), (iii) `hCore` (the leading-form comparison). The `nReg/2` shift cancels. -/
theorem deepest_le_of_optimal_chart {L m : ℕ} {Y : Type*}
    [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y]
    (H : Fin (L + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (deepest v : Params H)
    (F : (Fin m → ℝ) × Y → ℝ) (Q : (Fin m → ℝ) × Y → ℝ) (R : Y → ℝ) (t0 : Y)
    (coreDeepest : ℝ≥0∞)
    (hDeepest : rlctAt H (dlnLoss H B) deepest = (m : ℝ≥0∞) / 2 + coreDeepest)
    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), t0))
    (hF : ∀ p, F p = (∑ i, p.1 i ^ 2) + Q p)
    (hQ0 : ∀ p, 0 ≤ Q p) (hFmeas : Measurable F)
    (hR : ∀ t, R t = Q (0, t)) (hRmeas : Measurable R)
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U), R z ≠ 0)
    (C : ℝ) (hC : 0 < C)
    (hcmp : ∃ U ∈ 𝓝 ((0 : Fin m → ℝ), t0), ∀ p ∈ U,
        (∑ i, p.1 i ^ 2) + R p.2 ≤ C * F p)
    (hCore : coreDeepest ≤ rlctAtOn R t0) :
    rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
  have hAtV : (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v :=
    rlctAt_ge_nReg_add_slice H B v F Q R t0 hchart hF hQ0 hFmeas hR hRmeas hRne C hC hcmp
  exact deepest_le_of_optimal_via_L2_ge (B := B) H r (rlctAt H (dlnLoss H B) deepest)
    (rlctAt H (dlnLoss H B) v) m coreDeepest (rlctAtOn R t0) hDeepest hAtV hCore

/-! ## PART (b) interface — the slice-residual ↦ core RLCT identification (`hCore` discharge)

The G1 verify-first (decorrelated pen-and-paper, EXACT algebra, L=2, r∈{1,2,3}, reduced widths
M∈{(1,1,1),(2,2,2),(1,2,1),(2,1,2),(3,3,3)} + Codex xhigh) found the slice residual to be EXACTLY

    R = ‖ T₁·(I_{M₁} + G)·T₂ ‖²_F,   G = gauge-only, G(0) = 0, min-degree 2,

so `R = (core ∘ fst) ∘ Φ` for the LOCAL DIFFEO `Φ : (T, g) ↦ ((T₁, (I+G(g))·T₂), g)` fixing the
origin (block-triangular Jacobian, `det DΦ(0) = (det(I+G(0)))^{M₂} = 1` ⟹ bounded-unit), with `core`
loss `dlnLoss M 0` (a function of `T` alone, NOT the gauge `g`). The same-weight transverse coupling
`Z₁·Y₂` flagged at r≥2 is ABSORBED into the invertible inner factor `I+G` — NOT an additive
germ-changing perturbation — so the identification is `r`-independent and TIGHT (`rlctAtOn R 0 =
coreDeepest`, equality). The bound is NOT the R1-resolution-coupled leading-form lemma first feared;
it is this local-diffeo + spectator reduction, routing through the SAME banked machinery #44 uses.

The interface below banks `hCore` CONDITIONAL on the producer's diffeo data (the EXACT shape the
producer at obligation (i) supplies). It decouples `hCore` from the R1 / interior-det timeline. -/

/-- **`hCore` via the slice-residual diffeo** (the PART (b) interface, conditional clean-three). The
slice residual `R` on `Reduced × Gauge` equals the reduced core `core₀` (a function of
the `Reduced` factor alone) pulled back along a bounded-unit local diffeo `Φ` fixing the basepoint
`(t0, g0)`, i.e. `R = (core₀ ∘ fst) ∘ Φ` (`hRform`). Then `rlctAtOn R (t0,g0) = rlctAtOn core₀ t0`:
the diffeo transfer (`rlctAtOn_boundedUnit_localHomeomorph`) strips `Φ`, the spectator peel
(`rlctAtOn_spectator_peel`) drops the gauge factor. In particular `coreDeepest = rlctAtOn core₀ t0`
discharges the D1 `hCore : coreDeepest ≤ rlctAtOn R (t0,g0)` with EQUALITY (the G1 tightness).

The hypotheses are EXACTLY the producer's outputs: the diffeo `Φ`/`Φsymm`/derivatives + bounded-unit
Jacobian on an open `V ∋ (t0,g0)` (the raw-data `rlctAtOn_boundedUnit_localHomeomorph` form —
the `Φ` of G1), the form identity `hRform`, and a positive-finite gauge
nbhd `hG` (the spectator box). `core₀` is the reduced loss `dlnLoss M 0` at the producer.

**SCOPE LIMIT (kill-condition adjudication a97332/a591012b, 2026-06-29 — do not over-read).**
The germ-factorization `hRform` (`R = (core₀∘fst)∘Φ`, `Φ` bounded-unit, `det DΦ(0) =
1`) is dischargeable by the producer ONLY at DEEPEST-TYPE optimal points (where the extra Morse rank
`nReg_v − nReg = 0`, so `R` IS the deepest core up to the inner factor — the G1 finding). At a
MIDDLE-STRATUM optimal `v` (`nReg_v > nReg`, e.g. `(3,3,3)/r=1`, `A₁=diag(1,1,0)`, `A₂=diag(1,0,0)`,
`nReg_v=7 > nReg=5`), the EXACT slice residual after the constant-`nReg` peel has a degree-2 Morse
part (`det DΦ(0) ≠ 1`, a genuinely DIFFERENT germ) — so `hRform` is FALSE there and this does NOT
fire. `hCore : coreDeepest ≤ rlctAtOn R t0` STILL HOLDS at such `v` (verified EXACT:
`rlctAtOn R 0 = coreDeepest = 3/2` at that point — the `extra = nReg_v − nReg` Morse halves exactly
offset the degraded core), via a Morse-WITH-PARAMETERS VALUE argument, NOT this factorization. So at
GENERAL `v`, `hCore` is discharged at the VALUE level (`rlctAtOn R 0 ≥ coreDeepest`), an open
producer obligation NOT reducible to `hRform` — surfaced to the controller (the kill residual
gap). THIS lemma remains the lightest discharge on the DEEPEST sub-locus (where `nReg_v = nReg`). -/
theorem hCore_slice_residual_eq
    {Reduced Gauge : Type*}
    [NormedAddCommGroup Reduced] [NormedSpace ℝ Reduced] [MeasureSpace Reduced]
    [BorelSpace Reduced] [FiniteDimensional ℝ Reduced]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge] [MeasureSpace Gauge]
    [BorelSpace Gauge] [FiniteDimensional ℝ Gauge]
    [(volume : Measure (Reduced × Gauge)).IsAddHaarMeasure]
    [SFinite (volume : Measure Reduced)] [SFinite (volume : Measure Gauge)]
    [Measure.IsOpenPosMeasure (volume : Measure Gauge)]
    (core₀ : Reduced → ℝ) (R : Reduced × Gauge → ℝ) (t0 : Reduced) (g0 : Gauge)
    (Φ Φsymm : Reduced × Gauge → Reduced × Gauge)
    (DΦ DΦsymm : Reduced × Gauge → ((Reduced × Gauge) →L[ℝ] (Reduced × Gauge)))
    (V : Set (Reduced × Gauge))
    (hVopen : IsOpen V) (hwV : (t0, g0) ∈ V)
    (hfix : Φ (t0, g0) = (t0, g0))
    (hleft : ∀ w ∈ V, Φsymm (Φ w) = w) (hright : ∀ w ∈ V, Φ (Φsymm w) = w)
    (hΦcont : ContinuousOn Φ V) (hsymmcont : ContinuousOn Φsymm V)
    (hderiv : ∀ w ∈ V, HasFDerivAt Φ (DΦ w) w)
    (hderivsymm : ∀ w ∈ V, HasFDerivAt Φsymm (DΦsymm w) w)
    (hdetmeas : Measurable fun w => |(DΦ w).det|)
    (hdetmeassymm : Measurable fun w => |(DΦsymm w).det|)
    (hbdd : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΦ w).det| ∧ |(DΦ w).det| ≤ b)
    (hbddsymm : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΦsymm w).det| ∧ |(DΦsymm w).det| ≤ b)
    (hRform : ∀ w, R w = core₀ (Φ w).1)
    (hG : ∃ W : Set Gauge, IsOpen W ∧ g0 ∈ W ∧ volume W < ⊤) :
    rlctAtOn R (t0, g0) = rlctAtOn core₀ t0 := by
  -- `R = (core₀ ∘ fst) ∘ Φ`; strip `Φ` (bounded-unit local diffeo), then peel the gauge spectator.
  have hRfun : R = fun w => (fun p : Reduced × Gauge => core₀ p.1) (Φ w) := by
    funext w; rw [hRform]
  rw [hRfun]
  rw [rlctAtOn_boundedUnit_localHomeomorph (fun p : Reduced × Gauge => core₀ p.1) (t0, g0)
      Φ Φsymm DΦ DΦsymm V hVopen hwV hfix hleft hright hΦcont hsymmcont hderiv hderivsymm
      hdetmeas hdetmeassymm hbdd hbddsymm]
  exact rlctAtOn_spectator_peel core₀ t0 g0 hG

exec
/bin/bash -lc 'rg "lambdaCore" -n lean/DLNFibre/DLN' in /tmp/p44-scope
 succeeded in 0ms:
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:84:noncomputable def lambdaCore (d : Fin (N + 1) → ℕ) (r : ℕ) : ℚ :=
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:97:  lambdaShift d r + lambdaCore d r
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:227:theorem two_lambdaCore_eq_cValue
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:229:    2 * lambdaCore d r = (cValue (shiftedSorted d r) : ℚ) := by
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:329:  -- Reduce `2·lambdaCore = cValue` by clearing the `4ℓ` denominator (cancel `4ℓ ≠ 0`).
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:332:  -- `4ℓ·(2·lambdaCore) = 2·residueA(ℓ−residueA) − 2(ℓ−1)S² + 4ℓ·activePairSum` (cleared).
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:335:  have hlhs : 4 * (ℓ : ℚ) * (2 * lambdaCore d r)
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:339:    rw [lambdaCore, hellQ, hactiveSumQ]; field_simp
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:360:  rw [lambda, mul_add, two_lambdaCore_eq_cValue d r hN, codimFormula]
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:551:active-set size minus one). Specialising at `ℓ = qipM M` recovers the LR `lambdaCore`; at
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:579:/-- **`lambdaCore` is `coreFormula` at the LR cutoff** `ℓ = qipM`. The LR `activeSum`/`residueA`/
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:581:theorem lambdaCore_eq_coreFormula (d : Fin (N + 1) → ℕ) (r : ℕ) :
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:582:    lambdaCore d r = coreFormula (shiftedSorted d r) (qipM (shiftedSorted d r)) := by
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:785:/-! ## Assembling `paperLambdaCore = lambdaCore` (the core equality) -/
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:842:`paperLambdaCore d r = lambdaCore d r`. Cases on the corner `shiftedSorted d r 0`: when `≥ 1`, both
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:845:theorem paperLambdaCore_eq_lambdaCore (d : Fin (N + 1) → ℕ) (r : ℕ) :
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:846:    paperLambdaCore d r = lambdaCore d r := by
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:849:  rw [paperLambdaCore, lambdaCore_eq_coreFormula, ← hM]
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:872:    -- `lambdaCore` (`= coreFormula M (qipM M) = cValue/2`) is `0`.
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:875:        rw [← lambdaCore_eq_coreFormula]
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:877:        · exact two_lambdaCore_eq_cValue d r hN1
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:887:ℓ-independent and shared; the cores agree by `paperLambdaCore_eq_lambdaCore`.) -/
lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean:889:  rw [paperLambda, lambda, paperLambdaCore_eq_lambdaCore]
lean/DLNFibre/DLN/RLCT/AxCheck.lean:170:-- [propext, Classical.choice, Quot.sound], no `sorryAx`: `extra_half_add_lambdaCore_Mprime_ge_square` is
lean/DLNFibre/DLN/RLCT/AxCheck.lean:171:-- the UNCONDITIONAL §6 arithmetic (lambdaCore(square m) ≤ extra/2 + lambdaCore(M')); `hCore_middle_stratum_
lean/DLNFibre/DLN/RLCT/AxCheck.lean:175:#print axioms extra_half_add_lambdaCore_Mprime_ge_square
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1085:(`nReg = r(H⁰+Hᴸ−r)`, `ℝ≥0∞`) plus the singular core `ofReal(lambdaCore M)` (`M = H−r`) recombines to
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1087:`lambdaCore M ≥ 0` (so `ofReal` splits additively) and `r ≤ H s` for the `nReg` natural-subtraction. -/
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1091:        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1097:  have hsplit : (aoyagiLambda H r : ℝ) = (nReg : ℝ) / 2 + (lambdaCore M : ℝ) := by
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1102:  have hcore_nn : (0 : ℝ) ≤ (lambdaCore M : ℝ) := by
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1103:    rw [show (0 : ℝ) = ((0 : ℚ) : ℝ) by norm_num, Rat.cast_le]; unfold lambdaCore
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1117:core `lambdaCore` on the reduced widths `M = H−r`. The split is the rank-`r` gauge-slice change of
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1130:        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1134:as the regular-part shift `[−r²+r(H¹+Hᴸ⁺¹)]/2` plus the singular-core `lambdaCore` over the reduced
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1165:`⨅ monomialThreshold = lambdaCore`. It closes PARALLEL to R1, gated NOT on the value but on two
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1207:the match is purely the VALUE. That value `⨅ monomialThreshold = ofReal(lambdaCore M)` is **A1's**
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1208:job (S2 `monomial_rlct` + `lambdaCore_eq_clean`), kept separate from this chart fact.
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1225:non-strict, Lehalleur–Rimányi) to exclude the `prod ≡ 0` degeneracy the combinatorial `lambdaCore` cannot
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1518:/-! ### A1 (`lambdaCore_eq_clean`) route notes (the theorem itself is built at the end of the file).
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1521:`lambdaCore M = ½·min_T M(T)` equals `cleanCore c (sortedSmallest M c)` for an **achiever**
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1530:`Φ c = 2·cleanCore c (a₀,…,a_c)` (so `lambdaCore M = ½·minMval`, and the target is
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1533:`i·aᵢ ≤ Sᵢ + i − 1` (`c = 1` is always good, so `c*` exists; verified `lambdaCore = cleanCore c*`
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1564:`lambdaCore M = lambdaCore (sort M)`) with `Mval M T* = ½(∑Y² − ∑M²)`, then `Finset.inf'_le`. All
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1734:/-! ## A1 (`lambdaCore_eq_clean`) — the genuine clean closed form, built here.
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1736:The route is in the `lambdaCore_eq_clean` docstring above. The hard core is a from-scratch Karamata
lean/DLNFibre/DLN/RLCT/Skeleton.lean:3051:/-! ## A1 closing machinery (Route B: Rado–Gale achiever) + `lambdaCore_eq_clean`
lean/DLNFibre/DLN/RLCT/Skeleton.lean:3053:**A1 (Lemma 3): `lambdaCore M = cleanCore` at the achiever `c`.** Statement frozen (rv-2). The
lean/DLNFibre/DLN/RLCT/Skeleton.lean:3067:- LOWER `lambdaCore ≥ cleanCore`: feed the per-`k` edge bound (`smallestK_edge_le_width` for `k>c`;
lean/DLNFibre/DLN/RLCT/Skeleton.lean:3069:- UPPER `lambdaCore ≤ cleanCore`: telescope `T*` for a corridor-feasible ordering `q*` of `Y` — then
lean/DLNFibre/DLN/RLCT/Skeleton.lean:3147:    ∃ (c : ℕ) (hc : c ≤ L), 1 ≤ c ∧ lambdaCore M = cleanCore c (sortedSmallest M c hc) := by
lean/DLNFibre/DLN/RLCT/Skeleton.lean:3165:  -- lambdaCore = ½·I ; cleanCore = ¼·D ; with 2I = D ⟹ equal
lean/DLNFibre/DLN/RLCT/Skeleton.lean:3166:  have hlam : lambdaCore M = (1 / 2 : ℚ) * (I : ℤ) := by rw [lambdaCore, hI]
lean/DLNFibre/DLN/RLCT/Skeleton.lean:4241:/-- **A1 (Lemma 3, the headline arithmetic).** `lambdaCore M = cleanCore` at the achiever `cAch M`
lean/DLNFibre/DLN/RLCT/Skeleton.lean:4246:theorem lambdaCore_eq_clean (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
lean/DLNFibre/DLN/RLCT/Skeleton.lean:4247:    ∃ (c : ℕ) (hc : c ≤ L), 1 ≤ c ∧ lambdaCore M = cleanCore c (sortedSmallest M c hc) := by
lean/DLNFibre/DLN/RLCT/Foundations/Lambda.lean:10:The candidate value `Mval`, the admissible cone `Adm`, the core `lambdaCore = ½·min_T M(T)`,
lean/DLNFibre/DLN/RLCT/Foundations/Lambda.lean:80:def lambdaCore (M : Fin (L + 1) → ℕ) : ℚ :=
lean/DLNFibre/DLN/RLCT/Foundations/Lambda.lean:87:  (-(r : ℚ) ^ 2 + r * (H 0 + H (Fin.last L))) / 2 + lambdaCore (fun s => H s - r)
lean/DLNFibre/DLN/RLCT/Validate/Case323RouteStep.lean:43:/-- `minAdm(M323) = 5` (so `lambdaCore(3,2,3) = 5/2`). -/
lean/DLNFibre/DLN/RLCT/Validate/Case323RouteStep.lean:66:is `½·minAdm = 5/2 = lambdaCore(3,2,3)`. The asymmetric SECOND anchor corroborating `case222_routeStep_value`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:13:Cover #21 (`resolution_value_of_atlas`) then closes `⨅ = ofReal(lambdaCore M)`. Core-only.
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:77:give `∫⁻_U < ⊤` (`rlctAtOn_ge_of_integral_lt`). Mechanism-independent. `⨅ = ofReal(lambdaCore M)` is
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:11:`redOf := schurStateRed`, `nRegOf := bindNReg`, `lamOf := lambdaCore`,
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:15:`bindNReg M := 2·(lambdaCore M − lambdaCore (schurStateRed M))` makes `harith_step` an UNCONDITIONAL `ring`
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:16:identity. The monotonicity `lambdaCore (schurStateRed M) ≤ lambdaCore M` survives only in `hnReg`
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:19:`(minAdm M − minAdm (schurStateRed M) : ℚ)` (`2·lambdaCore = (Adm).inf'`, the ℤ minimal codim).
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:27:/-- The per-node regular count as a ℚ-difference of `lambdaCore`s: `2·(λ M − λ (schurStateRed M))`. Equals
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:30:  2 * (lambdaCore M - lambdaCore (schurStateRed M))
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:32:/-- **`harith_step` — the telescope step (UNCONDITIONAL in ℚ).** `lambdaCore M = bindNReg M / 2 +
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:33:lambdaCore (schurStateRed M)`. Pure ring identity. No monotonicity needed (the ℚ relief). -/
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:35:    lambdaCore M = bindNReg M / 2 + lambdaCore (schurStateRed M) := by
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:38:/-- A leaf node has `lambdaCore = 0`: `isLeafNode` gives `inf' Mval ≤ 0` (via `Int.toNat_eq_zero`), and
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:39:`inf' ≥ 0` (admissible `Mval ≥ 0`), so `inf' = 0` and `lambdaCore = ½·0 = 0`. -/
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:40:theorem lambdaCore_eq_zero_of_isLeafNode (M : Fin (L + 1) → ℕ) (hleaf : isLeafNode M) :
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:41:    lambdaCore M = 0 := by
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:47:  unfold lambdaCore; rw [h0]; ring
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:50:`lambdaCore (schurStateRed M) = 0`, so `lambdaCore M = bindNReg M / 2`. The `#70`-base level (one above the
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:53:    lambdaCore M = bindNReg M / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:54:  rw [bind_harith_step M, lambdaCore_eq_zero_of_isLeafNode _ hleaf, add_zero]
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:63:/-- **`hlam` — `lambdaCore ≥ 0`.** `lambdaCore M = ½·inf' Mval ≥ 0` (admissible `Mval ≥ 0` ⟹ `inf' ≥ 0`). -/
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:64:theorem bind_hlam (M : Fin (L + 1) → ℕ) : 0 ≤ lambdaCore M := by
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:65:  unfold lambdaCore
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:71:≥ 0 ⟺ λ (schurStateRed M) ≤ λ M` — the monotonicity of `lambdaCore` under the `schurState` width-reduction
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:75:    (hMono : lambdaCore (schurStateRed M) ≤ lambdaCore M) :
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:81:(`MinAdmMono.lambdaCore_schurStateRed_le`, #149 — the running-min-cap cone-transform), so the binding
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:84:  bind_hnReg M (lambdaCore_schurStateRed_le M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMGeneralAssembly.lean:33:`⨅` over `routeMIota M` of the per-leaf `monomialThreshold` is `½·minAdm(M) = lambdaCore`. Reduces to the
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:90:`nReg/2 + ofReal(lambdaCore M)` — the Skeleton `deepest_regular_core_normal_form` target. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:110:        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:113:        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:144:        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:317:`nReg/2 + lambdaCore(1,1,2) = 2/2 + 1/2 = 3/2`. The reduced `(1,1,2)` RLCT `= 1/2` (the cert's
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:318:`lambdaCore(1,1,2)`, the recursion's child value) enters as the hypothesis `hred` — deferred, not
lean/DLNFibre/DLN/RLCT/Validate/Case222Value.lean:8:shapes, and **every** leaf threshold is `3/2 = ½·Mval(deepest rank-1 stratum) = lambdaCore (2,2,2)`:
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:25:- `routeLayerAtlas_value_eq_lambdaCore` — `⨅ monomialThreshold = ofReal(lambdaCore M)` over the
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:32:lane (`= ½·minAdm = lambdaCore`) but whose `rlctAtOn = ⨅` content is the ANALYTIC COVER: the two
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:122:/-! ## The migrated value lane: `⨅ monomialThreshold = ofReal(lambdaCore M)` -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:125:layer-collapsing chart family of the per-leaf `monomialThreshold` is `ofReal(lambdaCore M)` (for
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:131:theorem routeLayerAtlas_value_eq_lambdaCore (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:133:      = ENNReal.ofReal (lambdaCore M : ℝ) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:149:`resolution_charts` is `rlctAtOn(core) = ⨅ monomialThreshold`. The VALUE (`= ½·minAdm = lambdaCore`)
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:178:`⨅ monomialThreshold = ½·minAdm(2,2,2) = 3/2 = lambdaCore(2,2,2)`, confirming the lane is
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:181:theorem routeLayerAtlas_value_eq_lambdaCore_M222 :
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteStep.lean:9:`3/2 = lambdaCore(2,2,2)`. This de-risks the committed type WITHOUT touching the general `routeStep` body
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteStep.lean:48:/-- `minAdm(M222) = 3` (so `lambdaCore(2,2,2) = 3/2`). -/
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteStep.lean:72:is `½·minAdm = 3/2 = lambdaCore(2,2,2)`. Consumes the banked `foldFamily_iInf_eq_half_minAdm` — validating
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1033:`deepest_regular_core_normal_form` (Skeleton.lean:1124) wants `nReg/2 + ofReal(lambdaCore M)`. The
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1034:gap is exactly the **R1 core-value** `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1035:`resolution_charts` + A1's `lambdaCore_eq_clean`/`⨅ monomialThreshold = lambdaCore` — R1's lane, in
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1042:R1 core-value `hcore : rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's lane) and the
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1044:regular shift `nReg/2` plus the closed-form core `ofReal(lambdaCore M)` — the exact
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1055:      = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1063:        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:40:`lambdaCore = 0`; the headline stays NON-STRICT / paper-faithful `r ≤ min`, audit-verified true). The
lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:326:branch-divisors (`[4,3]` for `(2,2,2)` → `3/2`). This is the COMBINATORIAL `½·minAdm` (`= lambdaCore`, the
lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:338:   (`aoyagiLambda = nReg/2 + lambdaCore`; L2's `nReg/2` on a non-degenerate root, `#70` on a degenerate root).
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:16:`ofReal(lambdaCore M)`. Folding the core value `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` is
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:17:**R1** (`resolution_charts` + A1), kept separate (the gauge chart carries no `lambdaCore`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:519:chart's full content: it carries NO `lambdaCore` (R1's value `rlctAtOn (dlnLoss M 0) 0 =
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:520:ofReal(lambdaCore M)` is folded separately). Assembled from the chart-existence (#44c) + the transport
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:8:RECURSION route to `rlctAtOn (dlnLoss M 0) 0 = ofReal (lambdaCore M)` (`= ½·minAdm`), iterating the
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:23:The COMBINATORIAL arithmetic (`lambdaCore M = nReg M / 2 + lambdaCore (redOf M)`, with `lambdaCore` of a
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:24:degenerate state `= 0`) makes the value telescope `lambdaCore M = ∑ nReg_k / 2` close; the GEOMETRIC
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:43:combinatorial telescope `harith` (`lambdaCore M = nReg M / 2 + lambdaCore (redOf M)`, with the degenerate
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:45:(lambdaCore M)`. Proved by strong recursion on `chainWidthSum` (`redOf` strictly decreases `ΣM`).
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:60:/-- `minAdm(M334) = 8` (so `lambdaCore(3,3,4) = 4`, matching the published RRR closed form). -/
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:84:lambdaCore(3,3,4)`. This is the BINDING coupled `diag(b)` witness (cert `verify-r1-diagb-334.md`): a per-row
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:131:`2` (`minAdm = 4`, `lambdaCore = 2`). So `(4,4,2,2)` exercises the corank-2 mechanism on a NON-binding
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:160:/-- `minAdm(M4422) = 4` (so `lambdaCore(4,4,2,2) = 2`, NOT `7/2` — the certificate's correction). -/
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:182:minAdm`), the `⨅` of the `foldDivisors` thresholds is `½·minAdm = ½·4 = 2 = lambdaCore(4,4,2,2)`. The `min`
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:253:/-- `minAdm(M3354) = 8` (so `lambdaCore(3,3,5,4) = 4`); the minimiser `T=(1,1,0)` is unique. -/
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:273:`½·minAdm = ½·8 = 4 = lambdaCore(3,3,5,4)`. The deep-sharing `L=3` witness (cert §6): the committed
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:71:`coreDeepest = ofReal(lambdaCore (square m))`, `a + b ≤ m`):
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:91:    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:110:        = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:18:`resolution_value_of_atlas` takes the atlas and proves `⨅ monomialThreshold = ofReal(lambdaCore M)`
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:19:SORRY-FREE + S2-FREE: `le_antisymm` ((C≥) ⟹ `⨅ ≥ ½·m₀`, (C=∃) ⟹ `⨅ ≤ ½·m₀`), then `½·m₀ = lambdaCore M`
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:20:definitionally (`lambdaCore := ½·inf' Mval`). The geometric residual is isolated entirely into the
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:130:lands definitionally on `lambdaCore M = ½·m₀`. -/
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:144:/-- `lambdaCore M = ½·(inf' Mval).toNat` as an `ℝ≥0∞` fact: the `ℚ`-valued `lambdaCore` cast through
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:147:theorem ofReal_lambdaCore_eq_half_inf (M : Fin (L + 1) → ℕ) :
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:148:    ENNReal.ofReal (lambdaCore M : ℝ)
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:155:  -- LHS: ofReal(lambdaCore) = ofReal((I.toNat : ℝ)/2).
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:156:  have hL : ENNReal.ofReal (lambdaCore M : ℝ) = ENNReal.ofReal ((I.toNat : ℝ) / 2) := by
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:157:    unfold lambdaCore
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:193:the chart monomial thresholds equals `ofReal(lambdaCore M)`. Sorry-free + S2-free, conditional on the
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:195:`⨅ ≤ ½·m₀` (`iInf_le`); then `½·m₀ = ofReal(lambdaCore M)` definitionally (`ofReal_lambdaCore_eq_half_inf`).
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:200:    (⨅ i : ι, monomialThreshold (d i) (k i) (h i)) = ENNReal.ofReal (lambdaCore M : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:201:  rw [ofReal_lambdaCore_eq_half_inf]
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:209:admissible stratum `Adm = {0}`, `Mval 0 = 1`, so `m₀ = 1` and `lambdaCore = ½`) a one-path atlas
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:237:/-- The non-vacuity value: the `M = ![1,1]` atlas yields `⨅ monomialThreshold = ofReal(lambdaCore)`
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:240:    = ENNReal.ofReal (lambdaCore (![1, 1] : Fin 2 → ℕ) : ℝ) :=
lean/DLNFibre/DLN/RLCT/Validate/MinAdmMono.lean:262:/-- **`hMono` — `lambdaCore (schurStateRed M) ≤ lambdaCore M`** (the binding-arithmetic monotonicity, #149).
lean/DLNFibre/DLN/RLCT/Validate/MinAdmMono.lean:264:theorem lambdaCore_schurStateRed_le (M : Fin (L + 1) → ℕ) :
lean/DLNFibre/DLN/RLCT/Validate/MinAdmMono.lean:265:    lambdaCore (schurStateRed M) ≤ lambdaCore M := by
lean/DLNFibre/DLN/RLCT/Validate/MinAdmMono.lean:266:  unfold lambdaCore
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:638:`⨅ monomialThreshold = ½·minAdm(2,2,2) = 3/2 = lambdaCore(2,2,2)` — fires on the worked anchor, confirming
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:18:`L = 1` core `lambdaCore (H−r)`, where at one reduced layer `lambdaCore M = M⁰·M¹/2`) closes the
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:201:/-- **`lambdaCore` at `L = 1`.** A single reduced layer has the all-zero exponent vector as its only
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:202:admissible `T` (the last-exponent constraint forces `T 0 = 0`), so `lambdaCore M = M⁰·M¹/2`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:203:theorem lambdaCore_L1 (M : Fin (1 + 1) → ℕ) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:204:    lambdaCore (L := 1) M = (1 / 2 : ℚ) * ((M 0 * M (Fin.last 1) : ℕ) : ℚ) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:205:  unfold lambdaCore
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:240:`lambdaCore (H−r)`. At `L = 1` both reduce to the single full block `H⁰·H¹/2`
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:241:(`= r(H⁰+H¹−r)/2 + (H⁰−r)(H¹−r)/2`, the latter being `lambdaCore (H−r)`). Proven sorry-free:
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:242:`rlctAt_dlnLoss_L1` (the full-block RLCT) + `lambdaCore_L1` (the core arithmetic) + the
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:249:        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:251:  -- right side: nReg/2 + ofReal(lambdaCore (H-r)).  Show both = (H0*H1)/2.
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:254:  -- lambdaCore (H-r) = (H0-r)(H1-r)/2 ≥ 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:256:  have hMcore : lambdaCore (L := 1) M = (1 / 2 : ℚ) * ((M 0 * M (Fin.last 1) : ℕ) : ℚ) :=
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:257:    lambdaCore_L1 M
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:262:  have hcoreReal : (lambdaCore (L := 1) M : ℝ) = ((M 0 * M (Fin.last 1) : ℕ) : ℝ) / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:265:  have hcoreENN : ENNReal.ofReal (lambdaCore (L := 1) M : ℝ)
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:13:> `rlctOf M = ofReal (lambdaCore M)`   ( `= ½·minAdm`, the value cobuild's L2-Skeleton bridge consumes)
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:17:monotonicity `hMono` (`lambdaCore (schurStateRed M) ≤ lambdaCore M`, rs-grind's #149 — carried here as a
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:38:equals the combinatorial value: `rlctOf M = ofReal (lambdaCore M)`.
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:41:`lamOf := lambdaCore`, `degenChild := fun M => isLeafNode (schurStateRed M)`, discharging the combinatorial
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:44:theorem binding_rlct_eq_lambdaCore_of_hstep
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:46:    (hMono : ∀ M : Fin (L' + 1 + 1) → ℕ, lambdaCore (schurStateRed M) ≤ lambdaCore M)
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:52:    rlctOf M = ENNReal.ofReal (lambdaCore M) :=
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:54:    schurStateRed bindNReg lambdaCore rlctOf (fun M => isLeafNode (schurStateRed M))
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:64:meeting-point — `hMono` discharged). Since `#149` is now PROVEN (`MinAdmMono.lambdaCore_schurStateRed_le`,
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:67:`rlctOf M = ofReal (lambdaCore M)` hangs on EXACTLY the two geometric obligations fm3 owns — the per-node
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:71:theorem binding_rlct_eq_lambdaCore_of_hstep'
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:78:    rlctOf M = ENNReal.ofReal (lambdaCore M) :=
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:79:  binding_rlct_eq_lambdaCore_of_hstep rlctOf
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:80:    (fun M => lambdaCore_schurStateRed_le M) hstep hbase M
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:22:    rlctAtOn R 0 = extra/2 + lambdaCore(M'),   extra = m(a+b) − ab,  M' = (m−a, m−a−b, m−b),
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:25:needs the **self-contained arithmetic** `extra/2 + lambdaCore(M') ≥ lambdaCore(square m)` (the
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:26:deepest reduced widths at L = 2 are the square `(m, m, m)`; `coreDeepest = lambdaCore(square m)`),
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:28:(`extra_half_add_lambdaCore_Mprime_ge_square`, sorry-free, clean-three) via the banked symbolic
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:62:`extra/2 + lambdaCore(M') ≥ lambdaCore(square m)`, `extra = m(a+b) − ab`,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:172:/-- **§6 — the self-contained arithmetic lemma.** `extra/2 + lambdaCore(M') ≥ lambdaCore(square m)`
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:174:square `(m, m, m)`, so `coreDeepest = lambdaCore (square m)`. Pure `Mval`/`Adm`/`Finset.inf'`
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:178:theorem extra_half_add_lambdaCore_Mprime_ge_square (m a b : ℕ) (hab : a + b ≤ m) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:179:    lambdaCore (squareWidths m)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:180:      ≤ (extraCount m a b : ℚ) / 2 + lambdaCore (MprimeWidths m a b) := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:200:  -- lift the `ℤ` inequality through `lambdaCore = (1/2)·(inf' Mval)`
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:201:  rw [lambdaCore, lambdaCore, ← hIsq, ← hIp]
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:205:/-- `lambdaCore M ≥ 0` (admissible `Mval ≥ 0` on the cone ⟹ `inf' ≥ 0`). Reuses the banked
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:207:theorem lambdaCore_nonneg_L2 (M : Fin 3 → ℕ) : 0 ≤ lambdaCore M := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:208:  rw [lambdaCore]
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:214:`coreDeepest = ofReal(lambdaCore (square m))` and the degraded-core value `ofReal(lambdaCore M')`,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:216:    coreDeepest ≤ (extra : ℝ≥0∞)/2 + ofReal(lambdaCore M').
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:218:Bridges the `ℚ` lemma through `ENNReal.ofReal` (both `lambdaCore`s nonneg; `(extra:ℝ≥0∞)/2 =
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:220:theorem coreDeepest_le_extra_half_add_lambdaCore_Mprime (m a b : ℕ) (hab : a + b ≤ m) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:221:    ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:223:        + ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:224:  have hQ := extra_half_add_lambdaCore_Mprime_ge_square m a b hab
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:226:  have hsqnn : (0 : ℚ) ≤ lambdaCore (squareWidths m) := lambdaCore_nonneg_L2 _
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:227:  have hpnn : (0 : ℚ) ≤ lambdaCore (MprimeWidths m a b) := lambdaCore_nonneg_L2 _
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:237:  have hQR : (lambdaCore (squareWidths m) : ℝ)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:238:      ≤ (extraCount m a b : ℝ) / 2 + (lambdaCore (MprimeWidths m a b) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:255:ofReal(lambdaCore M')`. Combined with the §6 arithmetic
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:256:(`coreDeepest_le_extra_half_add_lambdaCore_Mprime`)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:257:and `coreDeepest = ofReal(lambdaCore (square m))`, this gives `coreDeepest ≤ rlctAtOn R t0` — the
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:266:degraded-core value `hDegraded : rlctAtOn R₂ t0₂ = ofReal(lambdaCore M')` (the §5 interface
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:268:`coreDeepest = ofReal(lambdaCore (square m))`,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:276:    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:287:    (hDegraded : rlctAtOn R₂ t0₂ = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:297:  exact coreDeepest_le_extra_half_add_lambdaCore_Mprime m a b hab
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:316:`dlnLoss M 0` at the origin `(0 : Params M)` has local RLCT `ofReal(lambdaCore M)`. The
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:324:      = ENNReal.ofReal (lambdaCore M : ℝ)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:336:      = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ) :=
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:350:(square deepest reduced widths `M = (m,m,m)`, `coreDeepest = ofReal(lambdaCore (square m))`), given
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:363:    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:386:    (hDegraded : rlctAtOn R₂ t0₂ = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMValue.lean:7:`monomialThreshold` equals `½·minAdm(M)` (`= lambdaCore`, the CORE). This is the abstract value-fold
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:17:  `rlctAt H (dlnLoss H B) deepestPoint = nReg/2 + rlctAtOn(dlnLoss M 0) 0` (core RLCT, NOT `lambdaCore`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:20:- **`hRValue`** — R1's value `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)` (= `resolution_charts`
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:21:  ▸ A1 `lambdaCore_eq_clean`; cover wires the Skeleton `resolution_charts`, A1 supplies the value
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:26:`rlctAt H (dlnLoss H B) deepestPoint = nReg/2 + ofReal(lambdaCore M)`. Proof = the value-free
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:40:(`rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`), the local RLCT at the deepest point IS the
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:41:closed-form value `nReg/2 + ofReal(lambdaCore M)` — the Skeleton `deepest_regular_core_normal_form`
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:62:        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:65:        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by

exec
/bin/bash -lc "sed -n '1,200p' lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean" in /tmp/p44-scope
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestNormalFormWiring` — the L2 normal-form CONVERGENCE node, pre-staged

The Skeleton `deepest_regular_core_normal_form` (the **value-form** of the L2 reduction) is the
convergence node of the λ-spine (the #40 audit): it is **not** closeable by L2 alone — it needs the
L2 chart geometry AND R1's value composed. This module pre-stages that wiring as a CONDITIONAL lemma
taking the two gates as explicit hypotheses, so when the gates land the Skeleton sorry is a one-line
fill (`exact deepest_normal_form_of_value …`), with the convergence already de-risked + audited green.

The two inputs (both named, neither glossed):

- **`hGne`** — the reduced-core germ-nonvanishing carve-out. Feeds the VALUE-FREE reduction
  `deepest_regular_core_reduces` (`DeepestGaugeChart`, itself sorry-free modulo the L2 chart existence
  `deepest_gauge_squeeze_exists` = cobuild-sub34's regAbsorb instance), which lands
  `rlctAt H (dlnLoss H B) deepestPoint = nReg/2 + rlctAtOn(dlnLoss M 0) 0` (core RLCT, NOT `lambdaCore`).
  `hGne` holds for the non-degenerate reduced chain (no interior `M_s = 0`, crux2 #65's
  `dlnLoss_deepest_core_ae_ne_zero`); the degenerate boundary is the separate #70 direct-Morse lemma.
- **`hRValue`** — R1's value `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)` (= `resolution_charts`
  ▸ A1 `lambdaCore_eq_clean`; cover wires the Skeleton `resolution_charts`, A1 supplies the value
  step). This is the singular-core resolution value — the geometric content of R1, kept SEPARATE from
  the L2 chart fact (the #40-audit scope split).

The conclusion is the Skeleton `deepest_regular_core_normal_form` value-form verbatim:
`rlctAt H (dlnLoss H B) deepestPoint = nReg/2 + ofReal(lambdaCore M)`. Proof = the value-free
reduction (consuming `hGne`) rewritten by `hRValue`. **Gate-independent**: this lemma's OWN proof is
closeable now (the two gates are hypotheses, not sorries) — only its eventual USE in Skeleton awaits the
gates discharging. `M = fun s => H s - r` throughout (the reduced widths).
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The L2 normal-form WIRING (the convergence node, pre-staged).** Given the reduced-core
germ-nonvanishing `hGne` (⟹ the value-free L2 reduction applies) and R1's resolution value `hRValue`
(`rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`), the local RLCT at the deepest point IS the
closed-form value `nReg/2 + ofReal(lambdaCore M)` — the Skeleton `deepest_regular_core_normal_form`
target. Proof: `deepest_regular_core_reduces` (value-free, `nReg/2 + rlctAtOn(core) 0`) ▸ `hRValue`.

This is the assembly seam where the L2 chart geometry (#59, via `deepest_regular_core_reduces`) and
R1's value (#39 ▸ A1, via `hRValue`) MEET to produce the value-form. Pre-staged so the Skeleton sorry
at `deepest_regular_core_normal_form` collapses to `exact deepest_normal_form_of_value … hGne hRValue`
once both gates land. -/
theorem deepest_normal_form_of_value (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hGne : ∃ U ∈ 𝓝 (0 : Fin (flatDim (fun s => H s - r)) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm z) ≠ 0)
    (hRValue :
      rlctAtOn
          (fun A : Params (fun s => H s - r) =>
            dlnLoss (fun s => H s - r)
              (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
          (fun _ => 0 : Params (fun s => H s - r))
        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
  rw [deepest_regular_core_reduces H r B hB hr hL hGne, hRValue]

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc "sed -n '1,200p' lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean" in /tmp/p44-scope
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Skeleton
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# `DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion` — the general-M resolution recursion (det-1 phase)

The sound det-1 half of the general-M resolution (C2 = det-1 GL-straighten THEN blow-up). The crux
deliverables, all PROVEN (0 sorry):

- `schur_recursion_step_sound` — the **measure-preserving straightening phase** RLCT split: given a
  measure-preserving chart `χ` factoring the loss near the deepest point as `u·((∑ xᵢ²) + G²)`, the
  RLCT splits as `nReg/2 + rlctAtOn(G²)`. (Transport `rlctAtOn_comp_homeomorph` + germ-rewrite
  `rlctAtOn_germ_local` + unit-strip `rlctAtOn_unit_invariant_aux` + smooth-block `S1.5`.)
- `rlctAtOn_germ_local` — general-domain `rlctAtOn` germ-locality (reusable bedrock).
- `ChainDimSplit` — the additive width split (`drop + red = M`, the reduced chain).
- `prod_one_layer` / `dlnLoss_one_layer_deepest` — the L=1 smooth-block leaf (recursion terminator).

SOUNDNESS NOTE (the (C2) finding): the *clean* `rlctAtOn(dlnLoss M 0) 0 = nReg/2 + rlctAtOn(Mred) 0`
WITHOUT a measure-preserving chart hypothesis is **FALSE** (a measure-preserving recursion conserves
dimension ⟹ telescopes to ambient/2 = 4 for (2,2,2) ≠ the verified 3/2). The general-M chart is the
det-1 straightening (here) THEN a blow-up (monomial Jacobian → `⨅ monomialThreshold`, fm's cover
lane, applied to the residual `G`). The measure-preserving hypothesis on `χ` is load-bearing and
confines this lemma to the det-1 straightening phase; the blow-up's monomial weights live downstream.
Artifacts: `expeditions/.../14-r1-design/codex/g32-chart-structure-{prompt,answer}.md`.
-/

open MeasureTheory
open scoped ENNReal
namespace DLNFibre.DLN.RLCT

/-! The general-domain `rlctAtOn` unit-invariance (the prereq) now lives in `Foundations/S1Local.lean`
as `rlctAtOn_unit_invariant_aux` (beside `rlct_unit_invariant_aux`), reachable transitively via the
`Skeleton` import. Removed from this scratch file to avoid duplication. -/

/-- **The chain dimension split** (Codex Q4): an ADDITIVE split of the width vector `M` into a dropped
part (the resolved pivot dims `δ_s`) and a reduced part (the residual chain widths `M^s − δ_s`),
carried as `drop s + red s = M s` to avoid `Fin (M s − δ)` underflow. `splitEquiv` is the per-vertex
`Fin (drop s) ⊕ Fin (red s) ≃ Fin (M s)` that all the casts route through. -/
structure ChainDimSplit {L : ℕ} (M : Fin (L + 1) → ℕ) where
  drop : Fin (L + 1) → ℕ
  red : Fin (L + 1) → ℕ
  hsum : ∀ s, drop s + red s = M s
  hdrops : 0 < ∑ s, drop s   -- the termination condition: ΣM strictly drops on recursion

/-- The reduced width vector of a split (the residual chain's dimensions). -/
def ChainDimSplit.redM {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M) : Fin (L + 1) → ℕ :=
  S.red

/-- The per-vertex split equivalence `Fin (drop s) ⊕ Fin (red s) ≃ Fin (M s)`. -/
def ChainDimSplit.splitEquiv {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M) (s : Fin (L + 1)) :
    (Fin (S.drop s) ⊕ Fin (S.red s)) ≃ Fin (M s) :=
  (finSumFinEquiv).trans (finCongr (S.hsum s))

/-! ## The G3.2 det-1 Schur straightening — `IsSchurStraighten` (the (A) sub-step, SPECIFY)

> **SUPERSEDED (2026-06-22, pp2 #129/#130, controller-blessed).** This `IsSchurStraighten` datum and
> `schur_straighten_of_data` encode the CLEAN measure-preserving-chart route (`flatCore ∘ χ =ᶠ u · Φ` via
> a homeomorphism `χ`). pp2 #129 (decorrelated) RETRACTED that route: the per-node transvection is det-1 /
> measure-preserving (`mp_schur_transvection_vec`) but the LOSS is NOT invariant under it (`L` unipotent
> ⇏ orthogonal), so the clean factor through a c-o-v is unreachable. The CORRECTED datum is
> `IsSchurStraightenSqueeze` (below): the two-sided SQUEEZE `c₁·Φ ≤ flatCore ≤ c₂·Φ` at the deepest point
> (NO chart, NO Jacobian), consumed by `schur_recursion_step_squeeze`. The decls here are retained as a
> TRUE-but-off-path record: `schur_straighten_of_data` is a true conditional (it packages the datum given
> the clean factor as a hypothesis), but the clean-factor hypothesis is not satisfiable by the actual loss.
> Do NOT build the recursion on these; use the squeeze datum.

The (C2) node is **(B) blow-up THEN (A) det-1 Schur** (pp-hall g118/g121). The lanes split it:
**fm's (B) lane** is the coordinate-subspace blow-up (`pivotBlowupOn`, Jacobian `|u|^{Mval−1}`, the
monomial weight `(k,h)` → `monomialThreshold`). **My (A) lane** is the det-1 Schur straightening
WITHIN each blow-up chart: once the blow-up has made a leading pivot a UNIT, a unit-pivot row/col
clear (Lemma-2-general / the `(uᵢ,ψᵢ)` adapted basis) reduces the residual to a strictly-smaller
zero-core `‖∏C'‖²` and STRAIGHTENS the bilinear rank-defect center `{r−pq=0}` to a coordinate center
`{w=0}` (the det-1 change `w := r−pq`). **Jacobian = 1 (measure-preserving) — NO monomial weight;**
the monomial comes only from fm's (B) blow-up. This is the `resolvedForm` the controller named: the
det-1 normal form handed to fm's blow-up cover.

This is exactly the chart `schur_recursion_step_sound` consumes (a MEASURE-PRESERVING `χ` factoring
`dlnLoss M 0` as `u·((∑ regular²) + dlnLoss M' 0)`). The det-1 Schur is the (A) sub-step; it requires
a UNIT pivot (the hypothesis fm's blow-up supplies — at the bare singular origin the pivot is `0` and
this fails, which is WHY the blow-up runs first). `#109`'s substitution algebra (all diff=0) is the
SOUND core of this step. -/

/-- **The det-1 Schur straightening datum (the (A) sub-step) — SPECIFY, fm's 5-point contract.** A
measure-preserving chart `χ` (Jacobian 1, the det-1 Schur / Lemma-2-general) factoring `dlnLoss M 0`
near the deepest point as a unit `u` times `(regular smooth block) + (reduced-chain core dlnLoss M' 0)`,
with `M' = S.red` strictly smaller, AND exposing the explicit coordinate-center index set the blow-up
fires on. NO monomial weight (that is fm's blow-up). This is the `resolvedForm`. Fields carry fm's
5-point ask:
- (1 TYPE) `χ : (Fin nReg → ℝ) × (Fin N' → ℝ) ≃ₜ (Fin N → ℝ)`, `N'` the reduced ambient.
- (2 MP/det-1) `measurePreserving` — fm's glue composes through with NO Jacobian weight.
- (3 COORD-CENTER) `active : Finset (Fin N')` + pivot `p` + `centerCoord`: the rank-defect center is the
  coordinate subspace `{x | ∀ i ∈ active, x i = 0}` (the index set `g5_pivotNode` blows up).
- (4 REDUCED-CHAIN) `S.red` = M' + `flatRedCore`'s reduced-core component + `measure_drops`.
- (5 STRICT-TRANSFORM) `factor` — `flatCore ∘ χ = u · flatRedCore` near `0` (the rewrite fm's integrand
  transport uses; with the analytic unit `u`, MP-transported, no new proof). -/
structure IsSchurStraighten {L : ℕ} {N N' : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
    (nReg : ℕ)
    (flatCore : (Fin N → ℝ) → ℝ)             -- `dlnLoss M 0` in the post-blow-up flat coords
    (flatRedCore : (Fin nReg → ℝ) × ((Fin N' → ℝ)) → ℝ)  -- split target (reg block + reduced core on N')
    (redEmbed : (Fin N' → ℝ) → Params S.red)  -- the flat-embed of the reduced coords into Params M'
    (χ : ((Fin nReg → ℝ) × (Fin N' → ℝ)) ≃ₜ (Fin N → ℝ))  -- the det-1 Schur straightening chart
    (u : (Fin nReg → ℝ) × (Fin N' → ℝ) → ℝ)
    (active : Finset (Fin N')) (p : Fin N') : Prop where
  /-- (2) The straightening is MEASURE-PRESERVING (det-1, the (A) sub-step contributes no weight). -/
  measurePreserving : MeasurePreserving χ volume volume
  /-- `u` is measurable (the analytic unit). -/
  umeas : Measurable u
  /-- (4) REDUCED-CHAIN (explicit): the split target is the regular block plus the EXPLICIT reduced
  core `dlnLoss M' 0` (`M' = S.red`) on the embedded reduced coords — so fm's structural recursion
  descends on the smaller chain `S.red`, not an abstract residual. -/
  redCore_eq : ∀ q, flatRedCore q = (∑ i, q.1 i ^ 2) + dlnLoss S.red 0 (redEmbed q.2)
  /-- (5) STRICT-TRANSFORM: the det-1 normal form near the deepest point —
  `core ∘ χ = unit · (reg block + reduced core)`. -/
  factor : (fun q => flatCore (χ q)) =ᶠ[nhds 0] (fun q => u q * flatRedCore q)
  /-- (3) COORDINATE-CENTER: the pivot lies in the active set (the blow-up's center coords), so the
  rank-defect center `{q | ∀ i ∈ active, q.2 i = 0}` is a coordinate subspace `g5_pivotNode` can fire
  on. (`active`/`p` match `pivotBlowupOn`'s `(active : Finset) (p)` signature, S1G5Charts:384.) -/
  pivot_active : p ∈ active
  /-- (3) the active set is the blow-up codimension `Mval`-many center coords (nonempty: a real drop). -/
  active_nonempty : active.Nonempty
  /-- (4) Well-foundedness (pp #123 field-6): the reduced chain is strictly smaller. -/
  measure_drops : ∑ s, S.red s < ∑ s, M s

/-! ## Body sub-lemma (1): the hard-1-pivot Schur block-identity (the `(L,R)` transvections)

The #127 witness's `(L,R)` transvection pair, at the hard-1 pivot: `L = fromBlocks 1 0 (−c) 1`
(clear col 0), `R = fromBlocks 1 (−b) 0 1` (clear row 0), both UNIPOTENT (det 1), with
`L · (fromBlocks 1 b c D) · R = fromBlocks 1 0 0 (D − c·b)` — block-diagonalizing to the `1×1` regular
pivot ⊕ the reduced Schur factor `S = D − c·b`. Specializes Mathlib's `fromBlocks_eq_of_invertible₁₁`
(the LDU/Schur factorization) to `A = 1` (`⅟1 = 1`). -/
theorem hardPivot_schur_blockId {m n l : ℕ}
    (b : Matrix (Fin m) (Fin n) ℝ) (c : Matrix (Fin l) (Fin m) ℝ) (D : Matrix (Fin l) (Fin n) ℝ) :
    (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ) 0 (-c) 1)
        * (Matrix.fromBlocks 1 b c D)
        * (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ) (-b) 0 1)
      = Matrix.fromBlocks 1 0 0 (D - c * b) := by
  -- Direct double `fromBlocks_multiply`. L·A first (clear col 0), then ·R (clear row 0).
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  -- Discharge the four resulting blocks by ring/matrix algebra.
  congr 1 <;>
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.neg_mul, Matrix.mul_neg, add_zero, zero_add, Matrix.add_mul, Matrix.mul_add] <;>
    abel_nf <;>
    ring_nf

/-- **G3.2 crux — the det-1 Schur straightening, HONEST packaging form (GREEN, mine).**

The unconditional existence `∃ χ u …, IsSchurStraighten M S nReg flatCore …` for an *arbitrary*
`flatCore` is **false** (two independent obstructions, decorrelated pp/Codex 2026-06-22, controller
Decision (A) 2026-06-22 — dropped):
- (i) DIMENSION — a homeomorphism `(Fin nReg → ℝ) × (Fin N' → ℝ) ≃ₜ (Fin N → ℝ)` needs
  `N = nReg + N'` (invariance of domain); quantifying the three dims independently makes it impossible
  when `N ≠ nReg + N'`.
- (ii) CLEAN-FACTOR — `redCore_eq` pins `flatRedCore 0 = 0`, so `factor` forces `flatCore (χ 0) = 0`
  *and* a clean product factorisation `flatCore∘χ = u·(∑Eᵢ²+core)`; the design finding
  `g128-L2-seam-squeeze-bridge.md` shows that exact clean form is **NOT** reachable by a measure-
  preserving change of variables (the honest route is the two-sided SQUEEZE), so even with
  `flatCore = dlnLoss M 0` the unconditional form fails.

So the deliverable is the **packaging**: the heavy *existence* of the measure-preserving chart `χ`
realising the clean factor `flatCore∘χ =ᶠ u·(∑Eᵢ²+core)` is a separate downstream obligation (the chart-
existence content — disputed clean-MP-c-o-v vs #127 squeeze, controller reconciling); supplied here as a
hypothesis, this lemma assembles the `IsSchurStraighten` package, discharging the bookkeeping fields
(`umeas`, `redCore_eq`, `pivot_active`, `active_nonempty`, `measure_drops`) from the `ChainDimSplit` +
the supplied data. The locked `IsSchurStraighten` interface is intact; the statement is exactly what is
true. -/
theorem schur_straighten_of_data {L : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
    (nReg N N' : ℕ) (flatCore : (Fin N → ℝ) → ℝ)
    (redEmbed : (Fin N' → ℝ) → Params S.red)
    (χ : ((Fin nReg → ℝ) × (Fin N' → ℝ)) ≃ₜ (Fin N → ℝ))
    (hχmp : MeasurePreserving χ volume volume)
    (u : (Fin nReg → ℝ) × (Fin N' → ℝ) → ℝ) (humeas : Measurable u)
    (active : Finset (Fin N')) (p : Fin N') (hp : p ∈ active)
    -- the supplied clean germ-factorisation (the g128 straightening content, downstream):
    (hfactor : (fun q => flatCore (χ q)) =ᶠ[nhds 0]
        (fun q => u q * ((∑ i, q.1 i ^ 2) + dlnLoss S.red 0 (redEmbed q.2)))) :
    ∃ (flatRedCore : (Fin nReg → ℝ) × (Fin N' → ℝ) → ℝ)
      (redEmbed' : (Fin N' → ℝ) → Params S.red)
      (χ' : ((Fin nReg → ℝ) × (Fin N' → ℝ)) ≃ₜ (Fin N → ℝ))
      (u' : (Fin nReg → ℝ) × (Fin N' → ℝ) → ℝ) (active' : Finset (Fin N')) (p' : Fin N'),
      IsSchurStraighten M S nReg flatCore flatRedCore redEmbed' χ' u' active' p' := by
  refine ⟨fun q => (∑ i, q.1 i ^ 2) + dlnLoss S.red 0 (redEmbed q.2),
    redEmbed, χ, u, active, p, ?_⟩
  refine
    { measurePreserving := hχmp
      umeas := humeas
      redCore_eq := fun q => rfl
      factor := hfactor
      pivot_active := hp
      active_nonempty := ⟨p, hp⟩
      measure_drops := ?_ }
  -- ∑ S.red < ∑ M from drop + red = M with 0 < ∑ drop (the ChainDimSplit termination measure).
  have hle : ∑ s, S.red s ≤ ∑ s, M s :=
    Finset.sum_le_sum fun s _ => by have := S.hsum s; omega
  have hne : ∑ s, S.red s ≠ ∑ s, M s := by
    intro hEq
    have hdrop0 : ∑ s, S.drop s = 0 := by
      have hadd : ∑ s, S.drop s + ∑ s, S.red s = ∑ s, M s := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun s _ => S.hsum s
      omega

exec
/bin/bash -lc 'rg "reduced_transport" -n lean/DLNFibre/DLN' in /tmp/p44-scope
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:18:  its transport lemmas (`rlctAtOn_reduced_transport`, `schur_recursion_step_sound`/`_squeeze`), and the
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:85:crux2's banked `rlctAtOn_reduced_transport` datum (det-1 measure-preserving reindex) closing the descent:
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:110:`rlctAtOn_reduced_transport` (det-1 MP); the bundled datum + the anchored `hzero` give the
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:116:  rlctAtOn_reduced_transport S rt.G rt.redEmbed rt.hmp rt.hemb _ rt.hzero rt.hredCore
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:445:`rlctAtOn_reduced_transport`). If the post-blow-up reduced core `G` pulls back the COLLAPSED chain loss
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:649:theorem rlctAtOn_reduced_transport {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M)

exec
/bin/bash -lc "sed -n '600,760p' lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean" in /tmp/p44-scope
 succeeded in 0ms:
/-- **The per-node existence — `schur_straighten_squeeze_exists` (PROVEN, closes the per-node lane).**
At the post-blow-up 2-factor Schur node, the `IsSchurStraightenSqueeze` datum EXISTS (with explicit
constants `c₁ = (2(1+T²))⁻¹ > 0`, `c₂ = 2+2T²`). The blow-up lane's job — presenting the node loss in
Schur form near the deepest point with a bounded pivot column — enters as the EXPLICIT interface
hypothesis `hnode` (per Codex g132: the `flatCore = ‖Â·A2‖²` coordinate layout is the blow-up (B)-lane
contract, supplied here as a hypothesis, NOT asserted as `dlnLoss M 0 coords = ‖Â·A2‖²` which would
smuggle guessed plumbing). Given that presentation (`flatCore w = ∑ Erowⱼ² + ‖b·Erow + S·Γ‖²`,
`G(w.2)² = ‖S·Γ‖²`, `‖b‖² ≤ T²` on a nbhd), the datum's `squeeze` field is `schur_node_squeeze_unif`;
the rest are the supplied measurability / reduced-core / germ / well-foundedness contracts. This is the
g131-certified existence content transcribed to Lean — the squeeze, not a clean MP factor (#129). -/
theorem schur_straighten_squeeze_exists {L nReg : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
    {Y : Type*} [MeasureSpace Y] [TopologicalSpace Y] [Zero Y]
    {Mblk : Type*} [Fintype Mblk]
    (flatCore : (Fin nReg → ℝ) × Y → ℝ) (G : Y → ℝ) (redEmbed : Y → Params S.red) (T : ℝ)
    (bcol : (Fin nReg → ℝ) × Y → Mblk → ℝ)
    (SΓ : (Fin nReg → ℝ) × Y → Mblk → Fin nReg → ℝ)
    (hFmeas : Measurable flatCore) (hGmeas : Measurable G)
    (hredCore : ∀ y, G y ^ 2 = dlnLoss S.red 0 (redEmbed y))
    (hGne : ∃ U ∈ nhds (0 : Y), ∀ᵐ z ∂(volume.restrict U), G z ≠ 0)
    (hdrop : ∑ s, S.red s < ∑ s, M s)
    (hnode : ∃ U ∈ nhds ((0, 0) : (Fin nReg → ℝ) × Y), ∀ w ∈ U,
        flatCore w = (∑ j, (w.1 j) ^ 2) + (∑ i, ∑ j, (bcol w i * w.1 j + SΓ w i j) ^ 2)
        ∧ G w.2 ^ 2 = (∑ i, ∑ j, (SΓ w i j) ^ 2)
        ∧ (∑ i, (bcol w i) ^ 2) ≤ T ^ 2) :
    ∃ c₁ c₂, IsSchurStraightenSqueeze M S flatCore G redEmbed c₁ c₂ := by
  refine ⟨1 / (2 * (1 + T ^ 2)), 2 + 2 * T ^ 2, ?_⟩
  obtain ⟨U, hU, hpres⟩ := hnode
  refine
    { Fmeas := hFmeas
      Gmeas := hGmeas
      redCore_eq := hredCore
      Gne := hGne
      c₁pos := by positivity
      c₂pos := by positivity
      measure_drops := hdrop
      squeeze := ⟨U, hU, fun w hw => ?_⟩ }
  obtain ⟨hflat, hGsq, hbT⟩ := hpres w hw
  have hΦ : smoothBlockSplitForm G w = (∑ j, (w.1 j) ^ 2) + (∑ i, ∑ j, (SΓ w i j) ^ 2) := by
    simp only [smoothBlockSplitForm]; rw [hGsq]
  obtain ⟨hlo, hhi⟩ := schur_node_squeeze_unif (w.1) (bcol w) (SΓ w) T hbT
  exact ⟨by rw [hΦ]; positivity, by rw [hΦ, hflat]; exact hlo, by rw [hΦ, hflat]; exact hhi⟩

/-- **The reduced-chain RLCT-transport** (closes rv3's FLAG-A — the recursion-CLOSING link). The datum's
`redCore_eq` is a POINTWISE pullback `G y² = dlnLoss S.red 0 (redEmbed y)`; alone it does NOT give
`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) …`. This supplies the transport: if `redEmbed` is a
measure-preserving homeomorphism `Y ≃ₜ Params S.red` anchored (`redEmbed 0 = redZero`), then
`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) redZero` (`rlctAtOn_comp_homeomorph`). The basepoint
`redZero` is passed EXPLICITLY (`Params` has no canonical `Zero`; the reduced deepest point is named by
the producer). The recursion-assembly step discharges this with the datum to descend the RLCT. -/
theorem rlctAtOn_reduced_transport {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M)
    {Y : Type*} [MeasureSpace Y] [TopologicalSpace Y] [Zero Y]
    (G : Y → ℝ) (redEmbed : Y ≃ₜ Params S.red)
    (hmp : MeasurePreserving redEmbed volume volume) (hemb : MeasurableEmbedding redEmbed)
    (redZero : Params S.red) (hzero : redEmbed 0 = redZero)
    (hredCore : ∀ y, G y ^ 2 = dlnLoss S.red 0 (redEmbed y)) :
    rlctAtOn (fun y => G y ^ 2) (0 : Y) = rlctAtOn (dlnLoss S.red 0) redZero := by
  have hpull : (fun y => G y ^ 2) = (fun y => dlnLoss S.red 0 (redEmbed y)) := by
    funext y; exact hredCore y
  rw [hpull, rlctAtOn_comp_homeomorph redEmbed hmp hemb (dlnLoss S.red 0) 0, hzero]

/-! ## The L=1 base (the `block_elimination` prototype)

The recursion's leaf. At `L = 1` a `Params` is a SINGLE matrix `A : Matrix (Fin (M 0)) (Fin (M 1)) ℝ`
and `prod M A = A` (a one-term product), so at the deepest point `B = 0` the loss is ALREADY the pure
smooth block `dlnLoss M 0 A = ∑ᵢⱼ (A i j)² = ‖A‖²_F` — no chart, no unit, the reduced chain is empty.
This is what terminates the recursion (the `nReg = M0·M1` regular generators, `red = 0`). The genuine
Schur content (a NONTRIVIAL target `B` of rank `r`) is the `block_elimination` prototype: regular
row/column ops carry `B` to `diag(E_r, 0)`, exposing the `r×r` regular block — but at the deepest
point `B = 0` (`rank 0 = 0`), `block_elimination` degenerates to the all-smooth case, confirming the
leaf. Below: the L=1 deepest-point loss is the entrywise sum of squares (the smooth-block leaf form),
proved directly from `prod` at `L = 1`. -/

/-- `prod` at `L = 1`, entrywise: the single layer matrix `A 0` (a one-term product `1 · A 0`). The
index types match definitionally at `L = 1` (`(0 : Fin 1).castSucc = (0 : Fin 2)`,
`(0 : Fin 1).succ = Fin.last 1`), so `A 0` indexes by `i, j` directly. Mirrors `prod_two_layer`'s
`convert …one_mul…using 2` cast-discharge. -/
theorem prod_one_layer (M : Fin 2 → ℕ) (A : Params M)
    (i : Fin (M 0)) (j : Fin (M (Fin.last 1))) :
    prod M A i j = A 0 i j := by
  unfold prod
  simp only [prodAux, eq_mpr_eq_cast]
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) j using 2

/-- **L=1 base — the smooth-block leaf.** At `L = 1` and the deepest point `B = 0`, the loss is
the pure entrywise sum of squares of the single layer matrix `A 0` — already the smooth-block
normal form (`nReg = M0·M1` regular generators, empty reduced chain). This terminates the Schur
recursion: there is nothing left to pivot. (The genuine Schur split is for `B ≠ 0` of rank `r` via
`block_elimination`; at the deepest point `rank 0 = 0`, the regular `E_r` block is empty, the whole
loss is smooth.) -/
theorem dlnLoss_one_layer_deepest (M : Fin 2 → ℕ) (A : Params M) :
    dlnLoss M 0 A = ∑ i, ∑ j, (A 0 i j) ^ 2 := by
  unfold dlnLoss
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Matrix.sub_apply, Matrix.zero_apply, sub_zero, prod_one_layer]

/-! `dlnLoss_nonneg` now lives in `Foundations/Loss.lean` (reusable bedrock), reachable via the
`Skeleton` import. Removed from this scratch file to avoid duplication. -/

end DLNFibre.DLN.RLCT


exec
/bin/bash -lc 'rg "rlctAtOn (dlnLoss" -n lean/DLNFibre -g"*.lean"' in /tmp/p44-scope
 exited 2 in 0ms:
rg: regex parse error:
    (?:rlctAtOn (dlnLoss)
    ^
error: unclosed group

exec
/bin/bash -lc 'rg "rlctAtOn.*dlnLoss" -n lean/DLNFibre -g"*.lean"' in /tmp/p44-scope
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/Foundations/S1NodeCoverBridge.lean:8:descending to the child's box — NOT a point-RLCT. The clean point-min `rlctAtOn (dlnLoss M 0) 0 =
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:107:`rlctAtOn_comp_homeomorph`. Given the loss-identity `dlnLoss H222 0 = myF ∘ e222` (the consumer
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:110:(`e222_deepest`), giving `rlctAtOn (dlnLoss H222 0) deepest222 = rlctAtOn myF 0`. -/
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:153:theorem rlctAtOn_dlnLoss222_transport (myF : (Fin 8 → ℝ) → ℝ)
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean:155:    rlctAtOn (dlnLoss H222 0) deepest222 = rlctAtOn myF 0 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:7:`rlctAtOn (dlnLoss M 0) (chart (0,0)) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` from a measure-preserving
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:42:the chart image `χ (0,0)` splits: `rlctAtOn (dlnLoss M 0) (χ (0,0)) = nReg/2 + rlctAtOn (G²) 0`. Composes
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:43:`rlctAtOn_comp_homeomorph` (transport `dlnLoss` to the chart source) with `schur_recursion_step_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:57:    rlctAtOn (dlnLoss M 0) (chart (0, 0))
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:59:  -- transport `dlnLoss M 0` to the chart source: `rlctAtOn (dlnLoss M 0) (χ (0,0)) = rlctAtOn (dlnLoss ∘ χ) (0,0)`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:60:  rw [← rlctAtOn_comp_homeomorph chart hmp hemb (dlnLoss M 0) (0, 0)]
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:70:`rlctAtOn (dlnLoss M 0) (χ (0,0)) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`. Composes
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:72:`ReducedTransport.descent` (`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`); the two legs share the SAME
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:90:    rlctAtOn (dlnLoss M 0) (chart (0, 0))
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:91:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:61:reduced singular core RLCT `rlctAtOn (dlnLoss M 0) 0`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:392:    refine rlctAtOn_squeeze (fun x => dlnLoss H B ((paramsEquivFlat H).symm x)) Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:909:      refine rlctAtOn_squeeze (fun x => dlnLoss H B ((paramsEquivFlat H).symm x)) Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1032:`nReg/2 + rlctAtOn (dlnLoss M 0) 0` — the CORE RLCT, NOT its closed form. The Skeleton's
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1034:gap is exactly the **R1 core-value** `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1042:R1 core-value `hcore : rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's lane) and the
lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean:11:`hloss` hypothesis of `rlctAtOn_dlnLoss222_transport`.
lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean:49:the `hloss` hypothesis of `rlctAtOn_dlnLoss222_transport`, closing the seam end-to-end. Via
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:23:    `nReg/2 + rlctAtOn R t0 ≤ rlctAt (dlnLoss H B) v`, with `F`, `R` built from `q` (no bare
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:47:    (m : ℝ≥0∞)/2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v.
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:40:`descentStep : rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss (1,1,2) 0) 0 = 2/2 + rlctAtOn(child)`.
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:44:file does NOT prove `rlctAtOn flatCore (0,0) = rlctAtOn (dlnLoss H222 0) deepest222` (that is exactly the
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:312:      = (2 : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss (schurState M222route M222_hlo).red 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:321:identification: this proves `rlctAtOn flatCore222 (0,0) = 3/2`, not `rlctAtOn (dlnLoss H222 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:326:    (hred : rlctAtOn (dlnLoss (schurState M222route M222_hlo).red 0)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:12:the **reduced singular core** `rlctAtOn (dlnLoss M 0) 0` on the reduced widths `M = H−r`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:15:`rlctAtOn (dlnLoss M 0) 0`, the core RLCT at its deepest point — NOT on the closed form
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:16:`ofReal(lambdaCore M)`. Folding the core value `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` is
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:316:    refine rlctAtOn_squeeze (fun x => dlnLoss H B ((paramsEquivFlat H).symm x)) Φ wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:360:`rlctAt (dlnLoss H B) deepest = rlctAtOn Φ wstar`, where `Φ = ∑ regular² + dlnLoss M 0 (core)` and
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:382:coordinates has the same RLCT as on `Params M`: `rlctAtOn (dlnLoss M 0 ∘ (paramsEquivFlat M).symm) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:383:= rlctAtOn (dlnLoss M 0) (fun _ => 0)`. Transport along the measure-preserving flattening
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:390:      = rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:421:core)` has RLCT `nReg/2 + rlctAtOn (dlnLoss M 0) 0`: the `nReg` nondegenerate quadratic directions
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:424:and the reduced block's RLCT is `rlctAtOn (dlnLoss M 0) 0` (sub-7).
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:518:singular **core RLCT** `rlctAtOn (dlnLoss M 0) 0` on the reduced widths `M = H−r`. This is the gauge
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:519:chart's full content: it carries NO `lambdaCore` (R1's value `rlctAtOn (dlnLoss M 0) 0 =
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:28:**Scope: core-only** (`rlctAtOn(dlnLoss M 0) 0`, `M = H − r`). The regular `[−r²+r(H⁰+Hᴸ)]/2` shift is
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:11:    nReg/2 + rlctAtOn(core)(deepest-core) ≤ rlctAt (dlnLoss H B) v   (at a general optimal `v`)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:64:delivers `(★)`'s `hAtV` side: `nReg/2 + rlctAtOn R t0 ≤ rlctAt (dlnLoss H B) v`, with
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:89:    (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:118:  have hAtV : (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescentBuild.lean:88:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:447:anchored at the deepest point, then `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss (redChain t M) 0) redZero`. The
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:456:    rlctAtOn (fun y => G y ^ 2) (0 : Y) = rlctAtOn (dlnLoss (redChain t M) 0) redZero := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:459:  rw [hpull, rlctAtOn_comp_homeomorph redEmbed hmp hemb (dlnLoss (redChain t M) 0) 0, hzero]
lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:340:The two `⊤`s the oscillation conflated are DIFFERENT objects: (i) the GEOMETRIC `rlctAtOn (dlnLoss M 0) = ⊤`
lean/DLNFibre/DLN/RLCT/Validate/RRR.lean:121:    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:8:RECURSION route to `rlctAtOn (dlnLoss M 0) 0 = ofReal (lambdaCore M)` (`= ½·minAdm`), iterating the
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:16:- `hstep` (O1, the NON-degenerate-child step): `rlctAtOn (dlnLoss M 0) 0 = ofReal (nReg M / 2) +
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:17:  rlctAtOn (dlnLoss (redOf M) 0) 0`. Sound only when the child `redOf M` is non-degenerate (the
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:20:  `dlnLoss (redOf M) ≡ 0`, geometric `rlctAtOn = ⊤`), DON'T recurse — `rlctAtOn (dlnLoss M 0) 0 =
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:44:state contributing `0`), the binding R1 core identity holds: `rlctAtOn (dlnLoss M 0) 0 = ofReal
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:86:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0` at the child's deepest point. `Y` is the post-blow-up
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:109:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) (fun _ => 0)`. Consumes crux2's banked
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:115:      = rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:249:    --   • `rlctAtOn_layerReduced_transport` — the descent cert generalised to `dlnLoss (redChain t M)`.
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:14:- the measure-preserving transport `rlctAtOn (dlnLoss H222 0) deepest222 = rlctAtOn myF222 0`
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:15:  (`rlctAtOn_dlnLoss222_transport`, `ParamsFlat222`).
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:26:/-- **The `(2,2,2)` core RLCT (on `Params`).** `rlctAtOn (dlnLoss H222 0) deepest222 = 3/2`: the
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:28:(`rlctAtOn_dlnLoss222_transport`) carry the cover value (`rlctAtOn_myF222_eq`) from `Fin 8 → ℝ` to the
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:30:theorem case222_rlctAtOn_eq : rlctAtOn (dlnLoss H222 0) deepest222 = 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:31:  rw [rlctAtOn_dlnLoss222_transport myF222 dlnLoss222_eq_myF222, rlctAtOn_myF222_eq]
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:41:`resolution_charts` (core form): `rlctAtOn (dlnLoss M 0) deepest = ⨅ monomialThreshold (d i)(k i)(h i)`.
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:70:`rlctOf := fun M => rlctAtOn (dlnLoss M 0) (deepest)`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMNReg.lean:10:(`schur_node_loss_presentation`). The per-node RLCT splits `nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMCover.lean:24:`dlnLoss H222 0` RLCT statement requires transporting across `e222` (`rlctAtOn_dlnLoss222_transport`,
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:144:    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:205:    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:18:SOUNDNESS NOTE (the (C2) finding): the *clean* `rlctAtOn(dlnLoss M 0) 0 = nReg/2 + rlctAtOn(Mred) 0`
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:206:The clean `rlctAtOn(dlnLoss M 0) 0 = nReg/2 + rlctAtOn(dlnLoss Mred 0) 0` (no chart hypothesis) is
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:334:`rlctAtOn (dlnLoss M 0) (χ 0) = nReg/2 + rlctAtOn (G²) 0`. Transport (`rlctAtOn_comp_homeomorph`,
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:351:    rlctAtOn (dlnLoss M 0) (chart (0, 0))
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:353:  rw [← rlctAtOn_comp_homeomorph chart hmp hemb (dlnLoss M 0) (0, 0)]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:644:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) …`. This supplies the transport: if `redEmbed` is a
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:646:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) redZero` (`rlctAtOn_comp_homeomorph`). The basepoint
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:655:    rlctAtOn (fun y => G y ^ 2) (0 : Y) = rlctAtOn (dlnLoss S.red 0) redZero := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:658:  rw [hpull, rlctAtOn_comp_homeomorph redEmbed hmp hemb (dlnLoss S.red 0) 0, hzero]
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:373:    have htrans := rlctAtOn_comp_homeomorph τ hmp hemb (dlnLoss H Bp) w
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:322:    rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last 2))) ℝ) A)
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotRowWLOG.lean:306:    have htrans := rlctAtOn_comp_homeomorph τ hmp hemb (dlnLoss H Bp) w
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:165:  have hstep1 := rlctAtOn_comp_homeomorph p.symm hpmp hpemb (dlnLoss H B) c
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:176:  have hstep2 := rlctAtOn_comp_homeomorph τ hτmp hτemb (fun x => dlnLoss H B (p.symm x)) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:17:  `rlctAt H (dlnLoss H B) deepestPoint = nReg/2 + rlctAtOn(dlnLoss M 0) 0` (core RLCT, NOT `lambdaCore`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:20:- **`hRValue`** — R1's value `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)` (= `resolution_charts`
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:40:(`rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`), the local RLCT at the deepest point IS the
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:13:`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`; it makes NO codim claim. When G-b's
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:25:- `ReducedTransport S Y` — the det-1 MP reindex closing `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:27:Composed: `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` — the per-node DESCENT STEP that
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:59:ONLY: `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` must NOT be iterated INTO a
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:72:  /-- The det-1 MP descent transport (closes `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`); its `G` is
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:84:`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0)`. Composes the banked
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:86:`ReducedTransport.descent` (`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`). The two legs share the SAME
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:94:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:121:(`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`) and recurses on `S.red` (the
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:128:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:18:this transports it to the genuine `rlctAtOn (dlnLoss M 0) (fun _ => 0)` at the deepest point, via the
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:21:`rlctAtOn_dlnLoss222_transport` (ParamsFlat222, the (2,2,2) seam).
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:100:deepest point: `rlctAtOn (routeMCore M) 0 = rlctAtOn (dlnLoss M 0) (fun _ => 0)`. Via
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:102:zero-preserving `paramsEquivFlat_deepest`. The general-M analog of `rlctAtOn_dlnLoss222_transport`; this is
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:104:`rlctAtOn (dlnLoss M 0) (deepest)`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:107:      = rlctAtOn (dlnLoss M 0) (fun _ => 0 : Params M) := by
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:32:cover computes; the seam (`rlctAtOn_dlnLoss222_transport`) identifies `dlnLoss H222 0 = myF222 ∘ e222`.
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:9:The `(2,2,2)` value `rlctAtOn (dlnLoss H222 0) deepest222 = 3/2` routed through the **general**
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:25:* `rlctAtOn_dlnLoss222_transport` (the `e222` measure-preserving reindex, via `dlnLoss222_eq_myF222`)
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:58:/-- **The `(2,2,2)` R1 leg through the general engine** (the milestone). `rlctAtOn (dlnLoss H222 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:60:transport the loss to `myF222` (`rlctAtOn_dlnLoss222_transport` + `dlnLoss222_eq_myF222`), then read
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:65:    rlctAtOn (dlnLoss H222 0) deepest222 = 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:66:  rw [rlctAtOn_dlnLoss222_transport myF222 dlnLoss222_eq_myF222, rlctAtOn_myF222_eq_routeM]

exec
/bin/bash -lc "sed -n '1,200p' lean/DLNFibre/DLN/RLCT/Skeleton.lean" in /tmp/p44-scope
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.Lambda
import DLNFibre.DLN.RLCT.Foundations.S1Transport
import DLNFibre.DLN.RLCT.Foundations.S1Local
import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import DLNFibre.DLN.RLCT.BGEngine
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.GetD

/-!
# `DLNFibre.DLN.RLCT.Skeleton` — the goal skeleton (the contract)

The single cited `axiom` (S2, the monomial-integral extraction), every named-`sorry` rung
statement (S1 / L1 / L2 / D1 / R1 / A1 / A2), and the headline `aoyagi_learning_coefficient`
(design-spec §8).

**Statements-first.** Each rung below is a named `sorry` with the statement it must eventually
prove; a `sorry` under a correct statement is a building block. The sorry-count trends down as
rungs close. The headline is *assembled* from the named pieces so its statement type-checks.

## The one citation (S2) — and where the line is drawn
Per controller standing decision 2 and the decorrelated Codex audit (`codex/s2-axiom-answer.md`),
the cited content is **only** the irreducible monomial-integral fact: the RLCT threshold and pole
order of a **weighted monomial integral** `∫ (∏ uⱼ^{hⱼ}) · (∏ uⱼ^{2kⱼ})^{−c} du`. Everything else
stays on our side:
- the **cover** and **change-of-variables** validity → S1;
- the **resolution charts** producing the `(k, h)` data → R1;
- the reduction of `rlctAt (dlnLoss)` to a min over charts of these monomial thresholds →
  a *derived theorem* (proven later from S1 + R1 + S2), **not** an axiom.

So the chart-level formula is a theorem, not a citation; the axiom is the bare monomial fact.
(Codex's recommendation #5 and the brief's standing decision 2 coincide here.)
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory ENNReal Topology

variable {L : ℕ}

/-! ## Monomial-model objects (the S2 substrate) -/

/-- The per-axis ratio `(hⱼ+1)/(2kⱼ)` in `ℝ≥0∞`; `kⱼ = 0` gives `⊤` (that axis never binds the
minimum — the function is a unit in that direction). Division is in `ℝ≥0∞` (in `ℝ`, `a/0 = 0`
would be wrong here). -/
noncomputable def axisRatio (h k : ℕ) : ℝ≥0∞ := ((h : ℝ≥0∞) + 1) / (2 * (k : ℝ≥0∞))

/-- **R1.2a (regular-sequence divisor ratio).** A binding divisor over a codim-`c` stratum has
`(k, h) = (1, c−1)` (k=1 from order-2 vanishing of a real sum-of-squares; `h=c−1` from the smooth
codim-`c` blow-up Jacobian), ratio `c/2`. The upper-bound seed (binding divisor on the minimizing
stratum realises `½·Mval(t)`). -/
theorem axisRatio_regularSeq (c : ℕ) (hc : 1 ≤ c) : axisRatio (c - 1) 1 = (c : ℝ≥0∞) / 2 := by
  unfold axisRatio
  rw [Nat.cast_one, mul_one]
  congr 1
  have : ((c - 1 : ℕ) : ℝ≥0∞) + 1 = ((c - 1 + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring
  rw [this, Nat.sub_add_cancel hc]

/-- **R1.2b (multiplicity control — the lower-bound inequality).** Any divisor with `m·k ≤ h+1` has
ratio `≥ m/2`. With `m = min_t Mval` and our core's regular-sequence `k=1, h=c−1` (so `m·k = m ≤ c =
h+1`), every divisor ratio is `≥ ½·min_t Mval` — the lower-bound mechanism (the regular sequence,
not codim, is why `rlct = ½·codim` here; `xᵏ`/`(x²+y²)²` show the bare codim bound is false). -/
theorem axisRatio_ge_of_mult (h k m : ℕ) (hk : 1 ≤ k) (hmult : m * k ≤ h + 1) :
    (m : ℝ≥0∞) / 2 ≤ axisRatio h k := by
  unfold axisRatio
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hstep : (m : ℝ≥0∞) / 2 = ((m : ℝ≥0∞) * k) / (2 * k) := by
    rw [mul_comm (2 : ℝ≥0∞) (k : ℝ≥0∞), ← ENNReal.mul_div_mul_right (m : ℝ≥0∞) 2 hk0 (by simp)]
    ring_nf
  rw [hstep]
  apply ENNReal.div_le_div_right
  calc (m : ℝ≥0∞) * k = ((m * k : ℕ) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((h + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast hmult
    _ = (h : ℝ≥0∞) + 1 := by push_cast; ring

/-- The weighted monomial integrand: density `∏ uⱼ^{hⱼ}` (the pulled-back Jacobian × bump) against
the monomial `∏ uⱼ^{2kⱼ}` (the resolved function) raised to `−c`. The object whose threshold S2
cites. -/
noncomputable def monomialIntegrand (d : ℕ) (k h : Fin d → ℕ) (c : ℝ) (u : Fin d → ℝ) : ℝ :=
  (∏ j, |u j| ^ (h j)) * (∏ j, |u j| ^ (2 * k j)) ^ (-c)

/-- The unit box `[0,1]^d` (a compact chart neighbourhood of the origin). -/
def unitBox (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)

/-- The RLCT threshold of the weighted monomial integral: `sSup` of the down-set of exponents
`c' ≥ 0` for which the integrand is integrable on the box. -/
noncomputable def monomialThreshold (d : ℕ) (k h : Fin d → ℕ) : ℝ≥0∞ :=
  sSup { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧
          IntegrableOn (monomialIntegrand d k h (c' : ℝ)) (unitBox d) volume }

/-- The combinatorial pole order of the weighted monomial integral: the number of axes attaining the
minimal ratio (the binding-factor multiplicity). -/
noncomputable def monomialOrder (d : ℕ) (k h : Fin d → ℕ) : ℕ :=
  (Finset.univ.filter
    (fun j : Fin d => axisRatio (h j) (k j) = ⨅ j' : Fin d, axisRatio (h j') (k j'))).card

/-- The *analytic* pole order of the weighted monomial integral (the multiplicity of the largest
pole of its zeta function). Opaque placeholder — like `rlctOrderAt`, the direct analytic definition
needs meromorphic continuation Mathlib lacks; its value is pinned by the S2 citation below. -/
opaque monomialOrderAnalytic (d : ℕ) (k h : Fin d → ℕ) : ℕ

/-! ## S2 — THE ONE CITED AXIOM (Aoyagi p.6 / Hironaka; design-spec §7.1) -/

/-- **S2 (cited).** The normal-crossing extraction of the RLCT value and pole order for a weighted
monomial integral. The threshold of `∫ (∏ uⱼ^{hⱼ}) (∏ uⱼ^{2kⱼ})^{−c}` is `min_j (h_j+1)/(2k_j)`,
and — **in the singular case `∃ j, kⱼ ≠ 0`** — the analytic pole order equals the number of axes
attaining that minimum (per axis: `∫₀^ε u^{h−2kc} du < ∞ ⟺ c < (h+1)/(2k)`; the order is the
binding-factor multiplicity). This is the **single permitted external citation** (Watanabe; Hironaka
resolution). The cover, change-of-variables, properness, and bump-independence are **not** cited —
they are proven on our side (S1, R1). The order half is the genuine analytic content (the
meromorphic pole-order computation for a product of one-variable factors; Codex audit §4), which is
why it equates the opaque `monomialOrderAnalytic` to the combinatorial `monomialOrder`.

The order-half is **scoped to `∃ j, kⱼ ≠ 0`** (Rung-0c FLAG 1): when all `kⱼ = 0` the integrand is a
unit (`F ≢ 0` at the point — the non-singular `F(w*)≠0` chart), every `axisRatio = ⊤` ties, and the
unconditional `monomialOrder = d` would be a stray claim about a regular point's pole order. The
threshold-half is correct in that degenerate case too (`⨅ ⊤ = ⊤`, the locally-nonvanishing RLCT),
so it stays unconditional; only the order-conjunct carries the singularity hypothesis. -/
axiom monomial_rlct (d : ℕ) (k h : Fin d → ℕ) :
    monomialThreshold d k h = (⨅ j : Fin d, axisRatio (h j) (k j))
    ∧ ((∃ j : Fin d, k j ≠ 0) → monomialOrderAnalytic d k h = monomialOrder d k h)

/-! ### R1.2 threshold-level divisor arithmetic (the lower/upper bracket; shape-independent).
The per-axis seeds `axisRatio_regularSeq` / `axisRatio_ge_of_mult` lift through S2's threshold value
`monomialThreshold = ⨅ axisRatio` to the chart threshold. These bracket a chart's threshold and are
the arithmetic the R1 value-match assembly consumes: the lower bound (every divisor obeys the
multiplicity bound ⟹ threshold `≥ m/2`) and the upper bound (one binding divisor realises `c/2`). -/

/-- **R1.2 lower bound (multiplicity control at the threshold).** If every axis obeys the
multiplicity bound `m·kⱼ ≤ hⱼ+1` (regular sequence: `kⱼ=1` ⟹ `m ≤ hⱼ+1`), the chart threshold is
`≥ m/2`. Lifts `axisRatio_ge_of_mult` over the axes via S2 (`monomial_rlct.1` + `le_iInf`). With
`m = min_t Mval` this is the per-chart half of `min over charts ≥ ½·min_t Mval`. -/
theorem monomialThreshold_ge_of_mult (d : ℕ) (k h : Fin d → ℕ) (m : ℕ)
    (hk : ∀ j, 1 ≤ k j) (hmult : ∀ j, m * k j ≤ h j + 1) :
    (m : ℝ≥0∞) / 2 ≤ monomialThreshold d k h := by
  rw [(monomial_rlct d k h).1]
  exact le_iInf (fun j => axisRatio_ge_of_mult (h j) (k j) m (hk j) (hmult j))

/-- **R1.2 upper bound (one axis bounds the threshold).** A single axis's ratio bounds the chart
threshold above (`monomial_rlct.1` + `iInf_le`): the binding-divisor seed. -/
theorem monomialThreshold_le_axis (d : ℕ) (k h : Fin d → ℕ) (j : Fin d) :
    monomialThreshold d k h ≤ axisRatio (h j) (k j) := by
  rw [(monomial_rlct d k h).1]; exact iInf_le _ j

/-- **R1.2 binding divisor (upper bound `c/2`).** A regular-sequence binding axis `(kⱼ,hⱼ)=(1,c−1)`
makes the chart threshold `≤ c/2` (the binding divisor over a codim-`c` stratum realises `½·c`).
With `c = Mval(t)` at the minimizing stratum this is the upper half of the value-match. -/
theorem monomialThreshold_le_regularSeq (d : ℕ) (k h : Fin d → ℕ) (c : ℕ) (hc : 1 ≤ c) (j : Fin d)
    (hkj : k j = 1) (hhj : h j = c - 1) :
    monomialThreshold d k h ≤ (c : ℝ≥0∞) / 2 := by
  refine (monomialThreshold_le_axis d k h j).trans ?_
  rw [hkj, hhj, axisRatio_regularSeq c hc]

/-! ## S1 — RLCT invariance substrate (thread 05; design-spec §8)

The shared analytic linchpin, in the `weightedThreshold` abstraction (`Foundations/Rlct.lean`):
**S1.1** weighted-threshold TRANSPORT (the heavy core), then the corollaries **S1.2** monotonicity,
**S1.3** ideal-invariance / germ-locality (the encoded `rlct_unit_invariant` + `rlct_germ_local`),
**S1.4** Σ_X-elimination + φ-independence, and **S1.5** disjoint-block additivity (the engine of the
L2 regular/core split). -/

/-- **S1.1 (the linchpin — weighted-threshold transport; thread 05).** Transport of the weighted
RLCT threshold along a **proper, a.e.-analytic diffeo** `π` on a finite-dim real space: off a null
set `E`, `π` is injective and differentiable with derivative `Dπ`, and `π` is proper. Then
`θ(F, φ; {w*})` equals `θ(F∘π, (φ∘π)·|det Dπ|; π⁻¹{w*})` — the **Jacobian weight `|det Dπ|` is
MANDATORY** (Codex-caught, pp-verified: the *unweighted* `rlctAt(F∘π)=rlctAt(F)` is FALSE — e.g.
`F=x²+y²`, chart `(u,uv)` gives `1/2 ≠ 1`, the missing factor being exactly `|det Dπ|=|u|`). Proof
route (the heaviest analytic lemma below R1): delete `E`, apply Mathlib's Jacobian
change-of-variables on the diffeo part (`integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`),
restore the null set, then properness gives that every nbhd of `w*` pulls back to one of `π⁻¹{w*}`
(fixed-set ↔ local-nbhd integrability). D1 takes the single-map form; R1 per-chart + finite `min`.

Rung-0c FLAG (measure pin): the unconstrained `[MeasureSpace M]` made the bare statement **FALSE**
(Codex: on `ℝ` with weight `|x| dx`, `π = x³` gives `2 ≠ 4/3`) — the Jacobian-change-of-variables
the proof route needs holds for the **additive Haar / Lebesgue** measure, not an arbitrary one.
Pinned via `[(volume : Measure M).IsAddHaarMeasure]`; `MeasurableSet E` added (with `volume E = 0`,
the proof's null-set deletion + the Luzin-N image `π(E)` null are then available). The
Jacobian-weight placement was already correct, kept. Non-vacuous: equates two thresholds. -/
theorem weightedThreshold_transport
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M]
    [FiniteDimensional ℝ M] [(volume : Measure M).IsAddHaarMeasure]
    (F φ : M → ℝ) (wstar : M)
    (π : M → M) (Dπ : M → (M →L[ℝ] M)) (E : Set M)
    (hproper : IsProperMap π)
    (hE_meas : MeasurableSet E)
    (hE_null : volume E = 0)
    (hinj : Set.InjOn π Eᶜ)
    (hderiv : ∀ m ∈ Eᶜ, HasFDerivAt π (Dπ m) m)
    (hsurj : Function.Surjective π)
    (hImE : volume (π '' E) = 0) :
    weightedThreshold F φ {wstar}
      = weightedThreshold (F ∘ π) (fun m => φ (π m) * |(Dπ m).det|) (π ⁻¹' {wstar}) :=
  weightedThreshold_transport_aux F φ wstar π Dπ E hproper hE_meas hE_null hinj hderiv hsurj hImE

/-- **S1.3 (Lemma 1, ideal invariance core).** The RLCT is invariant under multiplying `F` by a unit
`u` (measurable, bounded `0 < a ≤ |u| ≤ b` near `w*`) — the operative "depends only on the ideal"
content (reduces `λ(⟨Fᵢ⟩)` to `λ(∑Fᵢ²)`, removes the bump and `Σ_X`). `Measurable u` is the
11th-finding fidelity fix (the integrand pushforward needs it). Wired to `rlct_unit_invariant_aux`
(`Foundations/S1Local`). Non-vacuous: equates the RLCT of `u·F` to that of `F`. -/

exec
/bin/bash -lc "sed -n '1,240p' lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean" in /tmp/p44-scope
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.D1ChartProducerL2Build
import DLNFibre.DLN.RLCT.Foundations.S1IFTProducer

/-!
# `DLNFibre.DLN.RLCT.Validate.D1IFTResidualProducer` — the D1 producer fed by a `C¹` residual

The §SEL selected-minor IFT-chart producer, WIRED. The banked reductions
`deepest_le_of_optimal_chart` (`D1ChartProducer`) and `deepest_le_of_optimal_middle_stratum`
(`D1ChartProducerL2Build`) consume the post-chart sum-of-squares form `F = ∑s² + Q` with the
constant comparison `hcmp` as **bare hypotheses**. This module DISCHARGES those from the
genuinely-lighter premise the §SEL route identified: the residual is a `C¹` sum of squares
`Q = ‖q‖²`. The network-free producer `rlctAtOn_quasiSplit_ge_of_contDiff_residual`
(`Foundations.S1IFTProducer`) builds `hF`, `hQ0`, `hR` (definitional) and `hcmp` (the §SEL
vector-triangle mean-value bound) from `q`'s smoothness, so the only chart fact left hypothesized is
the bounded-unit chart TRANSFER `hchart : rlctAt (dlnLoss H B) v = rlctAtOn F (0,t0)` (the banked
`rlctAtOn_boundedUnit_localHomeomorph` applied to the actual `Params H → flat` IFT chart at `v` —
the Altitude-B DLN-specific wiring, NOT a quadratic-split / Morse-Bott lemma).

## What it lands

  * **`rlctAt_ge_nReg_add_slice_of_residual`** — the `hAtV` half from a `C¹` first-peel residual:
    the chart transfer `hchart` + `q` `C¹` + the slice a.e.-nonzero ⟹
    `nReg/2 + rlctAtOn R t0 ≤ rlctAt (dlnLoss H B) v`, with `F`, `R` built from `q` (no bare
    `hF`/`hQ0`/`hcmp`).
  * **`deepest_le_of_optimal_of_iftResidual`** — the full D1 per-point `≥` at a middle-stratum
    optimal `v`, wired through BOTH peels: the first-peel residual `q` (this module) feeds the
    `hAtV` half, and the second-peel residual `q₂` + the §5 R1-resolution interface feed the
    case-(B) `hCore` (`hCore_middle_stratum_of_interface`). All chart data is CONSTRUCTED from the
    two `C¹` residuals; only `hchart`/`hchart₂` (the two `rlctAtOn`-equality transfers), `hDeepest`
    (#44), and `hDegraded` (the R1 interface) remain hypotheses.

Scope L = 2 (general-L = wall #120). The chart-transfer `hchart` and the deepest `hDeepest` stay the
tracked Skeleton obligations; this module removes the chart-DATA (`hF`/`hQ0`/`hcmp`) from the
hypothesis list, replacing them with the single `C¹`-residual premise the §SEL route certified.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **The `hAtV` half from a `C¹` first-peel residual** (the §SEL producer wired). At a general
optimal `v` at L = 2, given the bounded-unit chart transfer `hchart` to the post-chart loss
`F (s,t) = (∑ s²) + ‖q (s,t)‖²` (`q` the `C¹` inactive-residual vector on the flat slice
`(Fin m → ℝ) × Y`), with the slice residual `R t = ‖q (0,t)‖²` a.e.-nonzero near `t0`, the engine
gives the `hAtV` shape:

    (m : ℝ≥0∞)/2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v.

`hF`/`hQ0`/`hR`/`hcmp` are NOT hypotheses here — they are built from `q`'s smoothness by the
network-free `rlctAtOn_quasiSplit_ge_of_contDiff_residual`. (The regular-block count `m` is FREE in
this statement; the `nReg` in the name is the use-site instantiation `m = nRegL2 H r` — the name
parallels the banked `rlctAt_ge_nReg_add_slice` it generalizes off the bare chart data.) -/
theorem rlctAt_ge_nReg_add_slice_of_residual {L m n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y] [BorelSpace Y]
    [FiniteDimensional ℝ Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    (H : Fin (L + 1) → ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H)
    (q : (Fin m → ℝ) × Y → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 1 q) (t0 : Y)
    (hchart : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin m → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2))
            ((0 : Fin m → ℝ), t0))
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, q ((0 : Fin m → ℝ), z) i ^ 2) ≠ 0) :
    (m : ℝ≥0∞) / 2 + rlctAtOn (fun t : Y => ∑ i, q ((0 : Fin m → ℝ), t) i ^ 2) t0
      ≤ rlctAt H (dlnLoss H B) v := by
  rw [hchart]
  exact rlctAtOn_quasiSplit_ge_of_contDiff_residual q hq t0 hRne

/-- **The full D1 per-point `≥` from two `C¹` residuals** (the §SEL producer wired through both
peels). At a middle-stratum optimal `v` (square deepest reduced widths `(m,m,m)`,
`coreDeepest = ofReal(lambdaCore (square m))`, `a + b ≤ m`):

  * the FIRST-peel `C¹` residual `q` (on `(Fin nReg → ℝ) × Y`) + the chart transfer `hchart` give
    the `nReg`-block `hAtV` half (`rlctAt_ge_nReg_add_slice_of_residual` content, inlined via the
    engine);
  * the SECOND-peel `C¹` residual `q₂` (on `(Fin extra → ℝ) × Y₂`) + its chart transfer `hchart₂` +
    the §5 R1-resolution interface `hDegraded` discharge the case-(B) `hCore` via
    `hCore_middle_stratum_of_interface`;

and the deepest-side `#44` equality `hDeepest` closes `rlctAt deepest ≤ rlctAt v`. ALL chart DATA
(`hF`/`hQ0`/`hR`/`hcmp` for both peels) is CONSTRUCTED from `q`, `q₂` smoothness; only the two
`rlctAtOn`-equality transfers, `hDeepest`, and the R1 interface stay hypotheses.
`nReg = nRegL2 H r`, `extra = extraCount m a b`. -/
theorem deepest_le_of_optimal_of_iftResidual {n n₂ : ℕ}
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y] [BorelSpace Y]
    [FiniteDimensional ℝ Y] [ProperSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    {Y₂ : Type*} [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] [MeasureSpace Y₂] [BorelSpace Y₂]
    [FiniteDimensional ℝ Y₂] [ProperSpace Y₂] [IsFiniteMeasureOnCompacts (volume : Measure Y₂)]
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (deepest v : Params H) (m a b : ℕ) (hab : a + b ≤ m) (coreDeepest : ℝ≥0∞)
    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
    (hDeepest : rlctAt H (dlnLoss H B) deepest = (nRegL2 H r : ℝ≥0∞) / 2 + coreDeepest)
    -- FIRST-peel `C¹` residual + chart transfer
    (q : (Fin (nRegL2 H r) → ℝ) × Y → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 1 q) (t0 : Y)
    (hchart : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2))
            ((0 : Fin (nRegL2 H r) → ℝ), t0))
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), z) i ^ 2) ≠ 0)
    -- SECOND-peel `C¹` residual + chart transfer + the §5 interface
    (q₂ : (Fin (extraCount m a b) → ℝ) × Y₂ → EuclideanSpace ℝ (Fin n₂)) (hq₂ : ContDiff ℝ 1 q₂)
    (t0₂ : Y₂)
    (hchart₂ : rlctAtOn (fun t : Y => ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
        = rlctAtOn (fun p : (Fin (extraCount m a b) → ℝ) × Y₂ =>
            (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2))
            ((0 : Fin (extraCount m a b) → ℝ), t0₂))
    (hR₂ne : ∃ U ∈ 𝓝 t0₂, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), z) i ^ 2) ≠ 0)
    (hDegraded : rlctAtOn (fun t : Y₂ => ∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), t) i ^ 2) t0₂
        = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
    rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
  -- the FIRST-peel post-chart loss / slice residual (built from `q`)
  set F : (Fin (nRegL2 H r) → ℝ) × Y → ℝ :=
    fun p => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2) with hFdef
  set Q : (Fin (nRegL2 H r) → ℝ) × Y → ℝ := fun p => ∑ i, q p i ^ 2 with hQdef
  set R : Y → ℝ := fun t => ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2 with hRdef
  -- the SECOND-peel post-chart loss / slice residual (built from `q₂`)
  set F₂ : (Fin (extraCount m a b) → ℝ) × Y₂ → ℝ :=
    fun p => (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2) with hF₂def
  set Q₂ : (Fin (extraCount m a b) → ℝ) × Y₂ → ℝ := fun p => ∑ i, q₂ p i ^ 2 with hQ₂def
  set R₂ : Y₂ → ℝ := fun t => ∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), t) i ^ 2 with hR₂def
  -- measurability of `F`, `R` (continuity of the sum-of-squares of `C¹` coords)
  have hqcont : Continuous q := hq.continuous
  have hqi : ∀ i, Continuous fun p : (Fin (nRegL2 H r) → ℝ) × Y => q p i := fun i =>
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous).comp hqcont
  have hFmeas : Measurable F := by
    have hcont : Continuous F := by
      refine Continuous.add (continuous_finset_sum _
        (fun i _ => ((continuous_apply i).comp continuous_fst).pow 2))
        (continuous_finset_sum _ (fun i _ => (hqi i).pow 2))
    exact hcont.measurable
  have hRmeas : Measurable R := by
    have hcont : Continuous R := continuous_finset_sum _ (fun i _ =>
      ((hqi i).comp (Continuous.prodMk continuous_const continuous_id)).pow 2)
    exact hcont.measurable
  -- the FIRST-peel `hcmp` (the §SEL vector triangle from `q`'s smoothness)
  obtain ⟨C, hC, hcmp⟩ := hcmp_of_contDiff q hq t0
  -- the SECOND-peel measurability + `hcmp`
  have hq₂cont : Continuous q₂ := hq₂.continuous
  have hq₂i : ∀ i, Continuous fun p : (Fin (extraCount m a b) → ℝ) × Y₂ => q₂ p i := fun i =>
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous).comp hq₂cont
  have hF₂meas : Measurable F₂ := by
    have hcont : Continuous F₂ := by
      refine Continuous.add (continuous_finset_sum _
        (fun i _ => ((continuous_apply i).comp continuous_fst).pow 2))
        (continuous_finset_sum _ (fun i _ => (hq₂i i).pow 2))
    exact hcont.measurable
  have hR₂meas : Measurable R₂ := by
    have hcont : Continuous R₂ := continuous_finset_sum _ (fun i _ =>
      ((hq₂i i).comp (Continuous.prodMk continuous_const continuous_id)).pow 2)
    exact hcont.measurable
  obtain ⟨C₂, hC₂, hcmp₂⟩ := hcmp_of_contDiff q₂ hq₂ t0₂
  -- assemble through the banked two-peel reduction
  exact deepest_le_of_optimal_middle_stratum H r B deepest v m a b hab coreDeepest hcoreDeepest
    F Q R t0 hDeepest hchart (fun _ => rfl)
    (fun p => Finset.sum_nonneg fun i _ => sq_nonneg _) hFmeas (fun _ => rfl) hRmeas hRne C hC hcmp
    F₂ Q₂ R₂ t0₂ hchart₂ (fun _ => rfl)
    (fun p => Finset.sum_nonneg fun i _ => sq_nonneg _) hF₂meas (fun _ => rfl) hR₂meas hR₂ne
    C₂ hC₂ hcmp₂ hDegraded

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc "sed -n '1,240p' lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean" in /tmp/p44-scope
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.S1Spectator
import DLNFibre.DLN.RLCT.Foundations.S1NonMPTransport
import DLNFibre.DLN.RLCT.Foundations.LossContinuity

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart` — the L2 deepest-point gauge-slice normal form (#44)

The heavy geometric obligation of L2 (`product_reduction`): at the deepest point (every layer rank
exactly `r`), the local RLCT of `dlnLoss H B` splits as the **regular gauge shift** `nReg/2`
(`nReg = r(H⁰+Hᴸ−r)` nondegenerate gauge-orbit-transversal directions, Fubini-additive `S1.5`) plus
the **reduced singular core** `rlctAtOn (dlnLoss M 0) 0` on the reduced widths `M = H−r`.

This is the **VALUE-FREE** L2 reduction (`deepest_regular_core_reduces`): it lands on
`rlctAtOn (dlnLoss M 0) 0`, the core RLCT at its deepest point — NOT on the closed form
`ofReal(lambdaCore M)`. Folding the core value `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` is
**R1** (`resolution_charts` + A1), kept separate (the gauge chart carries no `lambdaCore`).

## The mechanism (pp-hall cert g150, decorrelated Codex; g147 skeleton)

At a deepest point `w0` with `IsDeepLayers H r B w0` (every layer rank exactly `r`), gauge-slice each
layer. By `block_elimination` there are units `P_s,Q_s` with `P_s (w0 s) Q_s = blockdiag[I_r,0]`; in
the gauge coords each layer is `C_s = [[I_r+X_s, Y_s],[Z_s, T_s]]`, the reduced block `T_s` of width
`M_s = H_s − r`. The product residuals `E = (∏C − blockdiag[I_r,0])` on the `(0,0),(0,1),(1,0)` blocks
are the `nReg` regular coords (Jacobian rank `= nReg` at the chain endpoints). **The reduced core is
the GAUGE-NORMALIZED chain `‖∏S_s‖² = dlnLoss M 0` (the `core` coords), NOT the raw `‖∏T_s‖²`**
(g150-fix → #61/g156: the additive Schur complement, Codex caught the raw-`T` error): the honest
reduced block is the Schur complement `S_s = T_s − Z_s(I+X_s)⁻¹Y_s` (an ADDITIVE shear of the core
slot — `coreAbsorb`; NOT the refuted multiplicative `T·(I−VY)⁻¹`). The raw-`∏T` form is FALSE for
matrices (the gauge unit `g` between blocks maps a `TS=0` direction to `TgS≠0`, ratio `→∞`). The `core`
slot of `split` carries the `S`-normalized chain — the structure is abstract over it; the
gauge-normalization is the chart's (cobuild-sub34's) obligation. The transport is the local SQUEEZE
(`rlctAtOn_squeeze`), not the
over-reaching global chart (sub-34 g152: the gauge slice is a LOCAL diffeo).

## Route status

ROUTE-FIRST: structure pinned (g147) + 7 sub-lemma signatures + the value-free assembly, all `sorry`.
The reachable sub-lemmas (1,2,5,6,7) route through green primitives; the heavy chart-existence
(sub-3,4) is the g150-cert-backed block algebra (#44c). The Skeleton `deepest_regular_core_normal_form`
discharge = this reduction `▸` the R1 core value (controller wires, single-writer for Skeleton).

## The producer contract (authoritative — the single source for `DeepestGaugeConstruction`)

The `deepest_gauge_squeeze_exists` producer (`DeepestGaugeConstruction.lean`, the #59 obligation)
consumes THIS structure. This block is the authoritative contract; read it instead of re-deriving the
interface. Canonical structure: `fm2/split-reindex` (post-`(C)`-refactor, #90).

**WHERE EACH PIECE OF THE GAUGE NONLINEARITY LIVES** (the recurring confusion — pin it once):
* `split` is a PURE measure-preserving RELABEL+translation (`deepestSplit_exists`, #64, DONE). Its reg
  slot `(split w).1` is a linear PROJECTION (the raw boundary pivots `X₁/Z₁/Y_L`), NOT the residuals
  `E`; its core slot `(split w).2.1` is the raw `T`-blocks; its spectator `(split w).2.2` is the
  interior gauge entries. The nReg COUNT is right (`r(H⁰+Hᴸ−r)`), the directions are raw — that is
  correct: split carries no gauge nonlinearity (det `±1`).
* `regStraighten : DeepestSplit → DeepestSplit` (a bare TOTAL continuous function post-`(C)`, NOT a
  `≃ₜ`) is the nonlinear `E`-straightening. It reads the WHOLE `q` (reg × core × spec — INCLUDING the
  spectator, where the interior `X₂` lives). **`(regStraighten q).1 = E_pivot`** (RULED 2026-06-23,
  controller): the core-INDEPENDENT, `dE(0) = id` straightened part — the genuine reg→reg local diffeo.
  The core-DEPENDENT cross-terms `E − E_pivot ∈ ideal(reg)` (cobuild sympy-verified `E|{reg=0} = 0`) are
  NOT coordinate — they are LOSS, and charge to PIN2's `∑E²` (cobuild's leak mechanism, `#54`). Rationale:
  a coordinate-straightening map must not depend on the core it is not straightening; `E_pivot` is the
  reg→reg diffeo, the residual is loss. `regStraighten_core`/`_spectator` fix only the OUTPUT core/spec
  slots; they do NOT restrict what the `.1`-OUTPUT reads. (`#82`, the producer's; total fn keeps
  global measurability — the `(C)` fallback.)
* `coreAbsorb : DeepestSplit ≃ₜ DeepestSplit` (`#79`, DONE) is the ADDITIVE Schur shear (det = 1, MP):
  `coreShearHomeo` with `shift = −Z(I+X)⁻¹Y` reading reg+spec, so `(coreAbsorb q).2.1` = the core-only
  per-layer Schur `∏S_s` (`S_s = T_s − Z_s(I+X_s)⁻¹Y_s`). The core-output is core-only `∏S_s`,
  TYPE-FORCED (`deepestCoreF` takes the core slot `Fin (flatDim M) → ℝ` ALONE — the full-product `R`,
  which depends on `E`, CANNOT be the core-output). NOT the refuted multiplicative `T·(I−VY)⁻¹`.
* `loss_squeeze` Φ = `∑ (regStraighten (split w)).1² + deepestCoreF (coreAbsorb (split w)).2.1`
  = `∑E² + ‖∏S_s‖²-core`. The full-product `R` (`= ∏S_s` only on `{E=0}`) is the LOSS-SIDE comparison
  object; its `R − ∏S_s` inter-layer discrepancy is the LEAK, charged to `∑E²` (`#54`
  `core_comparability_squeeze`), NOT a `coreAbsorb` component. There is NO inter-layer-unit peel.

**RLCT-PEEL ROUTES** (both via crux2's peels; NOT `weightedThreshold_weight_unit_invariant`):
* `coreAbsorb_rlct`: the MP route — `measurePreserving_coreShear` (`#83`) ⟹ `rlctAtOn_comp_homeomorph`
  (det = 1, no Jacobian). Done in `#79`.
* `regAbsorb_rlct`: the LOCAL route — `rlctAtOn_boundedUnit_localHomeomorph` (`#72`), which takes
  `regStraighten`/its local inverse as BARE FUNCTIONS + `Dπ` + an open `V ∋ 0` (inverses only on `V`).
  The `V`/`Dπ` data lives INSIDE the producer's proof, NOT as structure fields (sub-6 consumes
  `regAbsorb_rlct` as a bare equality `rw`).

**THE ACCESSOR** (split coords → per-layer gauge blocks): `regGaugeSlotEquiv` (`#78`,
`DeepestSplitReindex.lean`) — `(Fin nReg → ℝ) × (Fin nGauge → ℝ) ≃ₜ (RegGaugeIdx H r → ℝ)`. Feed
`(q.1, q.2.2)` (reg AND spec), read per layer `s`: `X_s = g⟨s, .inl (.inl (i,j))⟩`,
`Y_s = g⟨s, .inl (.inr (i,j))⟩`, `Z_s = g⟨s, .inr (i,j)⟩`. (`DeepestGaugeConstruction`'s `gaugeSlotRead`
already uses this.) The `T`-core is `(split w).2.1` directly (type-forced `FlatIdx (deepestM)`).

**DONE vs OPEN:** `split` (`#64`) + `coreAbsorb`/`coreAbsorb_rlct` (`#79`) are DONE — CONSUME, do not
rebuild. The ONLY open producer work: `#80` (`loss_squeeze`, the two-sided `c₁ < c₂` bound, `#54`
matrix algebra; NOT `ofExactGerm` — the comparability is a genuine squeeze) + `#82` (`regStraighten`
the `E`-straightening reading all slots + `regAbsorb_rlct` via `#72`).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The reduced widths `M = H − r` (the deepest-point reduced chain). -/
abbrev deepestM (H : Fin (L + 1) → ℕ) (r : ℕ) : Fin (L + 1) → ℕ := fun s => H s - r

/-- The regular gauge-orbit-transversal dimension `nReg = r(H⁰+Hᴸ−r)`. -/
abbrev deepestNReg (H : Fin (L + 1) → ℕ) (r : ℕ) : ℕ := r * (H 0 + H (Fin.last L) - r)

/-- The split codomain: `(regular nReg) × ((reduced core flatDim M) × (spectators nGauge))`. -/
abbrev DeepestSplit (H : Fin (L + 1) → ℕ) (r nGauge : ℕ) : Type :=
  (Fin (deepestNReg H r) → ℝ)
    × ((Fin (flatDim (deepestM H r)) → ℝ) × (Fin nGauge → ℝ))

/-- The RAW reduced-core loss in flat coordinates: `‖∏ T_s‖² = dlnLoss M 0` via the fixed flattening
`paramsEquivFlat M`. (The additive-block + spectator-peel run on this raw disjoint core; the
gauge-normalized Schur-`S` core reaches it through `coreAbsorb` + `coreAbsorb_rlct`.) -/
noncomputable abbrev deepestCoreF (H : Fin (L + 1) → ℕ) (r : ℕ)
    (y : Fin (flatDim (deepestM H r)) → ℝ) : ℝ :=
  dlnLoss (deepestM H r)
    (0 : Matrix (Fin (deepestM H r 0)) (Fin (deepestM H r (Fin.last L))) ℝ)
    ((paramsEquivFlat (deepestM H r)).symm y)

-- `continuous_prodAux` / `continuous_prod` / `continuous_dlnLoss` were lifted to the shared
-- `Foundations.LossContinuity` home (#28). They are now imported (same `DLNFibre.DLN.RLCT`
-- namespace) and used unchanged below; the local copies are removed to avoid the cross-lineage
-- duplicate-declaration clash that surfaces when this file is co-imported with the aggregator.

/-- **The deepest-point gauge-slice squeeze datum** (R-squeeze; g150 cert + the sub-34 g152 finding).
At a rank-`r`-exact deepest point, a measure-preserving coordinate reindex `split` of the flat
parameter space `Fin (flatDim H) → ℝ` into `nReg` regular gauge directions, the reduced core
`Fin (flatDim M) → ℝ`, and `nGauge` spectators, under which the loss `dlnLoss H B` (in flat coords) is
**two-sidedly squeezed** near the deepest point by `Φ = ∑ regular² + dlnLoss M 0 (core)`:
`c₁·Φ ≤ loss ≤ c₂·Φ` with `0 < c₁, c₂`.

**Why a SQUEEZE, not a chart equality (sub-34 g152, decorrelated):** a global chart-EQUALITY
`chart : Flat ≃ₜ Flat` + `∀x HasFDerivAt` over-reaches (its `∀x`-derivative form is unsound — the
honest gauge geometry is local). `rlctAtOn` is local, so the squeeze (`rlctAtOn_squeeze`) is the right
altitude — matching the blessed per-node `schur_recursion_step_squeeze`. The absorptions stay `≃ₜ`
SELF-maps (`coreAbsorb` an additive translation homeo — global free; `regStraighten` an `E`-straightening,
nonlinear in its own reg slot, made a global homeo by a CUTOFF inhabiting the Schur/E germ at `0`); the
differentiability lives LOCALLY in the `#71`/`#72` peel hypotheses, NOT as an `∀x` structure field. The
squeeze's core is the GAUGE-NORMALIZED chain (the gauge unit `g = (I+X)⁻¹` makes the raw-`∏T` squeeze
FALSE for matrices; the `Φ`-core `dlnLoss M 0 (core)` is the additive-Schur
`S_s = T_s − Z_s(I+X_s)⁻¹Y_s` chain in the `core` coords). -/
structure DeepestGaugeChart (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) where
  /-- The spectator-coordinate count (the remaining flat directions). -/
  nGauge : ℕ
  /-- The coordinate split: flat `H`-params ≃ₜ `(regular nReg) × ((reduced core flatDim M) × (spectators))`,
  a MEASURE-PRESERVING reindex (so the core slot holds the RAW layer blocks `T_s`). -/
  split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge
  /-- `split` is measure-preserving (a coordinate reindex). -/
  split_mp : MeasurePreserving split volume volume
  /-- `split` carries the flat image of the deepest point to the split origin (deviation coords `= 0`). -/
  split_basepoint : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0
  /-- **The gauge-absorption** on split coords (#61/g156, the corrected ADDITIVE form): a
  self-homeomorphism that turns the RAW core slot `T_s` into the Schur complement
  `S_s = T_s − Z_s(I+X_s)⁻¹Y_s` (an ADDITIVE shear of the core slot by `shift = −Z(I+X)⁻¹Y`, depending
  on the reg/spec slots — `coreShearHomeo`), fixing the regular and spectator slots. (NOT the refuted
  multiplicative `T·(I−VY)⁻¹` — g153's first form; #61/g156 corrected it to the additive Schur
  complement, which is what the translation `coreShearHomeo` produces.) MEASURE-PRESERVING (det = 1, a
  fiber translation — `measurePreserving_coreShear`), so `coreAbsorb_rlct` peels via `#71`/the MP route.
  Needed because the raw-`∏T` squeeze is FALSE for matrices, and a pure MP `split` cannot produce `S`. -/
  coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge
  /-- `coreAbsorb` fixes the origin. -/
  coreAbsorb_basepoint : coreAbsorb 0 = 0
  /-- `coreAbsorb` fixes the regular slot. -/
  coreAbsorb_regular : ∀ q : DeepestSplit H r nGauge, (coreAbsorb q).1 = q.1
  /-- `coreAbsorb` fixes the spectator slot. -/
  coreAbsorb_spectator : ∀ q : DeepestSplit H r nGauge, (coreAbsorb q).2.2 = q.2.2
  /-- **The core-absorption RLCT identity** (sub-34's obligation): the absorbed-core `Φ` and the
  raw-disjoint-core `Φ` have the SAME RLCT at the origin. Proof intent (#61/g156, MP route — the
  additive Schur shear is MEASURE-PRESERVING, det = 1): `π := coreAbsorb = coreShearHomeo shift`, a
  fiber translation `core ↦ core − Z(I+X)⁻¹Y`; `rawΦ ∘ π = absorbedΦ` (via `coreAbsorb_regular`); MP
  via `measurePreserving_coreShear` ⟹ `rlctAtOn_comp_homeomorph` (NO derivative/Jacobian bookkeeping —
  det = 1, not the refuted non-MP `det(I−VY)^{−M0}` of the multiplicative form). -/
  coreAbsorb_rlct :
    rlctAtOn
        (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
        (0 : DeepestSplit H r nGauge)
      = rlctAtOn
          (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
          (0 : DeepestSplit H r nGauge)
  /-- **The regular-absorption** on split coords (g161, the (e)-fix; the (C) wall-fallback shape). The
  split's regular slot is the RAW gauge pivots `(X,Y,Z)`, NOT the nonlinear regular residual
  `E = X₁+X₂+X₁X₂+…` the squeeze needs (`loss_squeeze` over `(split w).1` raw is FALSE, g161
  counterexample). `regStraighten` turns the raw reg slot into `E_pivot` (the core-INDEPENDENT,
  `dE(0)=id` straightened part; the core-dependent `E − E_pivot ∈ ideal(reg)` charges loss-side to
  `∑E²`, RULED 2026-06-23), fixing the core and spectator slots.
  **A bare TOTAL continuous function, NOT a `≃ₜ`** (the (C) fallback, controller-blessed): the IFT
  E-straightening is a local diffeo on `𝓝 0` but does NOT extend to a global spectator-fixing homeomorph
  in Mathlib v4.29 (the piecewise cutoff is discontinuous at `∂V`; no local→global API). A total
  continuous function keeps GLOBAL measurability (so `loss_squeeze`/`rlctAtOn_squeeze` are unaffected);
  the LOCAL invertibility + bounded-unit Jacobian live inside the producer's `regAbsorb_rlct` proof (via
  `rlctAtOn_boundedUnit_localHomeomorph`, crux2 #72, which takes `π/πsymm` as bare functions + `Dπ` + an
  open `V`, inverses only on `V`). The MAP (the cutoff E-straightening) is the producer's. -/
  regStraighten : DeepestSplit H r nGauge → DeepestSplit H r nGauge
  /-- `regStraighten` is (globally) continuous — the (C) fallback's key: total + continuous ⟹ globally
  measurable, so the squeeze's global measurability is preserved (a local OpenPartialHomeomorph would
  break it). -/
  regStraighten_continuous : Continuous regStraighten
  /-- `regStraighten` fixes the origin. -/
  regStraighten_basepoint : regStraighten 0 = 0
  /-- `regStraighten` fixes the core slot. -/
  regStraighten_core : ∀ q : DeepestSplit H r nGauge, (regStraighten q).2.1 = q.2.1
  /-- `regStraighten` fixes the spectator slot. -/
  regStraighten_spectator : ∀ q : DeepestSplit H r nGauge, (regStraighten q).2.2 = q.2.2
  /-- **The regular-unit RLCT peel** (the (e)-fix's reg-side, peeled FIRST so it composes with
  `coreAbsorb_rlct`): the reg-straightened `Φ` (regular through `regStraighten`, core already through
  `coreAbsorb`) and the reg-raw `Φ` have the SAME RLCT at the origin. Sequenced: `regAbsorb_rlct` peels
  the reg unit (core stays `coreAbsorb`'d), then `coreAbsorb_rlct` peels the core unit. Discharged via
  `rlctAtOn_boundedUnit_localHomeomorph` (crux2 #72): `regStraighten` is a local diffeo on an open `V ∋ 0`
  with `|det| = 1` at `0` — the producer supplies `(πsymm, Dπ, V)` to #72 inside this proof (the V/Dπ
  data is NOT a structure field — `regAbsorb_rlct` is consumed as a bare equality by sub-6). -/
  regAbsorb_rlct :
    rlctAtOn
        (fun q : DeepestSplit H r nGauge =>
          (∑ i, (regStraighten q).1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
        (0 : DeepestSplit H r nGauge)
      = rlctAtOn
          (fun q : DeepestSplit H r nGauge =>
            (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
  /-- **The loss-squeeze datum — RLCT-EQUALITY form** (route-B migration, 2026-06-25). The local RLCT of
  `dlnLoss H B` at the deepest point equals that of `Φ = ∑ (regStraighten (split w)).1² + deepestCoreF
  (coreAbsorb (split w)).2.1` (the regular slot through `regStraighten` → the nonlinear residual `E`, the
  core slot through `coreAbsorb` → the Schur core). **This was a POINTWISE two-sided sandwich; it is now
  the RLCT EQUALITY** the downstream chain actually consumes — the pointwise `coreΦ` sandwich is FALSE
  (an on-fibre counterexample: `Rcore = 0`, `loss = Sreg = 0`, but `coreΦ = t⁸ ≠ 0`). The TRUE pointwise
  bound is the `Score = frobSqMat(Rcore)` sandwich (`dlnLoss_two_sided_of_frame`); the producer constructs
  this field from it via `rlctAtOn_squeeze` (⟹ `rlctAtOn(Sreg+Score)`) + the analytic-unit diffeo bridge
  `rlctAtOn(Sreg+Score) = rlctAtOn(Sreg+coreΦ)` (`Ψ : S1 ↦ (I−K)·S1`, `rlctAtOn_comp_localDiffeo`). RLCT
  is diffeo-invariant, so `coreΦ` and `Score` give the SAME RLCT (the headline value is unaffected); the
  field keeps the `coreΦ` RHS so the downstream `deepest_regular_smooth_split` + the `_rlct` fields are
  unchanged. -/
  loss_squeeze :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split x)).2.1)

exec
/bin/bash -lc 'rg "rlctAtOn (dlnLoss" -g"*.lean" lean/DLNFibre/DLN/RLCT/Validate -n' in /tmp/p44-scope
 exited 2 in 0ms:
rg: regex parse error:
    (?:rlctAtOn (dlnLoss)
    ^
error: unclosed group

exec
/bin/bash -lc 'rg "rlctAtOn(.*dlnLoss" -n lean/DLNFibre/DLN/RLCT/Validate' in /tmp/p44-scope
 exited 2 in 0ms:
rg: regex parse error:
    (?:rlctAtOn(.*dlnLoss)
    ^
error: unclosed group

exec
/bin/bash -lc 'rg "rlctAtOn" lean/DLNFibre/DLN/RLCT/Validate -n' in /tmp/p44-scope
 succeeded in 1ms:
lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitSmooth.lean:63:part. (Used at `wstar` to feed `rlctAtOn_comp_localDiffeo`, but holds at every base point.) -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:8:The general per-node mechanism's value step (g138 §5(5)): `rlctAtOn (core) 0 = ⨅ᵢ monomialThreshold`,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:74:`rlctAtOn F 0 = ⨅ᵢ monomialThreshold (d i)(k i)(h i)`. `le_antisymm`: (≤) any admissible `c'` has
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:77:give `∫⁻_U < ⊤` (`rlctAtOn_ge_of_integral_lt`). Mechanism-independent. `⨅ = ofReal(lambdaCore M)` is
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:79:theorem routeM_rlctAtOn_eq_iInf {N : ℕ} (F : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:82:    rlctAtOn F (0 : Fin N → ℝ) = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:85:  · apply rlctAtOn_le_of_adm_le F t
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:92:  · apply rlctAtOn_ge_of_integral_lt F hcover.Fmeas U hcover.Uopen hcover.Umem t
lean/DLNFibre/DLN/RLCT/Validate/RRR.lean:121:    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:9:value `rlctAtOn myF222 0 = 3/2`, where `myF222 = ‖A·B‖²` in the explicit `a00=0..b11=7` flat order
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:10:(the seam's `dlnLoss ∘ e222.symm`). The cover→`rlctAtOn` spine is `Foundations.S1Cover`; the
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:15:box divergence (the `≤`-direction's analytic atom, fed to `rlctAtOn_le_of_box_diverges`) and — to
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:16:come — the concrete 3-deep chart cover and the final `rlctAtOn myF222 0 = 3/2`. The per-axis 1-D
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:110:For the `≤` direction (`rlctAtOn_le_of_box_diverges`), a leaf integrand at-or-above its threshold
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean:279:`rlctAtOn_le_of_box_diverges`). Proof: lower-bound by the open box `(0, ε)^d` (`lintegral_mono_set`),
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCover.lean:44:  The PROVEN general machinery is instead the per-node SQUEEZE `rlctAtOn = nReg/2 + rlctAtOn(reduced)`
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCover.lean:45:  (`schur_recursion_step_squeeze` + `rlctAtOn_layerReduced_transport`) — but that computes `rlctAtOn`
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCover.lean:47:  The squeeze is the wrong SHAPE for this field: lifting `rlctAtOn`-divergence to box-integral divergence
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescentBuild.lean:86:    rlctAtOn (RouteMNodeDescent.ofNodePresentation transport flatCore T bcol SΓ
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescentBuild.lean:88:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:602:genuine `≃L` (block upper-triangular, invertible diagonal). `regAbsorb`/`rlctAtOn_comp_localDiffeo`
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:7:`rlctAtOn (dlnLoss M 0) (chart (0,0)) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` from a measure-preserving
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:9:Composes `dlnLoss_chart_squeeze_descent` (chart transport via `rlctAtOn_comp_homeomorph` + the chart-free
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:42:the chart image `χ (0,0)` splits: `rlctAtOn (dlnLoss M 0) (χ (0,0)) = nReg/2 + rlctAtOn (G²) 0`. Composes
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:43:`rlctAtOn_comp_homeomorph` (transport `dlnLoss` to the chart source) with `schur_recursion_step_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:57:    rlctAtOn (dlnLoss M 0) (chart (0, 0))
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:58:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:59:  -- transport `dlnLoss M 0` to the chart source: `rlctAtOn (dlnLoss M 0) (χ (0,0)) = rlctAtOn (dlnLoss ∘ χ) (0,0)`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:60:  rw [← rlctAtOn_comp_homeomorph chart hmp hemb (dlnLoss M 0) (0, 0)]
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:70:`rlctAtOn (dlnLoss M 0) (χ (0,0)) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`. Composes
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:71:`dlnLoss_chart_squeeze_descent` (chart + squeeze → `nReg/2 + rlctAtOn (G²) 0`, `G = transport.G`) with
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:72:`ReducedTransport.descent` (`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`); the two legs share the SAME
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:90:    rlctAtOn (dlnLoss M 0) (chart (0, 0))
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean:91:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:61:reduced singular core RLCT `rlctAtOn (dlnLoss M 0) 0`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:77:        + rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:105:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:139:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:18:  its transport lemmas (`rlctAtOn_reduced_transport`, `schur_recursion_step_sound`/`_squeeze`), and the
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:85:crux2's banked `rlctAtOn_reduced_transport` datum (det-1 measure-preserving reindex) closing the descent:
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:86:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0` at the child's deepest point. `Y` is the post-blow-up
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:109:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) (fun _ => 0)`. Consumes crux2's banked
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:110:`rlctAtOn_reduced_transport` (det-1 MP); the bundled datum + the anchored `hzero` give the
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:114:    rlctAtOn (fun y => rt.G y ^ 2) (0 : Y)
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:115:      = rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:116:  rlctAtOn_reduced_transport S rt.G rt.redEmbed rt.hmp rt.hemb _ rt.hzero rt.hredCore
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:134:(the chart family always has ≥1 leaf) — `routeM_rlctAtOn_eq_iInf` needs `[Nonempty ι]` for the achiever-side
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:249:    --   • `rlctAtOn_layerReduced_transport` — the descent cert generalised to `dlnLoss (redChain t M)`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:297:`[Nonempty ι]` `routeM_rlctAtOn_eq_iInf` needs for the achiever-side `iInf_le` (crux2's bridge catch). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:13:family in EXACTLY the `(ι, d, k, h)`-tuple shape `routeM_rlctAtOn_eq_iInf`/`resolution_charts`
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:31:`resolution_charts` is `rlctAtOn(core) = ⨅ monomialThreshold` — an equality whose VALUE is this
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:32:lane (`= ½·minAdm = lambdaCore`) but whose `rlctAtOn = ⨅` content is the ANALYTIC COVER: the two
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:52:`routeM_rlctAtOn_eq_iInf` and the gate `resolution_charts` consume the SPLIT tuple `(d, k, h)`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:149:`resolution_charts` is `rlctAtOn(core) = ⨅ monomialThreshold`. The VALUE (`= ½·minAdm = lambdaCore`)
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:150:is the lane above; the `rlctAtOn = ⨅` content is the ANALYTIC COVER (`IsRouteMCover`'s two legs).
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:158:`⨅ monomialThreshold` is the core RLCT at the deepest point. Via `routeM_rlctAtOn_eq_iInf` (the
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:159:bridge) ∘ `rlctAtOn_routeMCore_transport` (flat ↔ params). The residual `hcover` is the ONLY missing
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:166:      rlctAtOn (fun A : Params M =>
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:170:  have hbridge := routeM_rlctAtOn_eq_iInf (routeMCore M) (routeMBaseNbhd M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:172:  rw [← rlctAtOn_routeMCore_transport M]
lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean:15:(det `±1`, NOT a blow-up — so it transports `rlctAtOn` by `rlctAtOn_comp_homeomorph`, the genuine
lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean:40:via `rlctAtOn_comp_homeomorph`.
lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean:85:for transporting `rlctAtOn` via `rlctAtOn_comp_homeomorph`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean:174:cover assembly feeds to `rlctAtOn_comp_homeomorph`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:113:    rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:114:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:155:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:158:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:165:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:169:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:174:      -- `DeepestGaugeChart.loss_squeeze` field): `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:176:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:335:  -- field is the RLCT-EQUALITY `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`. We prove it from the TRUE
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:336:  -- Score-sandwich `hsq` (`deepest_loss_squeeze`, axiom-clean) via `rlctAtOn_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:337:  -- (⟹ `rlctAtOn(Sreg_E + Score)`) + the analytic-unit diffeo bridge `rlctAtOn(Sreg_E + Score) =
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:338:  -- rlctAtOn(Sreg_E + coreΦ)` (`Ψ : S1 ↦ (I−K)·S1`). `Score = frobSqMat(Rcore)` (the `hscore`/`hScoreDef`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:361:  -- **ROUTE-B CLOSE (2026-06-25).** Target: `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)` (the migrated
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:362:  -- field). TWO steps: (1) `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + Score)` — the TRUE Score-sandwich `hsq`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:363:  -- fed to `rlctAtOn_squeeze` after the Params→flat MP transport; (2) the diffeo bridge
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:364:  -- `rlctAtOn(Sreg_E + Score) = rlctAtOn(Sreg_E + coreΦ)` via `Ψ : S1 ↦ (I−K)·S1` (`rlctAtOn_comp_localDiffeo`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:371:  -- **Step 1: `rlctAt(dlnLoss) = rlctAtOn Φscore wstar`** (Params→flat MP transport + `rlctAtOn_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:374:      = rlctAtOn Φscore wstar := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:375:    rw [← rlctAtOn_eq_rlctAt]
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:382:    have htrans := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:392:    refine rlctAtOn_squeeze (fun x => dlnLoss H B ((paramsEquivFlat H).symm x)) Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:466:  have hstep2 : rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:467:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:665:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:668:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:675:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:679:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:684:      -- `DeepestGaugeChart.loss_squeeze` field): `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:686:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:852:    -- field is the RLCT-EQUALITY `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)`. We prove it from the TRUE
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:853:    -- Score-sandwich `hsq` (`deepest_loss_squeeze`, axiom-clean) via `rlctAtOn_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:854:    -- (⟹ `rlctAtOn(Sreg_E + Score)`) + the analytic-unit diffeo bridge `rlctAtOn(Sreg_E + Score) =
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:855:    -- rlctAtOn(Sreg_E + coreΦ)` (`Ψ : S1 ↦ (I−K)·S1`). `Score = frobSqMat(Rcore)` (the `hscore`/`hScoreDef`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:878:    -- **ROUTE-B CLOSE (2026-06-25).** Target: `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + coreΦ)` (the migrated
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:879:    -- field). TWO steps: (1) `rlctAt(dlnLoss) = rlctAtOn(Sreg_E + Score)` — the TRUE Score-sandwich `hsq`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:880:    -- fed to `rlctAtOn_squeeze` after the Params→flat MP transport; (2) the diffeo bridge
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:881:    -- `rlctAtOn(Sreg_E + Score) = rlctAtOn(Sreg_E + coreΦ)` via `Ψ : S1 ↦ (I−K)·S1` (`rlctAtOn_comp_localDiffeo`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:888:    -- **Step 1: `rlctAt(dlnLoss) = rlctAtOn Φscore wstar`** (Params→flat MP transport + `rlctAtOn_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:891:        = rlctAtOn Φscore wstar := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:892:      rw [← rlctAtOn_eq_rlctAt]
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:899:      have htrans := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:909:      refine rlctAtOn_squeeze (fun x => dlnLoss H B ((paramsEquivFlat H).symm x)) Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:983:    have hstep2 : rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:984:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1032:`nReg/2 + rlctAtOn (dlnLoss M 0) 0` — the CORE RLCT, NOT its closed form. The Skeleton's
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1034:gap is exactly the **R1 core-value** `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1042:R1 core-value `hcore : rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's lane) and the
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1050:    (hcore : rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:24:  order — transporting `dlnLoss` to `blockG·blockH` via `rlctAtOn_comp_homeomorph`;
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:25:- `rlctAtOn_blockG_eq_one`: the `EuclideanSpace ℝ (Fin 2)` ↔ `Fin 2 → ℝ` bridge for
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:27:- `rlctAtOn_product_blocks`: the `product_min_rlct_of_ne` (#57) discharge (`block_ne_ae`).
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:132:`rlctAtOn` via `rlctAtOn_comp_homeomorph`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:141:(`measurePreserving_eME212`); transport via `rlctAtOn_comp_homeomorph` (`S1Fubini`), with
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:143:theorem rlctAtOn_case212_eq_product :
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:144:    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:145:      = rlctAtOn (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => blockG p.1 * blockH p.2) (0, 0) := by
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:148:  have key := rlctAtOn_comp_homeomorph eHom212 hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:156:/-- **Each block has RLCT 1.** `rlctAtOn blockG 0 = 1` (and likewise `blockH`): `blockG = Σᵢ aᵢ²` on
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:159:theorem rlctAtOn_blockG_eq_one : rlctAtOn blockG (0 : Fin 2 → ℝ) = 1 := by
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:166:  have key := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:174:theorem rlctAtOn_blockH_eq_one : rlctAtOn blockH (0 : Fin 2 → ℝ) = 1 :=
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:175:  rlctAtOn_blockG_eq_one
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:190:/-- **product-MIN for the two blocks.** `rlctAtOn (G·H)(0,0) = min (rlctAtOn G 0)(rlctAtOn H 0)`
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:193:theorem rlctAtOn_product_blocks :
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:194:    rlctAtOn (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => blockG p.1 * blockH p.2) (0, 0)
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:195:      = min (rlctAtOn blockG 0) (rlctAtOn blockH 0) := by
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:202:closed form `aoyagiLambda (2,1,2) 0 = 1`. Assembled: loss = `G·H` (`rlctAtOn_case212_eq_product`) ⟹
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:203:`min` (`rlctAtOn_product_blocks`) of the block RLCTs (`= 1` each), `min(1,1) = 1 = aoyagiLambda`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:205:    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:207:  rw [rlctAtOn_case212_eq_product, rlctAtOn_product_blocks,
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:208:    rlctAtOn_blockG_eq_one, rlctAtOn_blockH_eq_one, min_self]
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:11:- the cover value `rlctAtOn myF222 0 = 3/2` (`rlctAtOn_myF222_eq`, `Case222CoverGETail`: the geometric
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:12:  `≥`-cover — clean-three, S2-free — antisymmetric with the cited `≤`-half `rlctAtOn_myF222_le`);
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:14:- the measure-preserving transport `rlctAtOn (dlnLoss H222 0) deepest222 = rlctAtOn myF222 0`
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:15:  (`rlctAtOn_dlnLoss222_transport`, `ParamsFlat222`).
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:26:/-- **The `(2,2,2)` core RLCT (on `Params`).** `rlctAtOn (dlnLoss H222 0) deepest222 = 3/2`: the
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:28:(`rlctAtOn_dlnLoss222_transport`) carry the cover value (`rlctAtOn_myF222_eq`) from `Fin 8 → ℝ` to the
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:30:theorem case222_rlctAtOn_eq : rlctAtOn (dlnLoss H222 0) deepest222 = 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:31:  rw [rlctAtOn_dlnLoss222_transport myF222 dlnLoss222_eq_myF222, rlctAtOn_myF222_eq]
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:35:(`rlctAtOn_myF222_ge'`) is axiom-clean (S2-free); the value rests on the cited `≤`-bound (`monomial_rlct`,
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:36:Aoyagi/Watanabe) via `rlctAtOn_myF222_le`. Mirror of `case111_rlct`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:38:  rw [← rlctAtOn_eq_rlctAt, case222_rlctAtOn_eq]
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:41:`resolution_charts` (core form): `rlctAtOn (dlnLoss M 0) deepest = ⨅ monomialThreshold (d i)(k i)(h i)`.
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:49:      rlctAtOn (fun A : Params H222 =>
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:56:          case222_rlctAtOn_eq, iInf_unique, case222_unit_leaf_threshold]⟩
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:48:  shear is `det = 1`) ⟹ `rlctAtOn_comp_homeomorph` (NO Jacobian/weight bookkeeping; #61/g156 corrected
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:202:`rlctAtOn_comp_homeomorph`, det = 1 — NOT the abstract #71 bounded-unit peel) are wired directly. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:207:stays globally measurable for `rlctAtOn_squeeze`). The `regAbsorb_rlct` peel is discharged by
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:208:`rlctAtOn_regAbsorb_reduce` (the `coreAbsorb.symm` conjugation stripping `coreAbsorb` from the core
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:209:term) composed with `rlctAtOn_comp_localDiffeo` (the IFT → `#72` adapter): `E_pivot` need only be
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:241:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:245:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:260:      rlctAtOn (fun q : DeepestSplit H r nGauge =>
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:262:        = rlctAtOn (fun q : DeepestSplit H r nGauge =>
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:266:    have hkey := rlctAtOn_comp_localDiffeo
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:284:  exact rlctAtOn_regAbsorb_reduce2 coreAbsorb E_full
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:291:peels the RLCT via `rlctAtOn_comp_homeomorph` (NO derivative bookkeeping). The two MP helpers
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:300:(`measurePreserving_coreShear`) ⟹ `rlctAtOn_comp_homeomorph`. The concrete Schur shift is plugged in
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:308:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:312:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:317:  -- `coreAbsorb_rlct`: the shear is MP ⟹ `rlctAtOn_comp_homeomorph`, then `coreAbsorb 0 = 0`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:322:  have hkey := rlctAtOn_comp_homeomorph (coreShearHomeo shift hshift) hmp
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:345:Threaded into PIN 1's `regAbsorb_rlct` (`rlctAtOn_regAbsorb_reduce` needs `coreAbsorb` MP for the
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:355:`coreShear_satisfies_coreAbsorb` (`rlctAtOn_comp_homeomorph` on the det-1 shear). The concrete shift
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:362:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:366:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:340:The two `⊤`s the oscillation conflated are DIFFERENT objects: (i) the GEOMETRIC `rlctAtOn (dlnLoss M 0) = ⊤`
lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:343:(root `rlctAtOn = ½·minAdm`) is the COVER's job (`IsRouteMCover`, #104), NOT `foldFamily`. ANCHORED:
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean:9:g161): the bounded-unit-Jacobian data that crux2's `rlctAtOn_boundedUnit_localHomeomorph` (#72)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean:57:/-- **The bounded-unit Jacobian datum** (the `hbdd` of crux2's `rlctAtOn_boundedUnit_localHomeomorph`,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:11:    nReg/2 + rlctAtOn(core)(deepest-core) ≤ rlctAt (dlnLoss H B) v   (at a general optimal `v`)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:21:producer's outputs as hypotheses (the chart transfer `rlctAt (dlnLoss H B) v = rlctAtOn F (0,t0)`,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:22:banked `rlctAtOn_boundedUnit_localHomeomorph` discharges it; the post-chart sum-of-squares form
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:24:comparison `∑s² + R ≤ C·F` near `(0,t0)`), the engine gives `nReg/2 + rlctAtOn R t0 ≤
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:26:`coreV := rlctAtOn R t0`. Mechanical: reuses the banked engine + the chart-transfer equality.
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:29:Setting `coreV := rlctAtOn R t0` (NOT a separate `v−core` map) makes `hAtV` the engine output; the
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:30:SOLE remaining obligation is `hCore : coreDeepest ≤ rlctAtOn R t0`, i.e. `rlctAtOn R 0 ≥
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:31:rlctAtOn (core) 0`.
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:45:factorization is FALSE here. BUT the D1 INEQUALITY STILL HOLDS: `rlctAtOn R 0 = coreDeepest = 3/2`
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:64:delivers `(★)`'s `hAtV` side: `nReg/2 + rlctAtOn R t0 ≤ rlctAt (dlnLoss H B) v`, with
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:65:`coreV := rlctAtOn R t0`. The hypotheses are EXACTLY the producer obligations:
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:67:  * `hchart` — the chart transfer (banked `rlctAtOn_boundedUnit_localHomeomorph` at the producer;
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:75:After this, the remaining D1 obligation is `hCore : coreDeepest ≤ rlctAtOn R t0` (PART (b)). -/
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:81:    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), t0))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:89:    (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:96:leading-form comparison `hCore : coreDeepest ≤ rlctAtOn R t0` (PART (b)), the deepest point has
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:108:    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), t0))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:116:    (hCore : coreDeepest ≤ rlctAtOn R t0) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:118:  have hAtV : (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v :=
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:121:    (rlctAt H (dlnLoss H B) v) m coreDeepest (rlctAtOn R t0) hDeepest hAtV hCore
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:134:germ-changing perturbation — so the identification is `r`-independent and TIGHT (`rlctAtOn R 0 =
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:144:`(t0, g0)`, i.e. `R = (core₀ ∘ fst) ∘ Φ` (`hRform`). Then `rlctAtOn R (t0,g0) = rlctAtOn core₀ t0`:
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:145:the diffeo transfer (`rlctAtOn_boundedUnit_localHomeomorph`) strips `Φ`, the spectator peel
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:146:(`rlctAtOn_spectator_peel`) drops the gauge factor. In particular `coreDeepest = rlctAtOn core₀ t0`
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:147:discharges the D1 `hCore : coreDeepest ≤ rlctAtOn R (t0,g0)` with EQUALITY (the G1 tightness).
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:150:Jacobian on an open `V ∋ (t0,g0)` (the raw-data `rlctAtOn_boundedUnit_localHomeomorph` form —
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:161:fire. `hCore : coreDeepest ≤ rlctAtOn R t0` STILL HOLDS at such `v` (verified EXACT:
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:162:`rlctAtOn R 0 = coreDeepest = 3/2` at that point — the `extra = nReg_v − nReg` Morse halves exactly
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:164:GENERAL `v`, `hCore` is discharged at the VALUE level (`rlctAtOn R 0 ≥ coreDeepest`), an open
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:192:    rlctAtOn R (t0, g0) = rlctAtOn core₀ t0 := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:197:  rw [rlctAtOn_boundedUnit_localHomeomorph (fun p : Reduced × Gauge => core₀ p.1) (t0, g0)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:200:  exact rlctAtOn_spectator_peel core₀ t0 g0 hG
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:8:RECURSION route to `rlctAtOn (dlnLoss M 0) 0 = ofReal (lambdaCore M)` (`= ½·minAdm`), iterating the
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:16:- `hstep` (O1, the NON-degenerate-child step): `rlctAtOn (dlnLoss M 0) 0 = ofReal (nReg M / 2) +
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:17:  rlctAtOn (dlnLoss (redOf M) 0) 0`. Sound only when the child `redOf M` is non-degenerate (the
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:20:  `dlnLoss (redOf M) ≡ 0`, geometric `rlctAtOn = ⊤`), DON'T recurse — `rlctAtOn (dlnLoss M 0) 0 =
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:44:state contributing `0`), the binding R1 core identity holds: `rlctAtOn (dlnLoss M 0) 0 = ofReal
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:12:the **reduced singular core** `rlctAtOn (dlnLoss M 0) 0` on the reduced widths `M = H−r`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:15:`rlctAtOn (dlnLoss M 0) 0`, the core RLCT at its deepest point — NOT on the closed form
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:16:`ofReal(lambdaCore M)`. Folding the core value `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` is
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:33:(`rlctAtOn_squeeze`), not the
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:76:* `coreAbsorb_rlct`: the MP route — `measurePreserving_coreShear` (`#83`) ⟹ `rlctAtOn_comp_homeomorph`
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:78:* `regAbsorb_rlct`: the LOCAL route — `rlctAtOn_boundedUnit_localHomeomorph` (`#72`), which takes
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:135:honest gauge geometry is local). `rlctAtOn` is local, so the squeeze (`rlctAtOn_squeeze`) is the right
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:174:  via `measurePreserving_coreShear` ⟹ `rlctAtOn_comp_homeomorph` (NO derivative/Jacobian bookkeeping —
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:177:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:180:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:192:  continuous function keeps GLOBAL measurability (so `loss_squeeze`/`rlctAtOn_squeeze` are unaffected);
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:194:  `rlctAtOn_boundedUnit_localHomeomorph`, crux2 #72, which takes `π/πsymm` as bare functions + `Dπ` + an
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:211:  `rlctAtOn_boundedUnit_localHomeomorph` (crux2 #72): `regStraighten` is a local diffeo on an open `V ∋ 0`
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:215:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:219:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:230:  this field from it via `rlctAtOn_squeeze` (⟹ `rlctAtOn(Sreg+Score)`) + the analytic-unit diffeo bridge
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:231:  `rlctAtOn(Sreg+Score) = rlctAtOn(Sreg+coreΦ)` (`Ψ : S1 ↦ (I−K)·S1`, `rlctAtOn_comp_localDiffeo`). RLCT
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:237:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:263:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:266:        = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:293:    -- two-sided `c₁ = c₂ = 1` bound, then `rlctAtOn_squeeze` + the Params→flat transport (the SAME chain
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:298:    rw [← rlctAtOn_eq_rlctAt]
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:305:    have htrans := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:316:    refine rlctAtOn_squeeze (fun x => dlnLoss H B ((paramsEquivFlat H).symm x)) Φ wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:360:`rlctAt (dlnLoss H B) deepest = rlctAtOn Φ wstar`, where `Φ = ∑ regular² + dlnLoss M 0 (core)` and
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:361:`wstar = (paramsEquivFlat H) deepest`. Chain: `rlctAtOn_eq_rlctAt` (Params), Params→flat MP transport
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:362:(`rlctAtOn_comp_homeomorph` on `paramsEquivFlat H`), then `rlctAtOn_squeeze` consuming `loss_squeeze`
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:370:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:376:  -- refuted pointwise `coreΦ` sandwich to the RLCT-equality form — the `rlctAtOn_squeeze` + Params→flat
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:382:coordinates has the same RLCT as on `Params M`: `rlctAtOn (dlnLoss M 0 ∘ (paramsEquivFlat M).symm) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:383:= rlctAtOn (dlnLoss M 0) (fun _ => 0)`. Transport along the measure-preserving flattening
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:386:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:390:      = rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:400:  have key := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:421:core)` has RLCT `nReg/2 + rlctAtOn (dlnLoss M 0) 0`: the `nReg` nondegenerate quadratic directions
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:423:via `dlnLoss_nonneg`), the loss-independent gauge spectators peel off (`rlctAtOn_spectator_peel`),
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:424:and the reduced block's RLCT is `rlctAtOn (dlnLoss M 0) 0` (sub-7).
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:443:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:449:        + rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:462:  have hstep1 := rlctAtOn_comp_homeomorph Γ.split Γ.split_mp Γ.split.measurableEmbedding
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:505:  -- Step 3: spectator-peel `rlctAtOn (G²) (0,0) = rlctAtOn coreF 0` then sub-7.
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:511:    rlctAtOn_spectator_peel coreF (0 : Fin (flatDim M) → ℝ) (0 : Fin Γ.nGauge → ℝ)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:518:singular **core RLCT** `rlctAtOn (dlnLoss M 0) 0` on the reduced widths `M = H−r`. This is the gauge
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:519:chart's full content: it carries NO `lambdaCore` (R1's value `rlctAtOn (dlnLoss M 0) 0 =
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:534:        + rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:19:`rlctAtOn_squeeze` downstream needs the absorbed `Φ` GLOBALLY measurable — a local diffeo breaks it).
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:24:`rlctAtOn` is a germ at `0` and the loss-squeeze is local, the germ-at-`0` agreement is all that is
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:386:agreement PIN 2's loss-squeeze consumes (`rlctAtOn`/the squeeze are local). -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:412:`rlctAtOn_regAbsorb_reduce` needs. Abstract over `Ereg` (the concrete general-L residual + its
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:453:/-- **The reg-output is core-independent** (`hra_regdep` for `rlctAtOn_regAbsorb_reduce`): the reg
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:28:**Scope: core-only** (`rlctAtOn(dlnLoss M 0) 0`, `M = H − r`). The regular `[−r²+r(H⁰+Hᴸ)]/2` shift is
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSmooth.lean:12:`rlctAtOn_comp_localDiffeo` consumer uses global continuity for the absorbed map's global measurability).
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:1178:/-- **The `(2,2,2)` `≥`-direction headline** (downstream restatement). `rlctAtOn myF222 0 ≥ 3/2` via
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:1179:`rlctAtOn_ge_of_integral_lt` on `openBox ∋ 0` (`myF222_threshold_lt_top'`). -/
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:1180:theorem rlctAtOn_myF222_ge' : (3 : ℝ≥0∞) / 2 ≤ rlctAtOn myF222 0 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:1181:  apply rlctAtOn_ge_of_integral_lt myF222 ?_ openBox isOpen_openBox mem_openBox_zero (3 / 2)
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:1190:/-- **The `(2,2,2)` resolution value (`#80`): `rlctAtOn myF222 0 = 3/2`.** `le_antisymm` of the gated
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:1191:`≤`-half (`rlctAtOn_myF222_le`, `Case222Resolution` @dd40c45) and the `≥`-half proven here
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:1192:(`rlctAtOn_myF222_ge'`). Every leaf threshold is `3/2` (`Case222Value`), so this is the `⨅`-value. The
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:1195:theorem rlctAtOn_myF222_eq : rlctAtOn myF222 0 = 3 / 2 :=
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean:1196:  le_antisymm rlctAtOn_myF222_le rlctAtOn_myF222_ge'
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:12:    rlctAtOn (fun q => ∑ (regAbsorb q).1² + deepestCoreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:13:      = rlctAtOn (fun q => ∑ q.1²         + deepestCoreF (coreAbsorb q).2.1) 0.
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:26:`coreAbsorb.symm` (RLCT-invariant, `rlctAtOn_comp_homeomorph`), which collapses the core term to
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:36:The remaining genuinely-analytic atom — the decoupled peel `rlctAtOn (G ∘ regAbsorb) 0 = rlctAtOn G
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:38:bounded-unit Jacobian via `rlctAtOn_boundedUnit_localHomeomorph`, which needs the concrete `E` map).
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:89:    rlctAtOn (fun q => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:90:      = rlctAtOn (fun q => regF q.1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:94:    rlctAtOn (fun q => regF (regAbsorb q).1 + coreF q.2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:95:      = rlctAtOn (fun q => regF q.1 + coreF q.2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:100:theorem rlctAtOn_regAbsorb_reduce
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:111:      rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF q.2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:112:        = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:113:    rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:114:      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:123:  have hL : rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:124:      = rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF q.2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:125:    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:143:  have hR : rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:144:      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:145:    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:171:`0` and the peel (`rlctAtOn_comp_localDiffeo`) applies. No core-block-zero needed (invertibility of a
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:173:theorem rlctAtOn_regAbsorb_reduce2
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:181:      rlctAtOn (fun q : R × (C × S) => regF (E (coreAbsorb.symm q)) + coreF q.2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:182:        = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:183:    rlctAtOn (fun q : R × (C × S) => regF (E q) + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:184:      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:193:  have hL : rlctAtOn (fun q : R × (C × S) => regF (E q) + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:194:      = rlctAtOn (fun q : R × (C × S) => regF (E (coreAbsorb.symm q)) + coreF q.2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:195:    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:206:  have hR : rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:207:      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:208:    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:225:The decoupled peel `rlctAtOn (fun q => regF (regStraighten q).1 + coreF q.2.1) 0 = rlctAtOn (fun q =>
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:236:theorem rlctAtOn_regStraighten_peel
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:252:    rlctAtOn (fun q : R × (C × S) => regF (regStraighten q).1 + coreF q.2.1) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:253:      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:256:  have hkey := rlctAtOn_boundedUnit_localHomeomorph
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:268:/-! ## The IFT → #72 adapter (`rlctAtOn_comp_localDiffeo`)
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:272:`rlctAtOn (F ∘ f) wstar = rlctAtOn F wstar`. The implicit-function-theorem
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:283:theorem rlctAtOn_comp_localDiffeo {M : Type*}
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:290:    rlctAtOn (fun w => F (f w)) wstar = rlctAtOn F wstar := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:375:  have hkey := rlctAtOn_boundedUnit_localHomeomorph F wstar f g
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:426:`rlctAtOn_regAbsorb_reduce`): two points with the same reg AND spec slots have the same reg output. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:475:`rlctAtOn_comp_localDiffeo` consumes (it needs the derivative as a `≃L`, not a bare `→L`). The
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:489:is the unitriangular invertible shear `[[I, Σ],[0, I]]` (det 1), which `rlctAtOn_comp_localDiffeo`
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:574:invertible `e` `rlctAtOn_comp_localDiffeo` consumes — decoupled from HOW `D_E`'s reg-block is `id`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:652:`rlctAtOn_regAbsorb_reduce` is then `q = q'` at both reg + carried slots, so trivially equal). -/
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:10:`rlctAtOn myF222 0 = ⨅ᵢ monomialThreshold (dᵢ)(kᵢ)(hᵢ)` (the cover-form; `fm`'s `⨅ = 3/2` wraps it).
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:14:integral, never an `rlctAtOn` transport). The `≤` direction needs only ONE binding leaf chart
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:15:(`rlctAtOn_le_of_box_diverges` + `monomialIntegrand_lintegral_box_eq_top`); the `≥` direction needs
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:32:cover computes; the seam (`rlctAtOn_dlnLoss222_transport`) identifies `dlnLoss H222 0 = myF222 ∘ e222`.
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:75:NOT an `rlctAtOn` transport). -/
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:150:The `≤` direction (`rlctAtOn_le_of_box_diverges`) needs ONE binding leaf chart `φ` whose pulled-back
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:627:/-! ## The `≤`-direction (`rlctAtOn myF222 0 ≤ 3/2`)
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:632:`monomialIntegrand · Uval^{−c'}`. Discharges `rlctAtOn_le_of_box_diverges`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:712:/-- **The `≤`-direction.** `rlctAtOn myF222 0 ≤ 3/2`. For every `c' > 3/2`, `ε > 0`, the cube threshold
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:716:`coordZero_null`), diverge (`leaf_box_div`). Then `rlctAtOn_le_of_box_diverges`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:717:theorem rlctAtOn_myF222_le : rlctAtOn myF222 0 ≤ 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean:718:  apply rlctAtOn_le_of_box_diverges myF222 (3 / 2)
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:313:off the WHOLE sum (`rlctAtOn_comp_homeomorph` + `bareAbsorb_thetaConj_eq_conjAbsorb`): the bare absorbed-core
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:322:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:327:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:346:  have hkey := rlctAtOn_comp_homeomorph Θ hΘmp Θ.measurableEmbedding
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:365:`rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb` (@439) converts bare↔conj with NO drag (`Θ` fixes `q.1`) — and
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:366:lifting back via the `rlctAtOn_regAbsorb_reduce2` (π̃ option-D) LOCAL-DIFFEO reg-absorb (which preserves zero
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:368:`rlctAtOn_comp_localDiffeo` + the `DeepestL2ConjSmooth` `hTilde` lemmas (the conj one rides the value-fold
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:372:/-- **π̃ reg-absorb peel, CONJ side (LANDED).** The `hpeel` input `rlctAtOn_regAbsorb_reduce2` needs for
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:376:annihilates), then `rlctAtOn_comp_localDiffeo` peels it. The conj analogue of the wire's bare `hTilde`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:395:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:401:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:413:  have hkey := rlctAtOn_comp_localDiffeo
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:445:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:451:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:462:  have hkey := rlctAtOn_comp_localDiffeo
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:480:/-- **The gauge-reg reg-absorb (CONJ), via `rlctAtOn_regAbsorb_reduce2` + `regAbsorbPeel_conj`.** Straightens
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:500:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:505:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:510:  rlctAtOn_regAbsorb_reduce2 (deepestCoreAbsorbConj H r B hB hr hL hDA)
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:517:/-- **The gauge-reg reg-absorb (BARE), via `rlctAtOn_regAbsorb_reduce2` + `regAbsorbPeel_bare`.** -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:529:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:534:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:539:  rlctAtOn_regAbsorb_reduce2 (deepestCoreAbsorb H r hr hL)
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:549:`rlctAtOn_comp_localDiffeo` + the `DeepestL2ConjSmooth` `hTilde` lemmas. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:570:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:575:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:580:  -- Rewrite `(regStraighten q).1` to `deepestEFull q` (hregval) under both `rlctAtOn` binders.
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:584:    ← rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb H r B hB hr hL hDA hbdy,
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:588:`split` (`rlctAtOn_comp_homeomorph`, `split wstar = 0`). `rlctAtOn(R'∘split + coreF∘conjAbsorb∘split) wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:589:= rlctAtOn(R'∘split + coreF∘bareAbsorb∘split) wstar`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:614:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:619:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:624:  -- Transport the `0`-form LINK2 to flat `wstar` via `rlctAtOn_comp_homeomorph split` (both sides).
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:625:  have hconj := rlctAtOn_comp_homeomorph split hsplit_mp split.measurableEmbedding
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:629:  have hbare := rlctAtOn_comp_homeomorph split hsplit_mp split.measurableEmbedding
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:684:    rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSub4.lean:685:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:70:`rlctOf := fun M => rlctAtOn (dlnLoss M 0) (deepest)`. -/
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:58:(`core₀ = rlctAtOn`-equal to the deepest core, so `coreDeepest = rlctAtOn core₀ t0`).
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:100:  /-- The IFT chart transfer: `rlctAt (dlnLoss H B) v = rlctAtOn F (0, (t0,g0))`. -/
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:101:  hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), (t0, g0))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:122:  hcoreDeepest : coreDeepest = rlctAtOn core₀ t0
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:189:    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), (t0, g0)))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:196:    (hcoreDeepest : coreDeepest = rlctAtOn core₀ t0)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:252:      = rlctAtOn (fun p : (Fin 0 → ℝ) × (Reduced × Gauge) => (∑ i, p.1 i ^ 2) + 1)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:256:      (rlctAtOn (fun _ : Reduced => (1 : ℝ)) t0)) :=
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:257:  ⟨GeneralVChartL2.ofExactGerm H B v (rlctAtOn (fun _ : Reduced => (1 : ℝ)) t0)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:298:  have hCoreEq : rlctAtOn Γ.R (Γ.t0, Γ.g0) = rlctAtOn Γ.core₀ Γ.t0 :=
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:302:  -- Step 2: `hCore : coreDeepest ≤ rlctAtOn R (t0,g0)` — equality from `hcoreDeepest` + `hCoreEq`.
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean:303:  have hCore : coreDeepest ≤ rlctAtOn Γ.R (Γ.t0, Γ.g0) :=
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:12:  RLCT splits as `nReg/2 + rlctAtOn(G²)`. (Transport `rlctAtOn_comp_homeomorph` + germ-rewrite
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:13:  `rlctAtOn_germ_local` + unit-strip `rlctAtOn_unit_invariant_aux` + smooth-block `S1.5`.)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:14:- `rlctAtOn_germ_local` — general-domain `rlctAtOn` germ-locality (reusable bedrock).
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:18:SOUNDNESS NOTE (the (C2) finding): the *clean* `rlctAtOn(dlnLoss M 0) 0 = nReg/2 + rlctAtOn(Mred) 0`
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:31:/-! The general-domain `rlctAtOn` unit-invariance (the prereq) now lives in `Foundations/S1Local.lean`
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:32:as `rlctAtOn_unit_invariant_aux` (beside `rlct_unit_invariant_aux`), reachable transitively via the
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:206:The clean `rlctAtOn(dlnLoss M 0) 0 = nReg/2 + rlctAtOn(dlnLoss Mred 0) 0` (no chart hypothesis) is
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:216:RLCT splits as `nReg/2 + rlctAtOn(G²)`. The unit `u` is stripped by `rlctAtOn_unit_invariant_aux`; the
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:217:smooth block by `rlct_additive_smooth_block` (S1.5); the chart transport by `rlctAtOn_comp_homeomorph`
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:222:/-- **`rlctAtOn` germ-locality (general domain).** The RLCT threshold depends only on the germ of the
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:223:integrand at the base point: `F =ᶠ[𝓝 w0] G ⟹ rlctAtOn F w0 = rlctAtOn G w0`. The general-domain twin
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:225:home is `S1Local.lean` beside `rlctAtOn_unit_invariant_aux`.) -/
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:226:theorem rlctAtOn_germ_local {N : Type*} [MeasureSpace N] [TopologicalSpace N]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:228:    rlctAtOn F w0 = rlctAtOn G w0 := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:230:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:253:identity misread as a loss-VALUE identity. So the per-node `rlctAtOn` does NOT resolve by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:254:`rlctAtOn_comp_homeomorph` (a change of variables); it resolves by the SQUEEZE (same as L2/g128): the
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:260:`|G| ≤ |F|` and `G` vanishes only where `F` does, then `rlctAtOn G wstar ≤ rlctAtOn F wstar` — a
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:264:theorem rlctAtOn_mono {M : Type*} [MeasureSpace M] [TopologicalSpace M] [OpensMeasurableSpace M]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:267:    rlctAtOn G wstar ≤ rlctAtOn F wstar := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:268:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:289:and `c₁·Φ ≤ F ≤ c₂·Φ` with `0 < c₁`, `0 < c₂`, then `rlctAtOn F wstar = rlctAtOn Φ wstar`. The
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:290:constant multiples `c₁, c₂` are positive units stripped by `rlctAtOn_unit_invariant_aux`; the two
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:291:inequalities give `rlctAtOn_mono` both ways (the `F=0 ⟺ Φ=0` vanishing from the two-sided bound with
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:293:theorem rlctAtOn_squeeze {M : Type*} [MeasureSpace M] [TopologicalSpace M] [OpensMeasurableSpace M]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:297:    rlctAtOn F wstar = rlctAtOn Φ wstar := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:300:  · rw [show rlctAtOn Φ wstar = rlctAtOn (fun w => c₂ * Φ w) wstar from
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:301:      (rlctAtOn_unit_invariant_aux Φ (fun _ => c₂) wstar c₂ c₂ hc₂ (by fun_prop)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:303:    refine rlctAtOn_mono (fun w => c₂ * Φ w) F wstar (by fun_prop) ⟨U, hU, fun w hw => ?_⟩
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:311:  · rw [show rlctAtOn Φ wstar = rlctAtOn (fun w => c₁ * Φ w) wstar from
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:312:      (rlctAtOn_unit_invariant_aux Φ (fun _ => c₁) wstar c₁ c₁ hc₁ (by fun_prop)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:314:    refine rlctAtOn_mono F (fun w => c₁ * Φ w) wstar hFmeas ⟨U, hU, fun w hw => ?_⟩
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:334:`rlctAtOn (dlnLoss M 0) (χ 0) = nReg/2 + rlctAtOn (G²) 0`. Transport (`rlctAtOn_comp_homeomorph`,
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:335:needs `χ` measure-preserving) → germ-rewrite (`rlctAtOn_germ_local`) → unit-strip
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:336:(`rlctAtOn_unit_invariant_aux`) → smooth-block split (`rlct_additive_smooth_block`, S1.5). The det-1
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:351:    rlctAtOn (dlnLoss M 0) (chart (0, 0))
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:352:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:353:  rw [← rlctAtOn_comp_homeomorph chart hmp hemb (dlnLoss M 0) (0, 0)]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:354:  rw [rlctAtOn_germ_local _ (fun p => u p * smoothBlockSplitForm G p) _ hfactor]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:355:  rw [rlctAtOn_unit_invariant_aux (smoothBlockSplitForm G) u (0, 0) a b ha humeas hu]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:362:`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0`. Chain: `rlctAtOn_squeeze` (the two-sided
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:363:`rlctAtOn_mono` + positive-unit strip — NO chart, NO measure Jacobian) → `rlct_additive_smooth_block`
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:379:    rlctAtOn flatCore ((0, 0) : (Fin nReg → ℝ) × Y)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:380:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:386:  rw [rlctAtOn_squeeze flatCore (smoothBlockSplitForm G) _ hFmeas hΦmeas c₁ c₂ hc₁ hc₂ hsq]
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:397:  the deepest point. No chart map; the anchor is the basepoint of `rlctAtOn … (0,0)`.
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:400:  `rlctAtOn_unit_invariant_aux`'s `a > 0` needs. NOT an abstract `Measurable u` (which could vanish).
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:436:`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0` — the regular smooth block plus the reduced-chain
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:438:(the g128/L2 chain: `rlctAtOn_squeeze` + `rlct_additive_smooth_block`). The recursion step the structural
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:445:    rlctAtOn flatCore ((0, 0) : (Fin nReg → ℝ) × Y)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:446:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) (0 : Y) :=
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:644:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) …`. This supplies the transport: if `redEmbed` is a
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:646:`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) redZero` (`rlctAtOn_comp_homeomorph`). The basepoint
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:649:theorem rlctAtOn_reduced_transport {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M)
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:655:    rlctAtOn (fun y => G y ^ 2) (0 : Y) = rlctAtOn (dlnLoss S.red 0) redZero := by
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:658:  rw [hpull, rlctAtOn_comp_homeomorph redEmbed hmp hemb (dlnLoss S.red 0) 0, hzero]
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:28:* Step Θ (`rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb`): `rlctAtOn(reg²+coreF∘bareAbsorb) =
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:29:  rlctAtOn(reg²+coreF∘conjAbsorb)` at `0`, via the MP core-shear `Θ = coreShearHomeo (schurCutoffShiftConj
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:30:  − schurCutoffShift)` (det-1, basepoint-fixing, reg-fixing; `rlctAtOn_comp_homeomorph`, NO derivative).
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:337:fixing the reg slot, so `rlctAtOn_comp_homeomorph` peels it — `rlctAtOn(reg²+coreF∘bareAbsorb) =
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:338:rlctAtOn(reg²+coreF∘conjAbsorb)` with NO derivative bookkeeping (atom-free). -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:438:the reg slot with `bareAbsorb ∘ Θ = conjAbsorb`, so `rlctAtOn_comp_homeomorph` peels it. Atom-free. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:439:theorem rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb (H : Fin (L + 1) → ℕ) (r : ℕ)
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:444:    rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:448:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:470:  have hkey := rlctAtOn_comp_homeomorph Θ hΘmp Θ.measurableEmbedding G 0
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotRowWLOG.lean:280:`rlctAtOn_comp_homeomorph`). So the infimum is preserved — the row dual of the colPerm lemma. -/
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotRowWLOG.lean:306:    have htrans := rlctAtOn_comp_homeomorph τ hmp hemb (dlnLoss H Bp) w
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotRowWLOG.lean:311:    rw [hcomp, rlctAtOn_eq_rlctAt, rlctAtOn_eq_rlctAt] at htrans
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:8:`rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`, with `Φscore` carrying the matrix-Schur `Score` and
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:17:Given those two, `rlctAtOn_diffeo_bridge_of` discharges `hstep2` by germ-locality
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:18:(`rlctAtOn_germ_local`) + RLCT-invariance under a local diffeo (`rlctAtOn_comp_localDiffeo`). The proof
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:35:`wstar`, then `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`. Proof: germ-locality replaces `Φscore`
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:36:by `Φcore ∘ Psi`, and `rlctAtOn_comp_localDiffeo` strips `Psi`. This is the exact shape `hstep2`
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:39:theorem rlctAtOn_diffeo_bridge_of {M : Type*}
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:47:    rlctAtOn Φscore wstar = rlctAtOn Φcore wstar := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:48:  rw [← rlctAtOn_germ_local (fun x => Φcore (Psi x)) Φscore wstar hcomp]
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean:49:  exact rlctAtOn_comp_localDiffeo Φcore wstar Psi e hcontdiff hderiv hfix
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:12:producer / `hfin`: purely `dlnLoss` + the column permutation + the banked `rlctAtOn`-MP-invariance.
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:27:   `rlctAtOn_comp_homeomorph` + an `iInf`-over-bijection congruence).
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:344:`rlctAtOn_comp_homeomorph`). So the infimum is preserved — choice-independent, through the
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:373:    have htrans := rlctAtOn_comp_homeomorph τ hmp hemb (dlnLoss H Bp) w
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:378:    rw [hcomp, rlctAtOn_eq_rlctAt, rlctAtOn_eq_rlctAt] at htrans
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:6:The `≥` half of the `(2,2,2)` resolution value: `rlctAtOn myF222 0 ≥ 3/2`. Together with the gated
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:7:`≤`-half (`rlctAtOn_myF222_le`, `Case222Resolution`) this pins `rlctAtOn myF222 0 = 3/2 = ⨅`.
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:9:## The reduction (gated `rlctAtOn_ge_of_integral_lt`) — on a BOUNDED open box
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:11:`rlctAtOn_ge_of_integral_lt` reduces `3/2 ≤ rlctAtOn myF222 0` to the threshold-integral finiteness
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:27:SPECIFY stage: `rlctAtOn_myF222_ge` headline verified (reduces to `hfin` over `openBox`); `hfin`
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:282:(`rlctAtOn_myF222_ge'`, `rlctAtOn_myF222_eq`), where `p0_summand_via_tail` (the `p = 0` chain) and the
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean:284:(`aPivotSummand_lt_top` / `myF222_threshold_lintegral_lt_top` / `rlctAtOn_myF222_ge`) were superseded by
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:13:`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`; it makes NO codim claim. When G-b's
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:23:- `IsSchurStraightenSqueeze` — the squeeze giving `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0`
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:25:- `ReducedTransport S Y` — the det-1 MP reindex closing `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:27:Composed: `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` — the per-node DESCENT STEP that
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:47:compacts `volume` — the squeeze's `rlctAtOn` measure hygiene; the `MeasureSpace` / `TopologicalSpace` / `Zero`
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:59:ONLY: `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` must NOT be iterated INTO a
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:60:degenerate leaf (`isLeafNode M ↔ ∃ s, M s = 0`, where `dlnLoss ≡ 0` so `rlctAtOn = ⊤` and
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:72:  /-- The det-1 MP descent transport (closes `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`); its `G` is
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:78:  /-- The #134 ONE-datum squeeze: `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0`, with `G` and
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:84:`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0)`. Composes the banked
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:85:`schur_straighten_squeeze_of_data` (the `nReg/2 + rlctAtOn (G²) 0` split, with `G = transport.G`) with
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:86:`ReducedTransport.descent` (`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`). The two legs share the SAME
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:93:    rlctAtOn nd.flatCore (0, 0)
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:94:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:121:(`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`) and recurses on `S.red` (the
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:127:    rlctAtOn nd.flatCore (0, 0)
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean:128:      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:22:`H¹ = 0`: there the loss is an empty sum `≡ 0`, so `rlctAt = ⊤` (`rlctAtOn_zero_eq_top`), while the
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:37:`rlctAtOn (∑ᵢ xᵢ²) 0 = (m+1)/2` on the product Lebesgue measure, bridged from
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:39:measure-preserving homeomorph `toLp`. Generalises `Case212.rlctAtOn_blockG_eq_one` (`m = 1`). -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:40:theorem sumSq_rlctAtOn_finN (m : ℕ) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:41:    rlctAtOn (fun x : Fin (m + 1) → ℝ => ∑ i, x i ^ 2) (0 : Fin (m + 1) → ℝ)
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:47:  have key := rlctAtOn_comp_homeomorph e hmp hemb
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:59:theorem sumSq_rlctAtOn_finN_pos (n : ℕ) (hn : 0 < n) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:60:    rlctAtOn (fun x : Fin n → ℝ => ∑ i, x i ^ 2) (0 : Fin n → ℝ) = ((n : ℕ) / 2 : ℝ≥0∞) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:62:  exact sumSq_rlctAtOn_finN m
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:145:(`Homeomorph.addRight`), and apply `sumSq_rlctAtOn_finN`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:160:  -- Step 1: rlctAt = rlctAtOn (loss ∘ p.symm) at c (flatten via the homeomorph p.symm)
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:161:  rw [← rlctAtOn_eq_rlctAt]
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:165:  have hstep1 := rlctAtOn_comp_homeomorph p.symm hpmp hpemb (dlnLoss H B) c
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:176:  have hstep2 := rlctAtOn_comp_homeomorph τ hτmp hτemb (fun x => dlnLoss H B (p.symm x)) 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:195:  rw [hcomp, sumSq_rlctAtOn_finN_pos n hnpos]
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:9:The `(2,2,2)` value `rlctAtOn (dlnLoss H222 0) deepest222 = 3/2` routed through the **general**
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:10:`IsRouteMCover` / `routeM_rlctAtOn_eq_iInf` engine (the path that generalizes to all rank patterns),
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:11:rather than through the concrete `rlctAtOn_myF222_eq` of `Case222Rlct`.
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:14:end-to-end in `Case222Rlct` (`case222_rlctAtOn_eq` / `case222_rlct`), via the concrete geometric
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:15:`≥`-cover (`rlctAtOn_myF222_eq`, clean-three, S2-free) antisymmetric with the cited `≤`-half
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:17:value through the general abstraction — exercising `IsRouteMCover` + `routeM_rlctAtOn_eq_iInf`
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:23:* `routeM_rlctAtOn_eq_iInf` gives `rlctAtOn myF222 0 = ⨅ i, monomialThreshold (…) = 3/2`
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:25:* `rlctAtOn_dlnLoss222_transport` (the `e222` measure-preserving reindex, via `dlnLoss222_eq_myF222`)
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:49:/-- **The `(2,2,2)` cover value through the general engine.** `rlctAtOn myF222 0 = 3/2`, derived by
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:50:feeding `isRouteMCover_222` to the GENERAL `routeM_rlctAtOn_eq_iInf` (`= ⨅ monomialThreshold`) and
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:52:`rlctAtOn_myF222_eq`. -/
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:53:theorem rlctAtOn_myF222_eq_routeM : rlctAtOn myF222 (0 : Fin 8 → ℝ) = 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:54:  rw [routeM_rlctAtOn_eq_iInf myF222 openBox (Fin 1) routeM222D routeM222K routeM222H
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:58:/-- **The `(2,2,2)` R1 leg through the general engine** (the milestone). `rlctAtOn (dlnLoss H222 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:59:deepest222 = 3/2`, derived through the general `IsRouteMCover` / `routeM_rlctAtOn_eq_iInf` path:
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:60:transport the loss to `myF222` (`rlctAtOn_dlnLoss222_transport` + `dlnLoss222_eq_myF222`), then read
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:61:off the general-engine cover value (`rlctAtOn_myF222_eq_routeM`). Reproduces `Case222Rlct`'s
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:62:`case222_rlctAtOn_eq` (which goes through the concrete cover) via the GENERAL abstraction — the
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:64:theorem case222_rlctAtOn_eq_routeM :
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:65:    rlctAtOn (dlnLoss H222 0) deepest222 = 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean:66:  rw [rlctAtOn_dlnLoss222_transport myF222 dlnLoss222_eq_myF222, rlctAtOn_myF222_eq_routeM]
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurSmooth.lean:11:GLOBALLY plus an invertible strict derivative. The consumer `rlctAtOn_comp_localDiffeo` demands GLOBAL
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:9:abstract Route-M bridge `routeM_rlctAtOn_eq_iInf` (which consumes `F : (Fin N → ℝ) → ℝ`, `U`, `ι d k h`).
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:17:The KEYSTONE (`rlctAtOn_routeMCore_transport`): the bridge concludes about `rlctAtOn (routeMCore M) 0`;
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:18:this transports it to the genuine `rlctAtOn (dlnLoss M 0) (fun _ => 0)` at the deepest point, via the
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:19:measure-preserving homeomorphism `paramsEquivFlat M` (`rlctAtOn_comp_homeomorph`, S1Fubini) + the
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:21:`rlctAtOn_dlnLoss222_transport` (ParamsFlat222, the (2,2,2) seam).
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:25:family (gated). So this banks the headline plumbing the route to `routeM_rlctAtOn_eq_iInf` rests on.
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:100:deepest point: `rlctAtOn (routeMCore M) 0 = rlctAtOn (dlnLoss M 0) (fun _ => 0)`. Via
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:101:`rlctAtOn_comp_homeomorph` (the measure-preserving homeomorphism `paramsEquivFlat M`) + the
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:102:zero-preserving `paramsEquivFlat_deepest`. The general-M analog of `rlctAtOn_dlnLoss222_transport`; this is
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:103:what carries crux2's bridge conclusion `rlctAtOn (routeMCore M) 0 = ⨅ …` back to the headline's
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:104:`rlctAtOn (dlnLoss M 0) (deepest)`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:105:theorem rlctAtOn_routeMCore_transport (M : Fin (L + 1) → ℕ) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:106:    rlctAtOn (routeMCore M) (0 : Fin (routeMAmbient M) → ℝ)
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:107:      = rlctAtOn (dlnLoss M 0) (fun _ => 0 : Params M) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:112:  have key := rlctAtOn_comp_homeomorph (paramsEquivFlatHomeo M) hmp hemb (routeMCore M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean:114:  -- `key : rlctAtOn (routeMCore M ∘ e) deepest = rlctAtOn (routeMCore M) (e deepest)`
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:22:abstract `rlctAtOn_comp_localDiffeo` + `rlctAtOn_germ_local`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:25:assembly, every body `sorry`. Typechecks against the banked `rlctAtOn_comp_localDiffeo` interface.
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:3056:Assembles via the banked abstract bridge `rlctAtOn_diffeo_bridge_of`: S6 comp-identity (germ) +
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:3121:    rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:3122:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:3137:  exact rlctAtOn_diffeo_bridge_of Φscore Φcore wstar (psiL2 H r B hB hr hL J Pf Qf)
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:289:origin, `rlctAtOn(core)(0) = ⨅ monomialThreshold`. For the trivial network `M = (1,1,1)` the core IS
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:293:(`iInf_unique`), `rlctAtOn = rlctAt` on `Params`, to the proven bridge
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:298:      rlctAtOn (fun A : Params (![1, 1, 1] : Fin 3 → ℕ) =>
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:305:          rlctAtOn_eq_rlctAt, case111_rlct_eq_monomialThreshold, iInf_unique]⟩
lean/DLNFibre/DLN/RLCT/Validate/RouteMNReg.lean:10:(`schur_node_loss_presentation`). The per-node RLCT splits `nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:410:(`schur_recursion_step_squeeze`, banked) and the det-1 MP reindex (`rlctAtOn_comp_homeomorph`, banked) are
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:445:`rlctAtOn_reduced_transport`). If the post-blow-up reduced core `G` pulls back the COLLAPSED chain loss
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:447:anchored at the deepest point, then `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss (redChain t M) 0) redZero`. The
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:449:(`rlctAtOn_comp_homeomorph`), so the same proof transports to the one-fewer-arity chain. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:450:theorem rlctAtOn_layerReduced_transport (t : ℕ) (M : Fin (L + 1 + 1 + 1) → ℕ)
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:456:    rlctAtOn (fun y => G y ^ 2) (0 : Y) = rlctAtOn (dlnLoss (redChain t M) 0) redZero := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:459:  rw [hpull, rlctAtOn_comp_homeomorph redEmbed hmp hemb (dlnLoss (redChain t M) 0) 0, hzero]
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:612:`routeM_rlctAtOn_eq_iInf` target value, delivered by the LAYER-COLLAPSING atlas: every leaf's single
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMCover.lean:18:  `rlctAtOn_myF222_le`'s `≤`-leg, at-and-above the threshold).
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMCover.lean:24:`dlnLoss H222 0` RLCT statement requires transporting across `e222` (`rlctAtOn_dlnLoss222_transport`,
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMCover.lean:157:`[−ε, ε]^8` is `⊤`. This is the `(2,2,2)` `≤`-direction analytic content (`rlctAtOn_myF222_le`'s calc),
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMCover.lean:162:(unlike the `> 3/2` `rlctAtOn_myF222_le`), as `cover_ge_div`'s `monomialThreshold ≤ c'` premise needs. -/
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:22:    rlctAtOn R 0 = extra/2 + lambdaCore(M'),   extra = m(a+b) − ab,  M' = (m−a, m−a−b, m−b),
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:36:and produces `coreDeepest ≤ rlctAtOn R t0`.
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:252:    extra/2 + rlctAtOn R₂ t0₂ ≤ rlctAtOn R t0,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:254:and the §5 R1-resolution-at-`M'` interface (`hDegraded`) supplies `rlctAtOn R₂ t0₂ =
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:257:and `coreDeepest = ofReal(lambdaCore (square m))`, this gives `coreDeepest ≤ rlctAtOn R t0` — the
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:263:data `a + b ≤ m`: given the second-peel chart transfer (`hchart₂ : rlctAtOn R t0 = rlctAtOn F₂
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:266:degraded-core value `hDegraded : rlctAtOn R₂ t0₂ = ofReal(lambdaCore M')` (the §5 interface
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:269:the D1 `hCore` holds: `coreDeepest ≤ rlctAtOn R t0`. The `extra` Morse squares peeled in the SECOND
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:279:    (hchart₂ : rlctAtOn R t0 = rlctAtOn F₂ ((0 : Fin (extraCount m a b) → ℝ), t0₂))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:287:    (hDegraded : rlctAtOn R₂ t0₂ = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:288:    coreDeepest ≤ rlctAtOn R t0 := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:290:  have hpeel : (extraCount m a b : ℝ≥0∞) / 2 + rlctAtOn R₂ t0₂
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:291:      ≤ rlctAtOn F₂ ((0 : Fin (extraCount m a b) → ℝ), t0₂) :=
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:322:    rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last 2))) ℝ) A)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:332:    rlctAtOn (fun A : Params (MprimeWidths m a b) =>
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:367:    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin (nRegL2 H r) → ℝ), t0))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:378:    (hchart₂ : rlctAtOn R t0 = rlctAtOn F₂ ((0 : Fin (extraCount m a b) → ℝ), t0₂))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:386:    (hDegraded : rlctAtOn R₂ t0₂ = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:388:  -- discharge `hCore : coreDeepest ≤ rlctAtOn R t0` from the SECOND peel + the interface
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:389:  have hCore : coreDeepest ≤ rlctAtOn R t0 :=
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:12:`Q = ‖q‖²`. The network-free producer `rlctAtOn_quasiSplit_ge_of_contDiff_residual`
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:15:the bounded-unit chart TRANSFER `hchart : rlctAt (dlnLoss H B) v = rlctAtOn F (0,t0)` (the banked
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:16:`rlctAtOn_boundedUnit_localHomeomorph` applied to the actual `Params H → flat` IFT chart at `v` —
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:23:    `nReg/2 + rlctAtOn R t0 ≤ rlctAt (dlnLoss H B) v`, with `F`, `R` built from `q` (no bare
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:29:    two `C¹` residuals; only `hchart`/`hchart₂` (the two `rlctAtOn`-equality transfers), `hDeepest`
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:47:    (m : ℝ≥0∞)/2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v.
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:50:network-free `rlctAtOn_quasiSplit_ge_of_contDiff_residual`. (The regular-block count `m` is FREE in
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:60:        = rlctAtOn (fun p : (Fin m → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2))
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:64:    (m : ℝ≥0∞) / 2 + rlctAtOn (fun t : Y => ∑ i, q ((0 : Fin m → ℝ), t) i ^ 2) t0
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:67:  exact rlctAtOn_quasiSplit_ge_of_contDiff_residual q hq t0 hRne
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:82:`rlctAtOn`-equality transfers, `hDeepest`, and the R1 interface stay hypotheses.
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:96:        = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2))
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:103:    (hchart₂ : rlctAtOn (fun t : Y => ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:104:        = rlctAtOn (fun p : (Fin (extraCount m a b) → ℝ) × Y₂ =>
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:109:    (hDegraded : rlctAtOn (fun t : Y₂ => ∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), t) i ^ 2) t0₂
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:17:  `rlctAt H (dlnLoss H B) deepestPoint = nReg/2 + rlctAtOn(dlnLoss M 0) 0` (core RLCT, NOT `lambdaCore`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:20:- **`hRValue`** — R1's value `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)` (= `resolution_charts`
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:40:(`rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`), the local RLCT at the deepest point IS the
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:42:target. Proof: `deepest_regular_core_reduces` (value-free, `nReg/2 + rlctAtOn(core) 0`) ▸ `hRValue`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:57:      rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:16:  `rlctAtOn F (t • v) = rlctAtOn F v`. The germ at `t·v` pulls back under the scaling diffeo `w = t·w'`
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:17:  (`rlctAtOn_comp_homeomorph`) to `t^D · (germ at v)`; the constant `t^D` is a unit
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:18:  (`rlctAtOn_unit_invariant_aux`). Reachable from green primitives + the homogeneity hypothesis.
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:22:  primitive" overestimate). `rlctAtOn F 0 ≤ rlctAtOn F v`: by `sSup_le` over admissible `c'` at `0`,
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:24:  admissible at `s•v` ⟹ `c' ≤ rlctAtOn (s•v) = rlctAtOn v` (L1-a). NO Fatou / Varchenko / general
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:44:constant along the punctured ray: `rlctAtOn F (t • v) = rlctAtOn F v`. The scaling `σ_t : w ↦ t • w` is
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:51:peeled by `rlctAtOn_unit_invariant_aux`. (ii) DIRECT admissible-set bijection: `Ω ∋ t•v` admissible ⟺
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:53:(homogeneity), both finite-nonzero, so finiteness is preserved) — like `rlctAtOn_spectator_peel`'s
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:55:theorem rlctAtOn_ray_scaling_invariant
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:59:    rlctAtOn F (t • v) = rlctAtOn F v := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:99:  -- assemble: `rlctAtOn F (t•v) = wThr F 1 {t•v} = wThr (F∘σ) (t^N) {v} = wThr (F∘σ) 1 {v}`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:100:  rw [rlctAtOn, htrans, hpeel]
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:105:  have := rlctAtOn_unit_invariant_aux F (fun _ : Fin N → ℝ => t ^ D) v (t ^ D) (t ^ D)
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:108:  rw [rlctAtOn, weightedThreshold] at this ⊢
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:113:point `0 = lim_{s→0} s • v` has RLCT `≤` the (ray-constant) RLCT at `v`: `rlctAtOn F 0 ≤ rlctAtOn F v`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:114:**Proof = nbhd-monotonicity of `rlctAtOn`, ~10 lines from the `sSup`/`∃Ω∋·` def:** for each admissible
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:116:is a nbhd of `s • v` too ⟹ `c'` admissible at `s • v` ⟹ `c' ≤ rlctAtOn F (s•v) = rlctAtOn F v` (L1-a);
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:118:theorem rlctAtOn_lsc_at_origin
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:121:    rlctAtOn F (0 : Fin N → ℝ) ≤ rlctAtOn F v := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:122:  unfold rlctAtOn weightedThreshold
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:146:  have hle_sv : (c' : ℝ≥0∞) ≤ rlctAtOn F (s • v) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:147:    rw [rlctAtOn, weightedThreshold]; exact le_sSup hadm_sv
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:148:  rw [rlctAtOn_ray_scaling_invariant F v D s hspos hFmeas hhomog] at hle_sv
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:152:deepest point `0` has the minimal local RLCT over all `v`: `rlctAtOn F 0 ≤ rlctAtOn F v`. This is
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:153:exactly `rlctAtOn_lsc_at_origin` — the assembly point where L1-a (ray-constancy) + L1-b (semicontinuity
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:160:    rlctAtOn F (0 : Fin N → ℝ) ≤ rlctAtOn F v :=
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:161:  rlctAtOn_lsc_at_origin F v D hFmeas hhomog
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:171:  `rlctAt(dlnLoss H B) deepest = nReg/2 + rlctAtOn(core) (deepest-core)`   [L2 at deepest, PROVEN]
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:172:  `rlctAt(dlnLoss H B) v       = nReg/2 + rlctAtOn(core) (v-core)`          [L2-at-`v`, the open piece]
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:173:  `rlctAtOn(core) (deepest-core) ≤ rlctAtOn(core) (v-core)`                 [CORE-P1, PROVEN]
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:2613:/-- **Step Ψ_conj — the L=2 CONJUGATED diffeo bridge** (`rlctAtOn Φscore = rlctAtOn Φcore_conj`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:2615:`rlctAtOn_diffeo_bridge_of` from S6 (`comp_identity_L2_conj`, germ) + S2 (`psiL2Conj_contDiff`) + S4
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:2617:Step Θ (`rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb`) closes the atom-free `hstep2 = Θ ∘ Ψ_conj`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:2647:    rlctAtOn Φscore wstar
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:2648:      = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean:2660:  exact rlctAtOn_diffeo_bridge_of Φscore Φcore wstar
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:40:`descentStep : rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss (1,1,2) 0) 0 = 2/2 + rlctAtOn(child)`.
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:43:NUMERICALLY equals the committed `case222_rlctAtOn_eq` (`Case222Rlct`); this is a value coincidence — the
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:44:file does NOT prove `rlctAtOn flatCore (0,0) = rlctAtOn (dlnLoss H222 0) deepest222` (that is exactly the
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:124:/-- The `(2,2,2)`-node `ReducedTransport` (the det-1 MP descent closing `rlctAtOn (G²) 0 = rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:307:/-- **The per-node descent step** for the `(2,2,2)` anchor: `rlctAtOn flatCore (0,0) = 2/2 + rlctAtOn
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:311:    rlctAtOn routeMNodeDescent222.flatCore (0, 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:312:      = (2 : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss (schurState M222route M222_hlo).red 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:320:NUMERICALLY equals the committed `(2,2,2)` RLCT `case222_rlctAtOn_eq = 3/2` — a coincidence, NOT an
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:321:identification: this proves `rlctAtOn flatCore222 (0,0) = 3/2`, not `rlctAtOn (dlnLoss H222 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:326:    (hred : rlctAtOn (dlnLoss (schurState M222route M222_hlo).red 0)
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:328:    rlctAtOn routeMNodeDescent222.flatCore (0, 0) = 3 / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:38:- The PROVEN squeeze (`rlctAtOn_squeeze`, `schur_recursion_step_squeeze`) computes the POINT
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:39:  RLCT `rlctAtOn (routeMCore M) 0` additively along the achiever path, giving the upper bound
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:40:  `rlctAtOn (routeMCore M) 0 ≤ ½·minAdm M`. That is STRICTLY WEAKER than this atom: `rlctAtOn ≤ t`
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:44:  `rlctAtOn ≤ t` would be the forbidden value-correct-germ-degenerate fill — the trap; NOT done.)
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:121:This gives the lower bound `rlctAtOn (routeMCore M) 0 ≤ ½·minAdm M` (`cover_ge_div`, via
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:126:`rlctAtOn ≤ ½·minAdm M`, strictly weaker than this BOUNDARY box-divergence; the route is the
lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean:11:`hloss` hypothesis of `rlctAtOn_dlnLoss222_transport`.
lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean:49:the `hloss` hypothesis of `rlctAtOn_dlnLoss222_transport`, closing the seam end-to-end. Via
lean/DLNFibre/DLN/RLCT/Validate/RouteMCoverLemmas.lean:16:  divergence `∫⁻_{[−ε,ε]^N} |F|^{−c'} = ⊤` (the same content as `rlctAtOn_le_of_box_diverges`'s
lean/DLNFibre/DLN/RLCT/Validate/RouteMCoverLemmas.lean:69:of `rlctAtOn_le_of_box_diverges` (the `≤`-direction localisation), repackaged to the `¬ IntegrableOn`

exec
/bin/bash -lc "sed -n '990,1240p' lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean" in /tmp/p44-scope
 succeeded in 0ms:
exec
/bin/bash -lc "sed -n '1,200p' p44-reachability-answer.md" in /tmp/p44-scope
 succeeded in 0ms:
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
OpenAI Codex v0.142.4
--------
workdir: /tmp/p44-scope
model: gpt-5-codex
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019f164e-a56c-7c00-98e1-20350edc6700
--------
user
# Scope: is the L2 deepest-point RLCT normal form (#44) reachable via the new §SEL IFT chart?

Decorrelated reachability adjudication. Lean 4 + Mathlib, a DLN RLCT formalisation. Pure
math/architecture reasoning — I want a BOUNDED-via-chart vs RESEARCH-WALL verdict + the route. Be
adversarial and concrete.

## The target (#44, currently a NAMED sorry, ~600–1500 LoC est. via the heavy route)
`deepest_regular_core_normal_form`: at the DEEPEST point of the DLN loss (L=2, layers all rank exactly
`r`; `B = A¹A²`, rank B = r), the local RLCT is
> `rlctAt H (dlnLoss H B) (deepestPoint) = nReg/2 + lambdaCore(H − r)`
where `nReg = r(H0 + H2 − r)` and `lambdaCore(M)` is a CLOSED-FORM combinatorial value
(`½·min_T M(T)` over an admissible cone — NOT defined as an RLCT; it's the recursively-computed core).

The docstring's intended proof: a rank-`r` gauge-slice change of variables `C_s = [[I_r+X_s, Y_s],[Z_s,
T_s]]` (regular coords = output residual blocks P₁₁−I, P₁₂, P₂₁; reduced core = ‖∏C'_s‖² = dlnLoss(H−r) 0),
routed through `rlctAtOn_unit_invariant_aux` + germ-locality (the slice has unit Jacobian, NOT det ±1, so
NOT a measure-preserving change of variables). That's the heavy 600–1500 LoC obligation.

## The NEW machinery (just built, separately): the §SEL general-`v` IFT chart
For a GENERAL optimal `v` (prod v = B, rank B = r), an IFT chart Φ (selected nReg loss-minors + complement
projection, det DΦ ≠ 0 PROVEN) transfers the local RLCT:
> `rlctAt H (dlnLoss H B) v = rlctAtOn (fun (s,y) => ∑ᵢ sᵢ² + ∑ⱼ qⱼ(s,y)²) (0, t0)`
i.e. `nReg` coordinates become exact squares `∑ s²` and the rest is a C¹ residual `q`. Then a banked
quasi-split engine gives `rlctAtOn (∑s² + ∑q²) (0,t0) = nReg/2 + rlctAtOn (∑ q(0,·)²) t0` (the residual's
own RLCT). The deepest point is a SPECIAL CASE of a general optimal `v`.

## THE QUESTION
Is #44 REACHABLE by applying the §SEL chart AT the deepest point (special case), reducing it to:
(A) the chart gives `rlctAt(deepest) = nReg/2 + rlctAtOn(residual q(0,·)²) t0` — mechanical from the
    banked chart + quasi-split, AND
(B) `rlctAtOn(residual q(0,·)² at deepest) = lambdaCore(H − r)` — the residual's RLCT equals the
    closed-form core?
— thereby REPLACING the heavy gauge-slice with {chart + quasi-split + (B)}? Or does (B) itself reopen the
same heavy gauge-slice / recursion, making the chart route no easier?

Sub-questions:
Q1. At the DEEPEST point specifically, is the §SEL residual `q(0,·)` literally (or up to a measure-
    preserving/diffeo reindex) the REDUCED-WIDTH loss `dlnLoss (H−r) 0` (the `∏ C'_s` core in the
    docstring)? I.e. does the selected-minor chart's complement coordinates at the deepest point coincide
    with the reduced-core block `T_s`? If yes, (B) becomes "rlctAtOn(dlnLoss (H−r) 0) 0 = lambdaCore(H−r)"
    — the SAME reduced-loss-RLCT identity the gauge-slice route produces. If the chart's `q` is NOT the
    clean reduced loss (e.g. it's the reduced loss PLUS chart cross-terms), is the difference RLCT-
    irrelevant (germ-locally same zero-set / same Newton polytope) or does it genuinely change the core?
Q2. Is `rlctAtOn(dlnLoss M 0) 0 = lambdaCore M` (the reduced-core identity) ALREADY a separate theorem in
    this development (the recursion / R1 machinery computes lambdaCore), so that the chart route closes
    #44 by CITING it — or is that identity ALSO open / IS effectively #44 at smaller width (so the chart
    just shifts the wall down a level)?
Q3. The chart gives `rlctAt = rlctAtOn(...)` as an EQUALITY (both ≤ and ≥) only if Φ is a genuine local
    diffeo with the residual form holding as a germ identity (f =ᶠ F∘Φ). The §SEL producer was built to
    give the `≥`-leg of a COMPARISON (rlctAt deepest ≤ rlctAt v) CONSUMING #44 as `hDeepest`. Does the
    chart actually yield the ABSOLUTE deepest value as an equality, or only one inequality direction?
    (If only ≤, #44 needs the matching ≥ — is that the hard half?)
Q4. VERDICT: BOUNDED-via-chart (#44 = chart + quasi-split + a CITED reduced-core identity, modest LoC) vs
    RESEARCH-WALL (the chart route reopens the gauge-slice or an open recursion, no easier than the heavy
    route). If bounded, the minimal lemma chain. If wall, the one obstruction that doesn't dissolve.

Adversarial: I suspect the chart elegantly delivers (A) but (B) just renames the heavy content (the
reduced-core RLCT = lambdaCore is the actual mathematical work, and the chart doesn't compute it). Tell me
if that suspicion is right, or if there's a genuine reduction I'm missing (e.g. the deepest residual being
exactly a smaller-width deepest loss makes #44 INDUCTIVE on width via the chart — which WOULD be a real
win). Findings only, no Lean.

warning: Model metadata for `gpt-5-codex` not found. Defaulting to fallback metadata; this can degrade performance and cause issues.
exec
/bin/bash -lc ls in /tmp/p44-scope
 succeeded in 0ms:
AGENTS.md
CLAUDE.md
README.md
ROADMAP.md
TEMPLATE.md
docs
expeditions
lean
p44-reachability-answer.md
p44-reachability-prompt.md
paper-sources
theory
threads

  → Review SEL chart and deepest point assets
  • Check status of reduced-core RLCT results
  • Synthesize verdict with reasoning
exec
/bin/bash -lc 'ls docs' in /tmp/p44-scope
 succeeded in 0ms:
decorrelated-records
expositions
policies

exec
/bin/bash -lc 'rg "SEL"' in /tmp/p44-scope
 succeeded in 124ms:
expeditions/2026-06-18-voigt-discharge/synthesis.md:  **degeneration** (L6.1+L6.2) — the Abeasis–Del Fra theorem the PAPER ITSELF only cites; genuine new content.
expeditions/2026-06-18-voigt-discharge/synthesis.md:theorem the SOURCE PAPER ITSELF cites (Abeasis–Del Fra / Lakshmibai–Magyar) — closes the geometry in modules,
expeditions/2026-06-18-voigt-discharge/synthesis.md:**hA UNBLOCKED** (thread 39, reviewer + decorrelated Codex, commit e2306f0): Codex produced a SELF-COMPILED
expeditions/2026-06-25-theta-components/threads/13-smoothness-S1/codex/jacobian-stdout.log:/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/synthesis.md:938:- **The L2 producer is now at a STABLE, fully-banked checkpoint.** Clean bricks (all axiom-clean): PIN1, PIN2 + the Score squeeze, the rectangular LDU, the germ bridge, E1, the split smooth-affine chart, the Ψ lenses, the abstract diffeo bridge, the triangular-normalizer Core lemma. The producer's remaining sorries are PRECISELY roadmapped as the general-L frontier (the (1a) IsDeepLayers strengthening for the L=2 diffeo + the L≥3 interior). The 12-catch producer-fold push is COMPLETE at this checkpoint — no green-but-wrong.
expeditions/2026-06-25-theta-components/threads/13-smoothness-S1/codex/jacobian-stdout.log:/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/synthesis.md:945:- **CONSOLIDATION — the producer fold reaches a stable, honestly-documented checkpoint.** Clean bricks ALL banked + axiom-clean: PIN1, PIN2 + the Score squeeze (`deepest_loss_squeeze` axiom-clean), the rectangular LDU, the germ bridge, E1, the split smooth-affine chart, the lenses, the abstract diffeo bridge, the triangular normalizer Core lemma. The producer's remaining sorries are PRECISELY roadmapped as the general-L frontier: 2896 (L2-diffeo via the (1a) IsDeepLayers strengthening), 3099/3104 (L≥3 hinterface, Item 19), 3270 (L≥3 hstep2, Item 24). The 12-catch producer-fold push concludes at a clean checkpoint — NOT a green-but-wrong close.
expeditions/2026-06-25-theta-components/threads/13-smoothness-S1/codex/jacobian-stdout.log:/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/r1-route-B-refuted.md:75:PRECISELY FOR the blow-up. A blow-up chart is non-injective with Jacobian vanishing on the exceptional
expeditions/2026-06-20-aoyagi-full/lessons.md:Mathlib gap dissolved. Then pp started writing "R1 is medium" — and CAUGHT ITSELF, pressure-tested R1.6 (the
expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/certificate-decoder-fix.md:   - The pivot `p` maps to ITSELF (`pivotBlowupOn … p`: `if i = p then x p`), scaling the FIXED-1
expeditions/2026-06-20-aoyagi-full/threads/24-r1-hfin-design/hfin-design-certificate.md:drops coords ⟹ `det ≡ 0`, `phi334`'s failure). The pivot blow-up `a = u·â` is PRECISELY what resolves
expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/codex/bcd-prompt.md:  `|x p|^{#E entries}` = `|x p|^{minAdm}`?? But target is `minAdm-1`. The pivot coord x p ITSELF is one of
expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/h2-joint-psi-cert.md:  PRECISELY the E2 solution: compute
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:The constructor leg of the D1 `hchart` (Altitude-B, spec §SEL): from a `C¹` map `Φ : E → E` (`E` a
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:(continuity + `ContinuousAt.eventually_ne` + compact-ball inf/sup). This is the §SEL "denominator-D
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean:§SEL selected-minor map) and `F = ∑s² + ∑q²` (the post-chart loss). -/
expeditions/2026-06-23-fibre-codim/threads/26-fibre-dim-fibration/codex/run.log:   singularities). What is the cleanest SELF-CONTAINED argument (Gröbner / standard monomial basis / a
expeditions/2026-06-23-fibre-codim/threads/18-deep-chart-ring/codex/fidelity-review-prompt.md:   inequality be TRUE-BUT-USELESS / reversed?
expeditions/2026-06-20-aoyagi-full/threads/wall2-clean-chart/codex/architecture-prompt.md:   free u's — using `paramsEquivFlat` ITSELF as the reshape so that the "which u goes where" is delegated to
expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/codex/l2wire-hptri-route-prompt.md:2. If (b): state PRECISELY the equality that must hold (Score-via-triangular = Score-via-producer) and
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:The network-free real-analysis lemma the D1 (★) `≥`-leg rests on (spec §SEL, the LIGHTER
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:    spec §SEL): a single mean-value Lipschitz bound `‖q(s,t) − q(0,t)‖ ≤ L·‖s‖` on a ball gives
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:/-- **The slice comparison from one vector Lipschitz bound** (the §SEL vector triangle). For a
lean/DLNFibre/DLN/RLCT/Foundations/S1IFTProducer.lean:is the constant comparison, and the §SEL vector triangle gives it from a single Lipschitz bound. -/
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-prompt.md:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:./genfree-strategy-prompt.md:44:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:./genfree-strategy-answer.md:59:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:./genfree-strategy-prompt.md:44:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-23-fibre-codim/threads/30-generic-freeness/codex/genfree-strategy-answer.md:./genfree-strategy-answer.md:59:   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/codex/r2-frontpivot-answer.md:   columns occupy that corner changes which entries are compared to `1`. The SELECTED expression
expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/hproducer-verdict.md:   columns occupy that corner changes which entries are compared to `1`. The SELECTED expression
expeditions/2026-06-18-voigt-discharge/threads/09-L4d-affine-domain-dim/codex/route-prompt.md:   QUESTION 3 (the catenary worry): does (**) ITSELF secretly need catenary-ness of R beyond what
expeditions/2026-06-20-aoyagi-full/threads/20-r1-route-adjudication/scripts/hnode_geometry_careful.py:The reduced G² must be the (1,4) leaf? No — (1,4) leaf is ITSELF smooth (4 squares),
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:132:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:162:./codex/hfin-prompt.md:49:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:252:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:321:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:351:./codex/hfin-prompt.md:49:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-prompt.md:49:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:132:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/iterfibre-run.log:./codex/hfin-run.log:132:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:./codex/hfin-prompt.md:49:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:./codex/hfin-run.log:63:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-run.log:./codex/hfin-prompt.md:49:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/codex/hfin-prompt.md:      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
expeditions/2026-06-20-aoyagi-full/threads/fm3-coord-bridge/codex/readbody-skeleton-prompt.md:(b) the single named gap is PRECISELY the §4 chart obligation (NOT a vacuous `sorry` that smuggles the
expeditions/2026-06-20-aoyagi-full/threads/fm3-coord-bridge/G1-FINAL-build-spec.md:across resumes. Cheaper to either (a) hand it a SELF-CONTAINED task with the current decls inlined, or (b)
expeditions/2026-06-20-aoyagi-full/threads/fm3-coord-bridge/G1-FINAL-build-spec.md:(yes). De-risks the type the general fix-body fills. Built it MYSELF (not via the drift-prone background
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:The §SEL selected-minor IFT-chart producer, WIRED. The banked reductions
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:genuinely-lighter premise the §SEL route identified: the residual is a `C¹` sum of squares
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:(`Foundations.S1IFTProducer`) builds `hF`, `hQ0`, `hR` (definitional) and `hcmp` (the §SEL
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:hypothesis list, replacing them with the single `C¹`-residual premise the §SEL route certified.
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:/-- **The `hAtV` half from a `C¹` first-peel residual** (the §SEL producer wired). At a general
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:/-- **The full D1 per-point `≥` from two `C¹` residuals** (the §SEL producer wired through both
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:  -- the FIRST-peel `hcmp` (the §SEL vector triangle from `q`'s smoothness)
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:SELF-maps (`coreAbsorb` an additive translation homeo — global free; `regStraighten` an `E`-straightening,
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverDispatch.lean:banked `routeMCore_box_diverges_clean`), and leaving the not-yet-built branches as PRECISELY-STATED
lean/DLNFibre/DLN/RLCT/AxCheck.lean:-- D1 §SEL producer (Altitude A, network-free) — must be CLEAN-THREE [propext, Classical.choice,
lean/DLNFibre/DLN/RLCT/AxCheck.lean:-- from ANY C¹ residual `q` (the §SEL collapse to `rlct_quasiSplit_ge`, D-INDEPENDENT — no new Mathlib
lean/DLNFibre/DLN/RLCT/AxCheck.lean:-- reviewer + lean-formaliser §QA). The §SEL win: chart-DATA (hF/hQ0/hcmp) removed from the hyp list.
lean/DLNFibre/DLN/RLCT/AxCheck.lean:-- use-site instantiates with the §SEL selected-minor Φ + the H_indep block-invertible f'.
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:that the `Y1'`-definition is PRECISELY the E2 solution holding `P01` fixed:
expeditions/2026-06-23-fibre-codim/threads/21-residual-math-paths/codex/route-prompt.md:   singularities). What is the cleanest SELF-CONTAINED argument (Gröbner / standard monomial basis / a
expeditions/2026-06-23-fibre-codim/threads/21-residual-math-paths/codex/route-answer.md:   singularities). What is the cleanest SELF-CONTAINED argument (Gröbner / standard monomial basis / a
expeditions/2026-06-23-fibre-codim/threads/15-total-ring-presentation/codex/r2-2-verdict-analysis.md:  R2-2 ITSELF — not R2-3. It needs a certified ideal-transport before grinding.
expeditions/2026-06-23-fibre-codim/threads/15-total-ring-presentation/codex/r2-2-presentation-prompt.md:5. REACHABILITY: M-route module estimate (count) + the single hardest sub-step of R2-2 ITSELF (not
expeditions/2026-06-21-perm-invariance/synthesis.md:- **OPERATING MODE (decided):** the controller writes the q-series Lean tides HIMSELF in voigt-discharge with
expeditions/2026-06-21-perm-invariance/synthesis.md:  commit to `pi-build`; SELF-CHECK `git -C <main> status` clean (no leak to aoyagi) before reporting.
expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/mapeq-nonprefix-prompt.md:A SECOND candidate map (call it phi_ach) is a COMPOSITION OF BLOCK SELF-MAPS of the flat coordinate
expeditions/2026-06-20-aoyagi-full/threads/28-hfin-recStep-spec/scripts/L32a_corank_reconcile.py:the {det R = 0} locus, which is ITSELF a lower-corank determinantal core in the R-variables.
expeditions/2026-06-21-perm-invariance/threads/06-durfee-strategy/scratch/durfee_routes.py:#     RHS(a,b) = P_a P_b? no, that's the claim. We test the SELF-recurrence of the RHS sum:
expeditions/2026-06-20-aoyagi-full/threads/28-hfin-recStep-spec/scripts/o2_q4.py:print("So Q4 'does {det Sc=0} diverge the free-box core below threshold' is answered by the IH ITSELF:")
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g123-scripts/g123_field4_L3.py:# or does the resolved form ITSELF contain a smaller chain core needing recursion (field 4)?
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g129-scripts/g130_fidelity_check.py:NOT the Aoyagi λ. => the split would compute a sound equation about the wrong point — USELESS for the
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/r1-route-B-refuted.md:PRECISELY FOR the blow-up. A blow-up chart is non-injective with Jacobian vanishing on the exceptional
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g156-adjudication-scripts/what_collapse_needs.py:print("PRECISELY what does the box-collapse consume? (the value-CLOSING step in GE)")
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/pp2-g161-confirm/g196_decorrelated_check.py:print(f"     NOT raw gauge coords — a raw-coord squeeze would FALSELY see this fibre point as singular.")
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g152-subchart-route-prompt.md:The cert's content (cross-term ∈ ideal(reg), endpoint leak absorbed into ∑E²) reads to me as PRECISELY a
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g156-soundness-adjudication-certificate.md:Includes a SELF-CORRECTION of Addenda 1-4's implicit "deepest_le covers the box directly" reading.
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g156-soundness-adjudication-certificate.md:**SELF-CORRECTION.** Addenda 1-4 spoke of "the ordering `rlctAtOn(F,deepest) ≤ rlctAtOn(F,v)` via
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g152-sub34-finding.md:## ADDENDUM (after reading weightedThreshold_transport / S1.1) — PARTIAL SELF-CORRECTION
p44-reachability-answer.md:# Scope: is the L2 deepest-point RLCT normal form (#44) reachable via the new §SEL IFT chart?
p44-reachability-answer.md:## The NEW machinery (just built, separately): the §SEL general-`v` IFT chart
p44-reachability-answer.md:Is #44 REACHABLE by applying the §SEL chart AT the deepest point (special case), reducing it to:
p44-reachability-answer.md:Q1. At the DEEPEST point specifically, is the §SEL residual `q(0,·)` literally (or up to a measure-
p44-reachability-answer.md:    diffeo with the residual form holding as a germ identity (f =ᶠ F∘Φ). The §SEL producer was built to
p44-reachability-answer.md:  → Review SEL chart and deepest point assets

exec
/bin/bash -lc "sed -n '1,200p' lean/DLNFibre/DLN/RLCT/Validate/RouteMValue.lean" in /tmp/p44-scope
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMRecursion

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMValue` — the value fold over `routeMIota` (fm3 #103)

The value-side of the Route-M recursion: the `⨅` over the chart family `routeMIota M` of the per-leaf
`monomialThreshold` equals `½·minAdm(M)` (`= lambdaCore`, the CORE). This is the abstract value-fold
WIRING — it reduces the recursion's output to the banked `RouteMState.foldFamily_iInf_eq_half_minAdm`
(which needs ONLY the per-leaf root-anchored `PivotWitness` + one achiever leaf; NO cascade / NO
`RealizableRank` — the cascade-realizability is the #104 DESCENT's geometric soundness, separate).

The recursion accumulates each leaf's `MonoData` via `MonoData.appendDivisor` down the `Σ`-tree, so a leaf's
`data` is `MonoData.foldDivisors (codimsOf path)` for the path's accumulated codims. This file states the
value fold CONDITIONALLY on that accumulation (`hdata`) + the witness data — both supplied by the dispatcher
(`routeStep`'s branch) once it emits the genuine per-cell codims. The accumulation `hdata` + the
achiever-leaf-existence for general `M` is the named gap (rides the rank-pattern read / #104); here is the
value-fold LOGIC that consumes it, abstract over the family.
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The value fold over `routeMIota` (the #103 value-wiring).** Given the recursion-accumulation
`hdata : (routeAtlas M M).data i = foldDivisors (codimsOf i)` (each leaf's `MonoData` is the
`appendDivisor`-fold of its path's codims) + the `foldFamily_iInf` data (every codim a root-anchored
`PivotWitness M`, an achiever leaf `i₀` with `minAdm ∈ codimsOf i₀`, `minAdm ≥ 1`), the `⨅` over the chart
family of the per-leaf `monomialThreshold` is `½·minAdm(M)`. Reduces to
`RouteMState.foldFamily_iInf_eq_half_minAdm` — the value rides ONLY the `PivotWitness` codims (no cascade).
The hypotheses `hdata`/`hwit`/`hbind₀` are what `routeStep`'s branch supplies (the named gap); this is the
value-fold logic, abstract over the family.

**Root-anchoring (the codims fidelity point, fm3 decl-check).** `hwit` requires each path codim to be a
`PivotWitness M` — i.e. `codim = (Mval M T).toNat` for `T ∈ Adm M` at the FIXED ROOT `M`, NOT the reduced
node's `minAdm`. This is load-bearing for `(C≥)`: a reduced node's `minAdm` UNDERSHOOTS (it can be `< minAdm
M`), which would break the lower bound. Worked anchors (decl-checked): `(2,2,2)` chain `→(1,1,2)→(0,0,2)`
(2 branch nodes), `codimsOf = [Mval(2,2,2)(0,0)=4, Mval(2,2,2)(1,0)=3=minAdm]`, fold `min(2,3/2)=3/2`;
`(3,2,3)` chain `→(2,1,3)→(1,0,3)` (2 branch nodes), `codimsOf = [6, 5]` (BOTH root `Mval(3,2,3) T`:
`Mval(1,0)=5=minAdm` the achiever, `Mval(0,0)=Mval(2,0)=6`; NOT the reduced `minAdm(2,1,3)=2`), fold
`min(3, 5/2)=5/2`. The `PivotWitness M` type enforces the root-anchoring; this lemma consumes it. -/
theorem routeM_value_eq (M : Fin (L + 1) → ℕ) (codimsOf : routeMIota M → List ℕ)
    (hdata : ∀ i, (routeAtlas M M).data i = MonoData.foldDivisors (codimsOf i))
    (hm₀ : 1 ≤ ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat)
    (hwit : ∀ i, ∀ c ∈ codimsOf i, PivotWitness M c)
    (i₀ : routeMIota M) (hbind₀ : ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat ∈ codimsOf i₀) :
    (⨅ i : routeMIota M, monomialThreshold (routeD M i) (routeK M i) (routeH M i))
      = ((((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat : ℝ≥0∞)) / 2 := by
  have hrw : ∀ i : routeMIota M,
      monomialThreshold (routeD M i) (routeK M i) (routeH M i)
        = monomialThreshold (MonoData.foldDivisors (codimsOf i)).d
            (MonoData.foldDivisors (codimsOf i)).k (MonoData.foldDivisors (codimsOf i)).h := by
    intro i
    unfold routeD routeK routeH
    rw [hdata i]
  rw [iInf_congr hrw]
  exact foldFamily_iInf_eq_half_minAdm M codimsOf hm₀ hwit i₀ hbind₀

end DLNFibre.DLN.RLCT

  ✓ Review SEL chart and deepest point assets
  ✓ Check status of reduced-core RLCT results
  → Synthesize verdict with reasoning
exec
/bin/bash -lc 'rg "rlctAtOn (.*lambdaCore" -n lean/DLNFibre' in /tmp/p44-scope
 exited 2 in 0ms:
rg: regex parse error:
    (?:rlctAtOn (.*lambdaCore)
    ^
error: unclosed group

exec
/bin/bash -lc 'rg "lambdaCore" lean/DLNFibre/DLN/RLCT/Validate -n' in /tmp/p44-scope
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:90:`nReg/2 + ofReal(lambdaCore M)` — the Skeleton `deepest_regular_core_normal_form` target. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:110:        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:113:        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivot.lean:144:        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:40:`lambdaCore = 0`; the headline stays NON-STRICT / paper-faithful `r ≤ min`, audit-verified true). The
lean/DLNFibre/DLN/RLCT/Validate/RouteMGeneralAssembly.lean:33:`⨅` over `routeMIota M` of the per-leaf `monomialThreshold` is `½·minAdm(M) = lambdaCore`. Reduces to the
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:25:- `routeLayerAtlas_value_eq_lambdaCore` — `⨅ monomialThreshold = ofReal(lambdaCore M)` over the
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:32:lane (`= ½·minAdm = lambdaCore`) but whose `rlctAtOn = ⨅` content is the ANALYTIC COVER: the two
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:122:/-! ## The migrated value lane: `⨅ monomialThreshold = ofReal(lambdaCore M)` -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:125:layer-collapsing chart family of the per-leaf `monomialThreshold` is `ofReal(lambdaCore M)` (for
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:131:theorem routeLayerAtlas_value_eq_lambdaCore (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:133:      = ENNReal.ofReal (lambdaCore M : ℝ) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:149:`resolution_charts` is `rlctAtOn(core) = ⨅ monomialThreshold`. The VALUE (`= ½·minAdm = lambdaCore`)
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:178:`⨅ monomialThreshold = ½·minAdm(2,2,2) = 3/2 = lambdaCore(2,2,2)`, confirming the lane is
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:181:theorem routeLayerAtlas_value_eq_lambdaCore_M222 :
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:8:RECURSION route to `rlctAtOn (dlnLoss M 0) 0 = ofReal (lambdaCore M)` (`= ½·minAdm`), iterating the
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:23:The COMBINATORIAL arithmetic (`lambdaCore M = nReg M / 2 + lambdaCore (redOf M)`, with `lambdaCore` of a
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:24:degenerate state `= 0`) makes the value telescope `lambdaCore M = ∑ nReg_k / 2` close; the GEOMETRIC
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:43:combinatorial telescope `harith` (`lambdaCore M = nReg M / 2 + lambdaCore (redOf M)`, with the degenerate
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean:45:(lambdaCore M)`. Proved by strong recursion on `chainWidthSum` (`redOf` strictly decreases `ΣM`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:16:`ofReal(lambdaCore M)`. Folding the core value `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` is
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:17:**R1** (`resolution_charts` + A1), kept separate (the gauge chart carries no `lambdaCore`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:519:chart's full content: it carries NO `lambdaCore` (R1's value `rlctAtOn (dlnLoss M 0) 0 =
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:520:ofReal(lambdaCore M)` is folded separately). Assembled from the chart-existence (#44c) + the transport
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1033:`deepest_regular_core_normal_form` (Skeleton.lean:1124) wants `nReg/2 + ofReal(lambdaCore M)`. The
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1034:gap is exactly the **R1 core-value** `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1035:`resolution_charts` + A1's `lambdaCore_eq_clean`/`⨅ monomialThreshold = lambdaCore` — R1's lane, in
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1042:R1 core-value `hcore : rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's lane) and the
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1044:regular shift `nReg/2` plus the closed-form core `ofReal(lambdaCore M)` — the exact
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1055:      = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1063:        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:60:/-- `minAdm(M334) = 8` (so `lambdaCore(3,3,4) = 4`, matching the published RRR closed form). -/
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:84:lambdaCore(3,3,4)`. This is the BINDING coupled `diag(b)` witness (cert `verify-r1-diagb-334.md`): a per-row
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:131:`2` (`minAdm = 4`, `lambdaCore = 2`). So `(4,4,2,2)` exercises the corank-2 mechanism on a NON-binding
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:160:/-- `minAdm(M4422) = 4` (so `lambdaCore(4,4,2,2) = 2`, NOT `7/2` — the certificate's correction). -/
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:182:minAdm`), the `⨅` of the `foldDivisors` thresholds is `½·minAdm = ½·4 = 2 = lambdaCore(4,4,2,2)`. The `min`
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:253:/-- `minAdm(M3354) = 8` (so `lambdaCore(3,3,5,4) = 4`); the minimiser `T=(1,1,0)` is unique. -/
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean:273:`½·minAdm = ½·8 = 4 = lambdaCore(3,3,5,4)`. The deep-sharing `L=3` witness (cert §6): the committed
lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:326:branch-divisors (`[4,3]` for `(2,2,2)` → `3/2`). This is the COMBINATORIAL `½·minAdm` (`= lambdaCore`, the
lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:338:   (`aoyagiLambda = nReg/2 + lambdaCore`; L2's `nReg/2` on a non-degenerate root, `#70` on a degenerate root).
lean/DLNFibre/DLN/RLCT/Validate/Case323RouteStep.lean:43:/-- `minAdm(M323) = 5` (so `lambdaCore(3,2,3) = 5/2`). -/
lean/DLNFibre/DLN/RLCT/Validate/Case323RouteStep.lean:66:is `½·minAdm = 5/2 = lambdaCore(3,2,3)`. The asymmetric SECOND anchor corroborating `case222_routeStep_value`
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:71:`coreDeepest = ofReal(lambdaCore (square m))`, `a + b ≤ m`):
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:91:    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
lean/DLNFibre/DLN/RLCT/Validate/D1IFTResidualProducer.lean:110:        = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:13:Cover #21 (`resolution_value_of_atlas`) then closes `⨅ = ofReal(lambdaCore M)`. Core-only.
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:77:give `∫⁻_U < ⊤` (`rlctAtOn_ge_of_integral_lt`). Mechanism-independent. `⨅ = ofReal(lambdaCore M)` is
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:18:`resolution_value_of_atlas` takes the atlas and proves `⨅ monomialThreshold = ofReal(lambdaCore M)`
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:19:SORRY-FREE + S2-FREE: `le_antisymm` ((C≥) ⟹ `⨅ ≥ ½·m₀`, (C=∃) ⟹ `⨅ ≤ ½·m₀`), then `½·m₀ = lambdaCore M`
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:20:definitionally (`lambdaCore := ½·inf' Mval`). The geometric residual is isolated entirely into the
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:130:lands definitionally on `lambdaCore M = ½·m₀`. -/
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:144:/-- `lambdaCore M = ½·(inf' Mval).toNat` as an `ℝ≥0∞` fact: the `ℚ`-valued `lambdaCore` cast through
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:147:theorem ofReal_lambdaCore_eq_half_inf (M : Fin (L + 1) → ℕ) :
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:148:    ENNReal.ofReal (lambdaCore M : ℝ)
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:155:  -- LHS: ofReal(lambdaCore) = ofReal((I.toNat : ℝ)/2).
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:156:  have hL : ENNReal.ofReal (lambdaCore M : ℝ) = ENNReal.ofReal ((I.toNat : ℝ) / 2) := by
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:157:    unfold lambdaCore
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:193:the chart monomial thresholds equals `ofReal(lambdaCore M)`. Sorry-free + S2-free, conditional on the
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:195:`⨅ ≤ ½·m₀` (`iInf_le`); then `½·m₀ = ofReal(lambdaCore M)` definitionally (`ofReal_lambdaCore_eq_half_inf`).
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:200:    (⨅ i : ι, monomialThreshold (d i) (k i) (h i)) = ENNReal.ofReal (lambdaCore M : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:201:  rw [ofReal_lambdaCore_eq_half_inf]
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:209:admissible stratum `Adm = {0}`, `Mval 0 = 1`, so `m₀ = 1` and `lambdaCore = ½`) a one-path atlas
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:237:/-- The non-vacuity value: the `M = ![1,1]` atlas yields `⨅ monomialThreshold = ofReal(lambdaCore)`
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:240:    = ENNReal.ofReal (lambdaCore (![1, 1] : Fin 2 → ℕ) : ℝ) :=
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:317:`nReg/2 + lambdaCore(1,1,2) = 2/2 + 1/2 = 3/2`. The reduced `(1,1,2)` RLCT `= 1/2` (the cert's
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean:318:`lambdaCore(1,1,2)`, the recursion's child value) enters as the hypothesis `hred` — deferred, not
lean/DLNFibre/DLN/RLCT/Validate/Case222Value.lean:8:shapes, and **every** leaf threshold is `3/2 = ½·Mval(deepest rank-1 stratum) = lambdaCore (2,2,2)`:
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:638:`⨅ monomialThreshold = ½·minAdm(2,2,2) = 3/2 = lambdaCore(2,2,2)` — fires on the worked anchor, confirming
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteStep.lean:9:`3/2 = lambdaCore(2,2,2)`. This de-risks the committed type WITHOUT touching the general `routeStep` body
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteStep.lean:48:/-- `minAdm(M222) = 3` (so `lambdaCore(2,2,2) = 3/2`). -/
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteStep.lean:72:is `½·minAdm = 3/2 = lambdaCore(2,2,2)`. Consumes the banked `foldFamily_iInf_eq_half_minAdm` — validating
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:11:`redOf := schurStateRed`, `nRegOf := bindNReg`, `lamOf := lambdaCore`,
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:15:`bindNReg M := 2·(lambdaCore M − lambdaCore (schurStateRed M))` makes `harith_step` an UNCONDITIONAL `ring`
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:16:identity. The monotonicity `lambdaCore (schurStateRed M) ≤ lambdaCore M` survives only in `hnReg`
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:19:`(minAdm M − minAdm (schurStateRed M) : ℚ)` (`2·lambdaCore = (Adm).inf'`, the ℤ minimal codim).
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:27:/-- The per-node regular count as a ℚ-difference of `lambdaCore`s: `2·(λ M − λ (schurStateRed M))`. Equals
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:30:  2 * (lambdaCore M - lambdaCore (schurStateRed M))
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:32:/-- **`harith_step` — the telescope step (UNCONDITIONAL in ℚ).** `lambdaCore M = bindNReg M / 2 +
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:33:lambdaCore (schurStateRed M)`. Pure ring identity. No monotonicity needed (the ℚ relief). -/
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:35:    lambdaCore M = bindNReg M / 2 + lambdaCore (schurStateRed M) := by
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:38:/-- A leaf node has `lambdaCore = 0`: `isLeafNode` gives `inf' Mval ≤ 0` (via `Int.toNat_eq_zero`), and
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:39:`inf' ≥ 0` (admissible `Mval ≥ 0`), so `inf' = 0` and `lambdaCore = ½·0 = 0`. -/
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:40:theorem lambdaCore_eq_zero_of_isLeafNode (M : Fin (L + 1) → ℕ) (hleaf : isLeafNode M) :
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:41:    lambdaCore M = 0 := by
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:47:  unfold lambdaCore; rw [h0]; ring
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:50:`lambdaCore (schurStateRed M) = 0`, so `lambdaCore M = bindNReg M / 2`. The `#70`-base level (one above the
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:53:    lambdaCore M = bindNReg M / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:54:  rw [bind_harith_step M, lambdaCore_eq_zero_of_isLeafNode _ hleaf, add_zero]
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:63:/-- **`hlam` — `lambdaCore ≥ 0`.** `lambdaCore M = ½·inf' Mval ≥ 0` (admissible `Mval ≥ 0` ⟹ `inf' ≥ 0`). -/
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:64:theorem bind_hlam (M : Fin (L + 1) → ℕ) : 0 ≤ lambdaCore M := by
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:65:  unfold lambdaCore
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:71:≥ 0 ⟺ λ (schurStateRed M) ≤ λ M` — the monotonicity of `lambdaCore` under the `schurState` width-reduction
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:75:    (hMono : lambdaCore (schurStateRed M) ≤ lambdaCore M) :
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:81:(`MinAdmMono.lambdaCore_schurStateRed_le`, #149 — the running-min-cap cone-transform), so the binding
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean:84:  bind_hnReg M (lambdaCore_schurStateRed_le M)
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:13:> `rlctOf M = ofReal (lambdaCore M)`   ( `= ½·minAdm`, the value cobuild's L2-Skeleton bridge consumes)
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:17:monotonicity `hMono` (`lambdaCore (schurStateRed M) ≤ lambdaCore M`, rs-grind's #149 — carried here as a
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:38:equals the combinatorial value: `rlctOf M = ofReal (lambdaCore M)`.
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:41:`lamOf := lambdaCore`, `degenChild := fun M => isLeafNode (schurStateRed M)`, discharging the combinatorial
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:44:theorem binding_rlct_eq_lambdaCore_of_hstep
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:46:    (hMono : ∀ M : Fin (L' + 1 + 1) → ℕ, lambdaCore (schurStateRed M) ≤ lambdaCore M)
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:52:    rlctOf M = ENNReal.ofReal (lambdaCore M) :=
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:54:    schurStateRed bindNReg lambdaCore rlctOf (fun M => isLeafNode (schurStateRed M))
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:64:meeting-point — `hMono` discharged). Since `#149` is now PROVEN (`MinAdmMono.lambdaCore_schurStateRed_le`,
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:67:`rlctOf M = ofReal (lambdaCore M)` hangs on EXACTLY the two geometric obligations fm3 owns — the per-node
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:71:theorem binding_rlct_eq_lambdaCore_of_hstep'
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:78:    rlctOf M = ENNReal.ofReal (lambdaCore M) :=
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:79:  binding_rlct_eq_lambdaCore_of_hstep rlctOf
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean:80:    (fun M => lambdaCore_schurStateRed_le M) hstep hbase M
lean/DLNFibre/DLN/RLCT/Validate/MinAdmMono.lean:262:/-- **`hMono` — `lambdaCore (schurStateRed M) ≤ lambdaCore M`** (the binding-arithmetic monotonicity, #149).
lean/DLNFibre/DLN/RLCT/Validate/MinAdmMono.lean:264:theorem lambdaCore_schurStateRed_le (M : Fin (L + 1) → ℕ) :
lean/DLNFibre/DLN/RLCT/Validate/MinAdmMono.lean:265:    lambdaCore (schurStateRed M) ≤ lambdaCore M := by
lean/DLNFibre/DLN/RLCT/Validate/MinAdmMono.lean:266:  unfold lambdaCore
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:18:`L = 1` core `lambdaCore (H−r)`, where at one reduced layer `lambdaCore M = M⁰·M¹/2`) closes the
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:201:/-- **`lambdaCore` at `L = 1`.** A single reduced layer has the all-zero exponent vector as its only
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:202:admissible `T` (the last-exponent constraint forces `T 0 = 0`), so `lambdaCore M = M⁰·M¹/2`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:203:theorem lambdaCore_L1 (M : Fin (1 + 1) → ℕ) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:204:    lambdaCore (L := 1) M = (1 / 2 : ℚ) * ((M 0 * M (Fin.last 1) : ℕ) : ℚ) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:205:  unfold lambdaCore
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:240:`lambdaCore (H−r)`. At `L = 1` both reduce to the single full block `H⁰·H¹/2`
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:241:(`= r(H⁰+H¹−r)/2 + (H⁰−r)(H¹−r)/2`, the latter being `lambdaCore (H−r)`). Proven sorry-free:
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:242:`rlctAt_dlnLoss_L1` (the full-block RLCT) + `lambdaCore_L1` (the core arithmetic) + the
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:249:        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:251:  -- right side: nReg/2 + ofReal(lambdaCore (H-r)).  Show both = (H0*H1)/2.
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:254:  -- lambdaCore (H-r) = (H0-r)(H1-r)/2 ≥ 0
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:256:  have hMcore : lambdaCore (L := 1) M = (1 / 2 : ℚ) * ((M 0 * M (Fin.last 1) : ℕ) : ℚ) :=
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:257:    lambdaCore_L1 M
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:262:  have hcoreReal : (lambdaCore (L := 1) M : ℝ) = ((M 0 * M (Fin.last 1) : ℕ) : ℝ) / 2 := by
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean:265:  have hcoreENN : ENNReal.ofReal (lambdaCore (L := 1) M : ℝ)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:22:    rlctAtOn R 0 = extra/2 + lambdaCore(M'),   extra = m(a+b) − ab,  M' = (m−a, m−a−b, m−b),
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:25:needs the **self-contained arithmetic** `extra/2 + lambdaCore(M') ≥ lambdaCore(square m)` (the
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:26:deepest reduced widths at L = 2 are the square `(m, m, m)`; `coreDeepest = lambdaCore(square m)`),
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:28:(`extra_half_add_lambdaCore_Mprime_ge_square`, sorry-free, clean-three) via the banked symbolic
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:62:`extra/2 + lambdaCore(M') ≥ lambdaCore(square m)`, `extra = m(a+b) − ab`,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:172:/-- **§6 — the self-contained arithmetic lemma.** `extra/2 + lambdaCore(M') ≥ lambdaCore(square m)`
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:174:square `(m, m, m)`, so `coreDeepest = lambdaCore (square m)`. Pure `Mval`/`Adm`/`Finset.inf'`
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:178:theorem extra_half_add_lambdaCore_Mprime_ge_square (m a b : ℕ) (hab : a + b ≤ m) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:179:    lambdaCore (squareWidths m)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:180:      ≤ (extraCount m a b : ℚ) / 2 + lambdaCore (MprimeWidths m a b) := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:200:  -- lift the `ℤ` inequality through `lambdaCore = (1/2)·(inf' Mval)`
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:201:  rw [lambdaCore, lambdaCore, ← hIsq, ← hIp]
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:205:/-- `lambdaCore M ≥ 0` (admissible `Mval ≥ 0` on the cone ⟹ `inf' ≥ 0`). Reuses the banked
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:207:theorem lambdaCore_nonneg_L2 (M : Fin 3 → ℕ) : 0 ≤ lambdaCore M := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:208:  rw [lambdaCore]
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:214:`coreDeepest = ofReal(lambdaCore (square m))` and the degraded-core value `ofReal(lambdaCore M')`,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:216:    coreDeepest ≤ (extra : ℝ≥0∞)/2 + ofReal(lambdaCore M').
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:218:Bridges the `ℚ` lemma through `ENNReal.ofReal` (both `lambdaCore`s nonneg; `(extra:ℝ≥0∞)/2 =
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:220:theorem coreDeepest_le_extra_half_add_lambdaCore_Mprime (m a b : ℕ) (hab : a + b ≤ m) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:221:    ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:223:        + ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:224:  have hQ := extra_half_add_lambdaCore_Mprime_ge_square m a b hab
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:226:  have hsqnn : (0 : ℚ) ≤ lambdaCore (squareWidths m) := lambdaCore_nonneg_L2 _
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:227:  have hpnn : (0 : ℚ) ≤ lambdaCore (MprimeWidths m a b) := lambdaCore_nonneg_L2 _
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:237:  have hQR : (lambdaCore (squareWidths m) : ℝ)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:238:      ≤ (extraCount m a b : ℝ) / 2 + (lambdaCore (MprimeWidths m a b) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:255:ofReal(lambdaCore M')`. Combined with the §6 arithmetic
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:256:(`coreDeepest_le_extra_half_add_lambdaCore_Mprime`)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:257:and `coreDeepest = ofReal(lambdaCore (square m))`, this gives `coreDeepest ≤ rlctAtOn R t0` — the
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:266:degraded-core value `hDegraded : rlctAtOn R₂ t0₂ = ofReal(lambdaCore M')` (the §5 interface
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:268:`coreDeepest = ofReal(lambdaCore (square m))`,
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:276:    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:287:    (hDegraded : rlctAtOn R₂ t0₂ = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:297:  exact coreDeepest_le_extra_half_add_lambdaCore_Mprime m a b hab
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:316:`dlnLoss M 0` at the origin `(0 : Params M)` has local RLCT `ofReal(lambdaCore M)`. The
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:324:      = ENNReal.ofReal (lambdaCore M : ℝ)
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:336:      = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ) :=
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:350:(square deepest reduced widths `M = (m,m,m)`, `coreDeepest = ofReal(lambdaCore (square m))`), given
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:363:    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean:386:    (hDegraded : rlctAtOn R₂ t0₂ = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:17:  `rlctAt H (dlnLoss H B) deepestPoint = nReg/2 + rlctAtOn(dlnLoss M 0) 0` (core RLCT, NOT `lambdaCore`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:20:- **`hRValue`** — R1's value `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)` (= `resolution_charts`
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:21:  ▸ A1 `lambdaCore_eq_clean`; cover wires the Skeleton `resolution_charts`, A1 supplies the value
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:26:`rlctAt H (dlnLoss H B) deepestPoint = nReg/2 + ofReal(lambdaCore M)`. Proof = the value-free
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:40:(`rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`), the local RLCT at the deepest point IS the
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:41:closed-form value `nReg/2 + ofReal(lambdaCore M)` — the Skeleton `deepest_regular_core_normal_form`
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:62:        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)) :
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean:65:        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMValue.lean:7:`monomialThreshold` equals `½·minAdm(M)` (`= lambdaCore`, the CORE). This is the abstract value-fold

  ✓ Review SEL chart and deepest point assets
  ✓ Check status of reduced-core RLCT results
  ✓ Synthesize verdict with reasoning
exec
/bin/bash -lc 'rg "sorry" lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean' in /tmp/p44-scope
 succeeded in 0ms:
carrier (whose general `branch` arm is the documented `sorry` in `RouteMRecursion.lean` — the
atlas `routeLayerAtlas` (`RouteMLayerSplit.lean`, 0 sorry). This file is PARALLEL: it does not
## What this banks (sorry-free, axioms = the single S2 `monomial_rlct`)
  `_achiever` + `monomialThreshold_singleton`. Replaces the `sorryAx`-tainted
/-! ## The `IsResolutionAtlas` instance from the layer atlas (the value clauses, sorry-free)
`sorryAx`-tainted `routeMGeneralValue` only delivered conditionally on the open `routeStep`
`routeMGeneralValue`/`routeM_value_eq` fold over `routeMIota M` (which inherited `sorryAx` through

exec
/bin/bash -lc 'rg "sorry" lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean' in /tmp/p44-scope
 succeeded in 0ms:
three are **worse than this `sorry`**, so it is left named. The certified body needs three Core-level pieces
are CONCRETE; the **single remaining gap** (fm3-authorized named `sorry`, NOT faked) is the GENERAL branch
    -- The layer-collapsing carrier + recursion + value-fold + descent are BANKED there (0 sorry, axioms =
    -- the documented blocker; the genuine machinery is sorry-free in `RouteMLayerSplit`.
    sorry

exec
/bin/bash -lc 'rg "sorry" lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean' in /tmp/p44-scope
 exited 1 in 0ms:
exec
/bin/bash -lc "nl -ba lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean | sed -n '80,220p'" in /tmp/p44-scope
 succeeded in 0ms:
    80	    (F : (Fin m → ℝ) × Y → ℝ) (Q : (Fin m → ℝ) × Y → ℝ) (R : Y → ℝ) (t0 : Y)
    81	    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), t0))
    82	    (hF : ∀ p, F p = (∑ i, p.1 i ^ 2) + Q p)
    83	    (hQ0 : ∀ p, 0 ≤ Q p) (hFmeas : Measurable F)
    84	    (hR : ∀ t, R t = Q (0, t)) (hRmeas : Measurable R)
    85	    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U), R z ≠ 0)
    86	    (C : ℝ) (hC : 0 < C)
    87	    (hcmp : ∃ U ∈ 𝓝 ((0 : Fin m → ℝ), t0), ∀ p ∈ U,
    88	        (∑ i, p.1 i ^ 2) + R p.2 ≤ C * F p) :
    89	    (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v := by
    90	  rw [hchart]
    91	  exact rlct_quasiSplit_ge F Q R t0 hF hQ0 hFmeas hR hRmeas hRne C hC hcmp
    92	
    93	/-- **PART (a) → D1 per-point `≥`** (the (★) close MODULO the two producer obligations). Wiring
    94	`rlctAt_ge_nReg_add_slice` (the `hAtV` side) through banked `deepest_le_of_optimal_via_L2_ge`: with
    95	the deepest-side equality `hDeepest` (banked via `deepest_regular_core_normal_form`, #44) and the
    96	leading-form comparison `hCore : coreDeepest ≤ rlctAtOn R t0` (PART (b)), the deepest point has
    97	`≤` local RLCT than `v`: `rlctAt (dlnLoss H B) deepest ≤ rlctAt (dlnLoss H B) v`. This is the
    98	`rlctAt_deepest_le_of_optimal` per-point conclusion, reduced to EXACTLY: (i) the IFT-chart producer,
    99	(ii) `hDeepest` (= #44), (iii) `hCore` (the leading-form comparison). The `nReg/2` shift cancels. -/
   100	theorem deepest_le_of_optimal_chart {L m : ℕ} {Y : Type*}
   101	    [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
   102	    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y]
   103	    (H : Fin (L + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
   104	    (deepest v : Params H)
   105	    (F : (Fin m → ℝ) × Y → ℝ) (Q : (Fin m → ℝ) × Y → ℝ) (R : Y → ℝ) (t0 : Y)
   106	    (coreDeepest : ℝ≥0∞)
   107	    (hDeepest : rlctAt H (dlnLoss H B) deepest = (m : ℝ≥0∞) / 2 + coreDeepest)
   108	    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin m → ℝ), t0))
   109	    (hF : ∀ p, F p = (∑ i, p.1 i ^ 2) + Q p)
   110	    (hQ0 : ∀ p, 0 ≤ Q p) (hFmeas : Measurable F)
   111	    (hR : ∀ t, R t = Q (0, t)) (hRmeas : Measurable R)
   112	    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U), R z ≠ 0)
   113	    (C : ℝ) (hC : 0 < C)
   114	    (hcmp : ∃ U ∈ 𝓝 ((0 : Fin m → ℝ), t0), ∀ p ∈ U,
   115	        (∑ i, p.1 i ^ 2) + R p.2 ≤ C * F p)
   116	    (hCore : coreDeepest ≤ rlctAtOn R t0) :
   117	    rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
   118	  have hAtV : (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v :=
   119	    rlctAt_ge_nReg_add_slice H B v F Q R t0 hchart hF hQ0 hFmeas hR hRmeas hRne C hC hcmp
   120	  exact deepest_le_of_optimal_via_L2_ge (B := B) H r (rlctAt H (dlnLoss H B) deepest)
   121	    (rlctAt H (dlnLoss H B) v) m coreDeepest (rlctAtOn R t0) hDeepest hAtV hCore
   122	
   123	/-! ## PART (b) interface — the slice-residual ↦ core RLCT identification (`hCore` discharge)
   124	
   125	The G1 verify-first (decorrelated pen-and-paper, EXACT algebra, L=2, r∈{1,2,3}, reduced widths
   126	M∈{(1,1,1),(2,2,2),(1,2,1),(2,1,2),(3,3,3)} + Codex xhigh) found the slice residual to be EXACTLY
   127	
   128	    R = ‖ T₁·(I_{M₁} + G)·T₂ ‖²_F,   G = gauge-only, G(0) = 0, min-degree 2,
   129	
   130	so `R = (core ∘ fst) ∘ Φ` for the LOCAL DIFFEO `Φ : (T, g) ↦ ((T₁, (I+G(g))·T₂), g)` fixing the
   131	origin (block-triangular Jacobian, `det DΦ(0) = (det(I+G(0)))^{M₂} = 1` ⟹ bounded-unit), with `core`
   132	loss `dlnLoss M 0` (a function of `T` alone, NOT the gauge `g`). The same-weight transverse coupling
   133	`Z₁·Y₂` flagged at r≥2 is ABSORBED into the invertible inner factor `I+G` — NOT an additive
   134	germ-changing perturbation — so the identification is `r`-independent and TIGHT (`rlctAtOn R 0 =
   135	coreDeepest`, equality). The bound is NOT the R1-resolution-coupled leading-form lemma first feared;
   136	it is this local-diffeo + spectator reduction, routing through the SAME banked machinery #44 uses.
   137	
   138	The interface below banks `hCore` CONDITIONAL on the producer's diffeo data (the EXACT shape the
   139	producer at obligation (i) supplies). It decouples `hCore` from the R1 / interior-det timeline. -/
   140	
   141	/-- **`hCore` via the slice-residual diffeo** (the PART (b) interface, conditional clean-three). The
   142	slice residual `R` on `Reduced × Gauge` equals the reduced core `core₀` (a function of
   143	the `Reduced` factor alone) pulled back along a bounded-unit local diffeo `Φ` fixing the basepoint
   144	`(t0, g0)`, i.e. `R = (core₀ ∘ fst) ∘ Φ` (`hRform`). Then `rlctAtOn R (t0,g0) = rlctAtOn core₀ t0`:
   145	the diffeo transfer (`rlctAtOn_boundedUnit_localHomeomorph`) strips `Φ`, the spectator peel
   146	(`rlctAtOn_spectator_peel`) drops the gauge factor. In particular `coreDeepest = rlctAtOn core₀ t0`
   147	discharges the D1 `hCore : coreDeepest ≤ rlctAtOn R (t0,g0)` with EQUALITY (the G1 tightness).
   148	
   149	The hypotheses are EXACTLY the producer's outputs: the diffeo `Φ`/`Φsymm`/derivatives + bounded-unit
   150	Jacobian on an open `V ∋ (t0,g0)` (the raw-data `rlctAtOn_boundedUnit_localHomeomorph` form —
   151	the `Φ` of G1), the form identity `hRform`, and a positive-finite gauge
   152	nbhd `hG` (the spectator box). `core₀` is the reduced loss `dlnLoss M 0` at the producer.
   153	
   154	**SCOPE LIMIT (kill-condition adjudication a97332/a591012b, 2026-06-29 — do not over-read).**
   155	The germ-factorization `hRform` (`R = (core₀∘fst)∘Φ`, `Φ` bounded-unit, `det DΦ(0) =
   156	1`) is dischargeable by the producer ONLY at DEEPEST-TYPE optimal points (where the extra Morse rank
   157	`nReg_v − nReg = 0`, so `R` IS the deepest core up to the inner factor — the G1 finding). At a
   158	MIDDLE-STRATUM optimal `v` (`nReg_v > nReg`, e.g. `(3,3,3)/r=1`, `A₁=diag(1,1,0)`, `A₂=diag(1,0,0)`,
   159	`nReg_v=7 > nReg=5`), the EXACT slice residual after the constant-`nReg` peel has a degree-2 Morse
   160	part (`det DΦ(0) ≠ 1`, a genuinely DIFFERENT germ) — so `hRform` is FALSE there and this does NOT
   161	fire. `hCore : coreDeepest ≤ rlctAtOn R t0` STILL HOLDS at such `v` (verified EXACT:
   162	`rlctAtOn R 0 = coreDeepest = 3/2` at that point — the `extra = nReg_v − nReg` Morse halves exactly
   163	offset the degraded core), via a Morse-WITH-PARAMETERS VALUE argument, NOT this factorization. So at
   164	GENERAL `v`, `hCore` is discharged at the VALUE level (`rlctAtOn R 0 ≥ coreDeepest`), an open
   165	producer obligation NOT reducible to `hRform` — surfaced to the controller (the kill residual
   166	gap). THIS lemma remains the lightest discharge on the DEEPEST sub-locus (where `nReg_v = nReg`). -/
   167	theorem hCore_slice_residual_eq
   168	    {Reduced Gauge : Type*}
   169	    [NormedAddCommGroup Reduced] [NormedSpace ℝ Reduced] [MeasureSpace Reduced]
   170	    [BorelSpace Reduced] [FiniteDimensional ℝ Reduced]
   171	    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge] [MeasureSpace Gauge]
   172	    [BorelSpace Gauge] [FiniteDimensional ℝ Gauge]
   173	    [(volume : Measure (Reduced × Gauge)).IsAddHaarMeasure]
   174	    [SFinite (volume : Measure Reduced)] [SFinite (volume : Measure Gauge)]
   175	    [Measure.IsOpenPosMeasure (volume : Measure Gauge)]
   176	    (core₀ : Reduced → ℝ) (R : Reduced × Gauge → ℝ) (t0 : Reduced) (g0 : Gauge)
   177	    (Φ Φsymm : Reduced × Gauge → Reduced × Gauge)
   178	    (DΦ DΦsymm : Reduced × Gauge → ((Reduced × Gauge) →L[ℝ] (Reduced × Gauge)))
   179	    (V : Set (Reduced × Gauge))
   180	    (hVopen : IsOpen V) (hwV : (t0, g0) ∈ V)
   181	    (hfix : Φ (t0, g0) = (t0, g0))
   182	    (hleft : ∀ w ∈ V, Φsymm (Φ w) = w) (hright : ∀ w ∈ V, Φ (Φsymm w) = w)
   183	    (hΦcont : ContinuousOn Φ V) (hsymmcont : ContinuousOn Φsymm V)
   184	    (hderiv : ∀ w ∈ V, HasFDerivAt Φ (DΦ w) w)
   185	    (hderivsymm : ∀ w ∈ V, HasFDerivAt Φsymm (DΦsymm w) w)
   186	    (hdetmeas : Measurable fun w => |(DΦ w).det|)
   187	    (hdetmeassymm : Measurable fun w => |(DΦsymm w).det|)
   188	    (hbdd : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΦ w).det| ∧ |(DΦ w).det| ≤ b)
   189	    (hbddsymm : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΦsymm w).det| ∧ |(DΦsymm w).det| ≤ b)
   190	    (hRform : ∀ w, R w = core₀ (Φ w).1)
   191	    (hG : ∃ W : Set Gauge, IsOpen W ∧ g0 ∈ W ∧ volume W < ⊤) :
   192	    rlctAtOn R (t0, g0) = rlctAtOn core₀ t0 := by
   193	  -- `R = (core₀ ∘ fst) ∘ Φ`; strip `Φ` (bounded-unit local diffeo), then peel the gauge spectator.
   194	  have hRfun : R = fun w => (fun p : Reduced × Gauge => core₀ p.1) (Φ w) := by
   195	    funext w; rw [hRform]
   196	  rw [hRfun]
   197	  rw [rlctAtOn_boundedUnit_localHomeomorph (fun p : Reduced × Gauge => core₀ p.1) (t0, g0)
   198	      Φ Φsymm DΦ DΦsymm V hVopen hwV hfix hleft hright hΦcont hsymmcont hderiv hderivsymm
   199	      hdetmeas hdetmeassymm hbdd hbddsymm]
   200	  exact rlctAtOn_spectator_peel core₀ t0 g0 hG
   201	
   202	end DLNFibre.DLN.RLCT

exec
/bin/bash -lc 'rg "rlctAtOn (fun A : Params" -n lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean' in /tmp/p44-scope
 exited 2 in 0ms:
rg: regex parse error:
    (?:rlctAtOn (fun A : Params)
    ^
error: unclosed group

exec
/bin/bash -lc 'rg "rlctAtOn (dlnLoss" lean/DLNFibre/DLN/RLCT/Validate -n | head' in /tmp/p44-scope
 succeeded in 0ms:
rg: regex parse error:
    (?:rlctAtOn (dlnLoss)
    ^
error: unclosed group

exec
/bin/bash -lc 'rg "rlctAtOn" lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean | head' in /tmp/p44-scope
 succeeded in 0ms:
    rlctAtOn R 0 = extra/2 + lambdaCore(M'),   extra = m(a+b) − ab,  M' = (m−a, m−a−b, m−b),
and produces `coreDeepest ≤ rlctAtOn R t0`.
    extra/2 + rlctAtOn R₂ t0₂ ≤ rlctAtOn R t0,
and the §5 R1-resolution-at-`M'` interface (`hDegraded`) supplies `rlctAtOn R₂ t0₂ =
and `coreDeepest = ofReal(lambdaCore (square m))`, this gives `coreDeepest ≤ rlctAtOn R t0` — the
data `a + b ≤ m`: given the second-peel chart transfer (`hchart₂ : rlctAtOn R t0 = rlctAtOn F₂
degraded-core value `hDegraded : rlctAtOn R₂ t0₂ = ofReal(lambdaCore M')` (the §5 interface
the D1 `hCore` holds: `coreDeepest ≤ rlctAtOn R t0`. The `extra` Morse squares peeled in the SECOND
    (hchart₂ : rlctAtOn R t0 = rlctAtOn F₂ ((0 : Fin (extraCount m a b) → ℝ), t0₂))
    (hDegraded : rlctAtOn R₂ t0₂ = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :

exec
/bin/bash -lc 'rg "theorem resolution_charts" -n' in /tmp/p44-scope
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean:162:theorem resolution_charts_of_layerCover (M : Fin (L + 1) → ℕ)
lean/DLNFibre/DLN/RLCT/Skeleton.lean:1228:theorem resolution_charts (M : Fin (L + 1) → ℕ)
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:296:theorem resolution_charts_case111 :
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean:47:theorem resolution_charts_case222 :
expeditions/2026-06-20-aoyagi-full/threads/01-rung0-definitions/design-spec.md:394:theorem resolution_charts … : ∃ charts, hcover ∧ hπ ∧ hmono ∧ (exponents give M(T) candidates)  -- R1
expeditions/2026-06-20-aoyagi-full/threads/18-r1-value-lane-migration/statement-card.md:68:- **Lean:** `theorem resolution_charts_of_layerCover (M)`
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/r1-design.md:13:theorem resolution_charts (H) (B) (wstar) :
expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/r1-rescope-statement.md:12:theorem resolution_charts (M : Fin (L + 1) → ℕ) :

exec
/bin/bash -lc "sed -n '1220,1340p' lean/DLNFibre/DLN/RLCT/Skeleton.lean" in /tmp/p44-scope
 succeeded in 0ms:
reachable under `hr`): `prod M A : Matrix (Fin (M 0)) (Fin (M (Fin.last L)))` is an empty matrix, so
`prod ≡ 0` again. Either way the core `dlnLoss M 0 ≡ 0`, so `rlctAtOn = ⊤`, while the right side
`⨅ monomialThreshold` is finite. R1 therefore ASSUMES `0 < M s` for EVERY layer `s` (`hMid` below — the
all-`s` form, endpoints included; the earlier interior-only form missed `M_0`/`M_L`, crux2's fidelity
catch). The formalisation's non-degeneracy carve-out — it refines the paper's realisability (`r ≤ min d⃗`,
non-strict, Lehalleur–Rimányi) to exclude the `prod ≡ 0` degeneracy the combinatorial `lambdaCore` cannot
see; sound within the realisable domain, but NOT a verbatim Aoyagi assumption. The headline supplies it in
`H`-form (`∀ s, r < H s`); the bridge `M s = H s − r` makes the two defeq (`r < H s ⟺ 0 < M s`). -/
theorem resolution_charts (M : Fin (L + 1) → ℕ)
    (hMid : ∀ s : Fin (L + 1), 0 < M s) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
      rlctAtOn (fun A : Params M =>
          dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A) (fun _ => 0 : Params M)
        = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
  sorry

/-! ## A1 / A2 — the arithmetic minimisation + the order count (design-spec §8) -/

/-- The balanced ℓ-split of `P`: `(P mod ℓ)` parts equal to `⌈P/ℓ⌉ = P/ℓ+1`, the rest
`⌊P/ℓ⌋ = P/ℓ`. -/
def balancedSplit (P ℓ : ℕ) (i : Fin ℓ) : ℕ :=
  if i.val < P % ℓ then P / ℓ + 1 else P / ℓ

/-- The clean core form `¼(Σ qᵢ² − Σ mₖ²)` over ℚ: `m : Fin (ℓ+1) → ℕ` the ℓ+1 chosen widths, `q`
the balanced ℓ-split of `P = Σ mₖ` (design-spec §4.3). -/
def cleanCore (ℓ : ℕ) (m : Fin (ℓ + 1) → ℕ) : ℚ :=
  let P := ∑ k, m k
  (1 / 4 : ℚ) * ((∑ i : Fin ℓ, (balancedSplit P ℓ i : ℚ) ^ 2)
    - (∑ k : Fin (ℓ + 1), (m k : ℚ) ^ 2))

/-- The printed Theorem-2 core expression `a(ℓ−a)/(4ℓ) − [ℓ(ℓ−1)/4](P/ℓ)² + ½ Σ_{i<j} mᵢmⱼ`, with
`a = P − (⌈P/ℓ⌉−1)ℓ = P mod ℓ` (design-spec §4.4). -/
def printedCore (ℓ : ℕ) (m : Fin (ℓ + 1) → ℕ) : ℚ :=
  let P := ∑ k, m k
  let a := P % ℓ
  (a * (ℓ - a) : ℚ) / (4 * ℓ) - (ℓ * (ℓ - 1) : ℚ) / 4 * ((P : ℚ) / ℓ) ^ 2
    + (1 / 2 : ℚ) * ∑ i : Fin (ℓ + 1), ∑ j : Fin (ℓ + 1),
        if i < j then (m i * m j : ℚ) else 0

/-- `T j ≤ tPrev M T j` on the admissible cone (weak-decrease, and `t⁽⁰⁾ = M⁽¹⁾ ≥ t⁽¹⁾`). -/
private theorem T_le_tPrev (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    (T j : ℤ) ≤ tPrev M T j := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨hbound, hdec, _⟩ := hT.2
  unfold tPrev
  split
  · rename_i h0
    have hb : T j ≤ admBound M j := hbound j
    rw [admBound, if_pos h0] at hb
    exact_mod_cast le_trans hb (min_le_left _ _)
  · have hle : (⟨j.val - 1, by omega⟩ : Fin L) ≤ j := by simp only [Fin.le_def]; omega
    exact_mod_cast hdec _ _ hle

/-- `T j ≤ M⁽ʲ⁺¹⁾` on the admissible cone (the block bound). -/
private theorem T_le_Msucc (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    (T j : ℤ) ≤ (M j.succ : ℤ) := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨hbound, _, _⟩ := hT.2
  have hb : T j ≤ admBound M j := hbound j
  unfold admBound at hb
  split at hb
  · rename_i h0
    have hle : T j ≤ M 1 := le_trans hb (min_le_right _ _)
    have hL : 0 < L := j.pos
    have hsucc : j.succ = (1 : Fin (L + 1)) := by
      apply Fin.ext; rw [Fin.val_succ, h0, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rw [hsucc]; exact_mod_cast hle
  · exact_mod_cast hb

/-- `Mval ≥ 0` on the admissible cone: each summand is a product of two nonnegative factors. -/
private theorem Mval_nonneg (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    0 ≤ Mval M T := by
  unfold Mval
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (by linarith [T_le_tPrev M T hT j]) (by linarith [T_le_Msucc M T hT j])

/-- `sortedSmallest M c` (for `c ≤ L`): the `c+1` smallest entries of `M : Fin (L+1) → ℕ`, as a
function `Fin (c+1) → ℕ`, via the ascending sort `Tuple.sort` and the first `c+1` indices. The `m`
argument of `cleanCore` is **pinned** to this (a function of `M`), making A1 the genuine Lemma 3. -/
def sortedSmallest (M : Fin (L + 1) → ℕ) (c : ℕ) (hc : c ≤ L) (k : Fin (c + 1)) : ℕ :=
  M (Tuple.sort M (Fin.castLE (by omega) k))

/-- `cleanCore` depends only on the **multiset** of `m`: permuting `m` leaves it fixed
(it is built from `∑ m` and `∑ m²`, both permutation-invariant). The crux that lets the genuine A1
proof stay local to the achiever — matching `cleanCore` at the minimiser's breakpoint widths to
`cleanCore (sortedSmallest …)` needs only that the two are the same *multiset*, not a global
permutation-transport of the admissible cone. -/
theorem cleanCore_perm (c : ℕ) (m : Fin (c + 1) → ℕ) (σ : Equiv.Perm (Fin (c + 1))) :
    cleanCore c (m ∘ σ) = cleanCore c m := by
  simp only [cleanCore]
  have hsum : (∑ k, (m ∘ σ) k) = ∑ k, m k := Equiv.sum_comp σ m
  have hsq : (∑ k, ((m ∘ σ) k : ℚ) ^ 2) = ∑ k, (m k : ℚ) ^ 2 := by
    have := Equiv.sum_comp σ (fun k => (m k : ℚ) ^ 2); simpa using this
  rw [hsum, hsq]

/-- The strict-descent positions of `T ∈ Adm M`: indices `j` where `u_j > u_{j+1}` (`u = M⁰ ∷ T`),
i.e. `T j < tPrev M T j`. The `Mval` sum collapses to these (the gap factor is `0` elsewhere). -/
noncomputable def descentSet (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Finset (Fin L) :=
  Finset.univ.filter (fun j => (T j : ℤ) < tPrev M T j)

/-- **#19 step-2 entry: `Mval` collapses to the strict descents.** For `T ∈ Adm M`, `Mval M T` sums
over only its `descentSet` (at a non-descent index `tPrev = T j` by admissibility, so the gap factor
`tPrev − T j` is `0`). The reparametrisation that feeds the per-T lower bound. -/
theorem Mval_descent (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    Mval M T = ∑ j ∈ descentSet M T, (tPrev M T j - (T j : ℤ)) * ((M j.succ : ℤ) - (T j : ℤ)) := by
  unfold Mval
  rw [descentSet]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _ hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
  have hge : (T j : ℤ) ≤ tPrev M T j := T_le_tPrev M T hT j
  have hz : tPrev M T j - (T j : ℤ) = 0 := by omega
  rw [hz, zero_mul]

/-- **Karamata for squares (ascending-prefix form, over ℤ).** If `y` is monotone on `[0,n)`, `x` and
`y` have equal total over `range n`, and every prefix sum of `x` is `≤` that of `y`, then
`∑ y² ≤ ∑ x²`. The convexity lower-bound engine: `x²−y² ≥ 2y(x−y)`, and `∑ y(x−y) ≥ 0` by
summation-by-parts (`Finset.sum_range_by_parts`) from prefix-domination + monotonicity. -/
private theorem karamata_sq (n : ℕ) (x y : ℕ → ℤ)

codex
**Verdict**  
- RESEARCH-WALL: applying the §SEL chart at the deepest point still requires the unresolved reduced-core RLCT identity, so #44 is not currently reachable via the chart route alone.

**Q1 – Residual identification**  
- At deepest-type points the producer’s `hCore_slice_residual_eq` shows the chart residual `R` is a bounded-unit diffeomorphic pullback of the reduced loss `dlnLoss (H−r) 0`, and spectator peeling removes the gauge factor; hence the RLCT of `R` equals the reduced-core RLCT. (lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:141-200)

**Q2 – Status of `rlctAtOn(dlnLoss M 0)=lambdaCore M`**  
- This equality is still open: the Skeleton’s `resolution_charts` remains a named `sorry`, and the general Route-M recursion currently stops at an explicitly identified gap. (lean/DLNFibre/DLN/RLCT/Skeleton.lean:1220-1236; lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:19-32,190-207)

**Q3 – Equality versus inequality**  
- The §SEL chart wiring produces the ≥-leg for general optimal points but assumes #44 (`hDeepest`) to compare with the deepest point; it does not supply the missing ≤ direction needed to prove #44 outright. (lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:93-121)

**Q4 – Obstruction**  
- The sole remaining obstacle is the unresolved R1 value theorem (`resolution_charts`, Route-M recursion). Until that core RLCT equals `lambdaCore` is proved, the chart+quasi-split machinery cannot close #44; it merely defers the hard work to the same outstanding result.

**Next step suggestion**  
- Focus effort on discharging the Route-M recursion / `resolution_charts` gap; once that lands, the chart route will immediately yield #44.
tokens used
164,872
**Verdict**  
- RESEARCH-WALL: applying the §SEL chart at the deepest point still requires the unresolved reduced-core RLCT identity, so #44 is not currently reachable via the chart route alone.

**Q1 – Residual identification**  
- At deepest-type points the producer’s `hCore_slice_residual_eq` shows the chart residual `R` is a bounded-unit diffeomorphic pullback of the reduced loss `dlnLoss (H−r) 0`, and spectator peeling removes the gauge factor; hence the RLCT of `R` equals the reduced-core RLCT. (lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:141-200)

**Q2 – Status of `rlctAtOn(dlnLoss M 0)=lambdaCore M`**  
- This equality is still open: the Skeleton’s `resolution_charts` remains a named `sorry`, and the general Route-M recursion currently stops at an explicitly identified gap. (lean/DLNFibre/DLN/RLCT/Skeleton.lean:1220-1236; lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:19-32,190-207)

**Q3 – Equality versus inequality**  
- The §SEL chart wiring produces the ≥-leg for general optimal points but assumes #44 (`hDeepest`) to compare with the deepest point; it does not supply the missing ≤ direction needed to prove #44 outright. (lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducer.lean:93-121)

**Q4 – Obstruction**  
- The sole remaining obstacle is the unresolved R1 value theorem (`resolution_charts`, Route-M recursion). Until that core RLCT equals `lambdaCore` is proved, the chart+quasi-split machinery cannot close #44; it merely defers the hard work to the same outstanding result.

**Next step suggestion**  
- Focus effort on discharging the Route-M recursion / `resolution_charts` gap; once that lands, the chart route will immediately yield #44.
