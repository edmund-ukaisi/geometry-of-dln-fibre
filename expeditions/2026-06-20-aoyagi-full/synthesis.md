# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-22): ★ DESIGN CLOSED (g132→g153) — general-M λ on three concurrent Lean grinds ★

**Phase.** The general-M monomial route is the live path (the per-node squeeze is OFF-path — blow-up gives
an x_p²·Q product, not the squeeze's additive sum; no measure-preserving recursion produces the monomial
Jacobian weight). The pen-and-paper / design side is **complete and corrected** (pp2 arc g132→g153, + g138 §1
C1 prose fixed). What remains is pure Lean: three concurrent grinds against a settled design, no open mechanism.

**The λ headline** `aoyagi_learning_coefficient` (Skeleton) is proven modulo three named rungs; A1, the top
assembly, the transport/shift machinery are proven. The headline-given-atlas chain is proven, green, S2-free
(`RouteMAtlas` unifies `IsRouteMCover` + `IsResolutionAtlas`; `routeM_rlctAtOn_eq_lambdaCore`). The three rungs:
- **R1** `resolution_charts` — fm3 #39: the `RouteMTree` dispatcher (classify + schur/pass/left/right state +
  descent) + cover-facts (`cover_le`/`cover_ge_div`) + achiever. `cover_le` (the path-composite CoV integral)
  is the one evidence-then-switch spot (WF.fix vs plain-inductive).
- **L2** `product_reduction` — crux2: APPROVED SPLIT (2026-06-22) into value-free `deepest_regular_core_reduces`
  (rlctAt deepest = nReg/2 + rlctAtOn(dlnLoss M 0) 0) + R1-value composition (▸). #50 = consuming side
  (S1 spectator-peel + sub-5/6/7 + assembly); #51 = the XL chart-existence.
- **D1** `rlctAt_deepest_le_of_optimal` (≥-leg) — downstream of L2's gauge chart (the 6-step wiring once the
  general-`IsDeepLayers` chart lands).

**C1 mechanism (SETTLED, g152/g153).** Per-node C1 = blow-up (x_p² weight, exceptional (k,h)=(1,card−1)) +
**det-1 triangular Schur peel** (w:=D−b·a, the #37 change) + recurse. The peel is NEEDED (g152: {S=0}={D=b·a}
is BILINEAR; pivotBlowupOn only hits coordinate subspaces — the peel makes it {w=0} first). The peel is det=1
MP at ANY rank (g153: unipotent block-triangular block-shear, rides measurePreserving_lemma2, no Jacobian
weight, no bounded-unit lemma); Σdrop=2 (ChainDimSplit.measure_drops). The same triangular peel appears one
level up at the g150 deepest-point gauge chart (there det-UNIT, non-MP). NOT the squeeze, NOT lemma2Fwd.

**g150 gauge chart (CORRECTED).** Reduced core = gauge-normalized ‖T̃_1···T̃_L‖² (product Schur complement),
NOT raw ‖∏T_s‖² (on {E=0} the cross-term becomes invertible gauge factor (I−V·Y)^{-1}). nReg = r(H₀+H_last−r).

**Cert sharpening (cobuild-sub34 + Codex, decorrelated, 2026-06-22).** The raw-chain squeeze ‖T·S‖² is FALSE
for matrices (g=(I−VY)⁻¹ maps a TS=0 dir to TgS≠0, ratio→∞) — independent re-derivation of why the core must
be T̃; the g-absorption IS the non-MP content. The cert framing refines: "exact split, not a squeeze" →
"exact only in T̃-coords; the raw-chain squeeze is false."

**sub-3/4 ROUTE — RESOLVED (2026-06-22): R-SQUEEZE; the XL chart-existence COLLAPSES.** crux2 (structure owner)
decided R-squeeze after reading cobuild-sub34's g152 finding. DeepestGaugeChart is trimmed: drop the global
`chart`/`Dchart`/`hasDeriv`/`jac_unit` + the `loss_form` EQUALITY; replace with a `loss_squeeze` datum
(c₁Φ ≤ dlnLoss∘flat ≤ c₂Φ near the deepest point, Φ = ∑reg² + dlnLoss M 0(core)); keep nGauge/split/split_mp/
split_zero. WHY: (1) the honest gauge chart is only a LOCAL diffeo at w0 (inverse uses A⁻¹/(I−VY)⁻¹, blows up
off w0) — a global homeo over-reaches; rlctAtOn is local, the squeeze is local-by-construction; (2) reuses ONLY
blessed infra — rlctAtOn_squeeze (the GeneralR1Recursion `schur_recursion_step_squeeze` pattern) + #52 +
rlct_additive_smooth_block; no global-chart construction, no weightedThreshold_transport; (3) crux2's proven
sub-6 SURVIVES (it computes rlctAtOn Φ; the squeeze only changes how sub-5 reaches Φ). NET: the XL sub-3/4
chart-existence (~600-1500 lines of cutoff-extension block algebra) is DROPPED — it collapses to ONE obligation:
the matrix-core comparability ‖T·(I−VY)⁻¹·S‖² ≍ dlnLoss M 0 (GAUGE-NORMALIZED T̃, NOT raw ∏T — raw is FALSE for
matrices). Ownership: crux2 = structure re-shape + sub-5 (Params→flat MP + rlctAtOn_squeeze); cobuild-sub34 = the
comparability (#53/#54/#55) against the trimmed loss_squeeze field. Handoff coherence: #55's raw-∏T framing
(|‖P11‖²−‖∏T‖²| ≤ K∑E²) is valid only if that leak bound holds; else state the comparability in T̃ form directly
— pinned by crux2's loss_squeeze field shape. (Route arc: squeeze → chart [on cutoff-satisfiability] → R-squeeze
[on the GeneralR1Recursion precedent + the collapse]; resolved by crux2's owner-call. Ledger lesson: bank live
decisions as "current lean, pending X", not as settled.)

**Current execution (three grinds):**
- fm3 #39 (R1 dispatcher + cover-facts) on origin/fm3/routem. Seam VERBATIM-matched to crux2's contract (fm3
  confirmed cover-fact signatures = the contract). Achiever = `_le_regularSeq` at j₀ (card=m₀ min-ratio axis) +
  threshold_ge, bundled by of_mult_and_achiever; binding axis = ⨅ over multiple C1 axes.
- crux2 #50 (value-free reduction) on origin/fm2/deepest-gauge-chart (@c1ce00f/@7573c0b): CONSUMING SIDE
  FULLY PROVEN (clean-three) — sub-2, sub-5 (`deepest_squeeze_transport`), sub-6, sub-7, the assembly
  `deepest_regular_core_reduces`; + 4 reusable Foundations lemmas (spectator-peel #52, continuous_dlnLoss,
  weightedThreshold_weight_unit_invariant, rlctAtOn_mono/rlctAtOn_squeeze re-homed GeneralR1Recursion→
  S1NonMPTransport). GATED on ONLY sub-3 (cobuild-sub34's comparability). STRUCTURE FIX in flight (cobuild-sub34
  caught it at instance-production): the trimmed loss_squeeze was OVER-CONSTRAINED — split MP + hardcoded Φ-core
  = dlnLoss M 0(paramsEquivFlat M ...) forces the RAW core, which g153 refuted (C1C2C3=blockdiag[1,−ε⁴]: loss=ε⁸
  > 0 = Φ). FIX (A, determined): add `coreEmbed` field (the g-absorbing UNIT-Jacobian reparam) + Φ-core =
  dlnLoss M 0(coreEmbed ...); split stays MP (sub-5/6 INTACT, verified line-by-line), sub-7 gains the unit-peel
  via the PROVEN weightedThreshold_weight_unit_invariant. L2 claim HOLDS (unit-Jacobian ⟹ core RLCT =
  rlctAtOn(dlnLoss M 0) 0). crux2 implementing. hGne carried as a local hypothesis → TRACKED for spine-wiring;
  gap #2 measurability CLOSED (Codex g151). crux2 NEXT → D1≥ wiring skeleton (below).
- cobuild-sub34 #51 (the COLLAPSED sub-3 = matrix-core comparability, GAUGE-NORMALIZED T̃): chart-collapse
  CONFIRMED; matrix bedrock #53 BANKED green (twofactor_block_product, schur_P11_decomp [P11=R+leak, R=T̃],
  frobenius_fromBlocks). OPEN soundness Q gating the loss_germ transcription — **split_mp vs T̃-core**: can an MP
  `split` deliver the T̃ core (crux2's `ofExactGerm` stands as-is), or is a non-MP `coreEmbed` field needed
  (cobuild-sub34)? DECIDED via the g153 litmus (C1C2C3=blockdiag[1,−ε⁴]: Φ=ε⁸ → MP-deliverable, crux2 right;
  Φ=0 → coreEmbed needed). Note: cobuild-sub34's "MP ⟹ linear reindex" inference is too strong (MP ≠ linear; a
  nonlinear volume-preserving split is possible, gauge slot compensating the (I−VY) det). Worktree workspace/dgc-sub34. pp2 backup.
- **D1 #42 ≥-leg (`rlctAt_deepest_le_of_optimal`):** #57 VERDICT (pp2, decorrelated): D1(a) "deepest = min-rlct
  over optimalSet" is L1-SEPARABLE — **NO 2nd citation, the only-S2 policy is SAFE** (Aoyagi Thm 2 NOT needed).
  BUT it needs a NEW value-independent analytic primitive (the design under-estimated D1(a) as a light
  rlctAtOn_mono step): (P1) RLCT lower-semicontinuity `rlctAt(deepest) ≤ liminf rlctAt(t·v) = rlctAt(v)` [L1-a
  scaling-invariance g162 elementary + L1-b semicontinuity HEAVY], OR (P2) RLCT = rlct-of-leading-Newton-form
  (Varchenko). pp2's light routes ALL REFUTED (g163: v's leading form is deg 2 not 4 — "deepest = leading part"
  is backwards; rlctAtOn_mono compares 2 funcs at 1 pt, not 1 func at 2 pts; block_elim split circular).
  HEADLINE KEYING (controller call, from the spine): the headline IS ⨅-over-optimalSet (Skeleton:1505) — the
  faithful learning coefficient; NOT downscoping to the deepest-point value (weaker, λ≤aoyagiLambda only). So
  D1(a) is load-bearing. DRIVING P1 (cleaner): pp2 designs the cert, crux2 assesses LEAN TRACTABILITY from the
  existing rlctAtOn machinery (rlctAtOn is the team's own def — semicontinuity may follow from its structure, not
  absent Mathlib analysis). That read → build P1 inline OR surface a feasibility fork to the operator. crux2 holds
  D1≥ wiring until P1 scoped; #112 wiring cert done. (Scope (i): non-rank-exact v is MOOT for D1(a) — it's a
  comparison via the scaling-ray on the RAW loss, charts no v; pp2 reconciled with crux2.)

**TRACKED SOUNDNESS / PRECISION ITEMS (controller holds):**
1. **hGne** (L2+R1) — RESOLVED → **STATED headline non-degeneracy hypothesis** (fm3 verdict (b), FORCED): interior M_s=H_s−r=0 ⟹ prod_M≡0 ⟹ dlnLoss M 0≡0 ⟹ RLCT=⊤, but lambdaCore M finite ⟹ the R1 identity is LITERALLY FALSE there; the domain MUST exclude it (forced by the formula's correctness) + Aoyagi-faithful. **Headline gains `∀ interior s (0<s<L), r<H_s` (interior M_s≥1)**, fenced as the Aoyagi non-degeneracy regime — strengthens hr:∀s,r≤H_s; threaded through aoyagi_learning_coefficient + deepest_point_reduction + L2 (crux2) + R1 (fm3). Endpoints s=0,L may have H=r; only interior forces prod≡0. A fidelity WIN (headline-as-stated was false for interior H_s=r). NOT an operator surface (faithful statement, doesn't touch only-S2) — but a prominent caveat on "DLNs mildly singular" in the final deliverable.
2. **D1(a) deepest=min-rlct** (#57+#60 RESOLVED) — L1-separable, NO 2nd citation; and **P1 is LIGHT** (#60 @4995532, ~10 lines from the team's OWN rlctAt def: an admissible U₀∈𝓝 0 swallows the ray points s·v ⟹ c'∈A(s·v) ⟹ sSup_le, + banked L1-a g162). g160's "heavy P1" was an OVERESTIMATE (pp2 had routed via general Watanabe semicontinuity; the ray-only version is free from the def) — corrected. **NO operator surface; no Mathlib gap; build inline.** Keying = ⨅ (faithful, Skeleton:1505). Route core-vs-full-B = crux2's spine-assembly call (both no-new-primitive: P1 light + the L2-at-every-v wrapper = reused L2 machinery, the regular shift constant on optimalSet since r constant). crux2 consuming #60 into the D1 skeleton (origin/fm2/d1-deepest-min) + filling L1-a.
3. **split_mp vs T̃-core** (#44 sub-3) — RESOLVED (g153 litmus → Φ=0 with the hardcoded core): a pure MP split can't do the non-MP g-absorption ⟹ crux2 implementing the `coreEmbed` field + re-proving sub-6/7 via its weight-invariance lemma. cobuild-sub34's catch (decorrelation: producer caught consumer bug).
4. **exact-vs-squeeze** — CORRECTED to SQUEEZE: cobuild-sub34's Lean #54 (`core_comparability_squeeze`) has c₁=(2(1+t²))⁻¹, c₂=2+2t² (c₁=1/2,c₂=2 at w0 — c₁<c₂ even at the basepoint; leak BOUNDED by t²∑E², not absorbed). The frobenius split loss=∑E²+‖P11‖² is exact (lemma 3), but the P11→R core-identification is a genuine SQUEEZE — the "exact" framing would couple reg+core (2⟨R,leak⟩), breaking sub-6's separation. So #48's "exact germ" OVERCLAIMED; the honest name is SQUEEZE. Consequence: `ofExactGerm` (c₁=c₂=1) is unused; cobuild-sub34 fills `loss_squeeze` directly with #54. RESOLVED: pp2 DOWNGRADED g155 → SQUEEZE (canonical @001fa37; g165-verified the cross-term 2⟨R,leak⟩ couples reg+core; g155-exact b3c51db SUPERSEDED). Route confirmed by committed code (@b4229e0: no chart/Dchart/jac_unit). (I'd banked EXACT prematurely — the name-results trap; cobuild-sub34's #54 + pp2's g165 corrected it.)

**CANONICAL CERT LINEAGE (for #28 — pp2's authoritative tips, 2026-06-22):**
- g138 design (C1 = blow-up + det-1 triangular peel + recurse): **origin/g138-c1-peel-prose @0823917** ← canonical
- g140 ι-pin: origin/g140-both-steps @2f80d44
- g134 (S-min): origin/g134-surjectivity-sketch @e18c00e
- g147 achiever: origin/g147-achiever-cert @6e6b00d
- g148 i₀ re-spell (2-node (2,2,2)): origin/g148-222fix2 @34c1d6c
- g150 gauge chart: **origin/g150-gauge-chart-fix @50251296** ← canonical (corrected T̃ form; raw-T superseded)
- g152/g153 C1-peel: origin/g152-c1-peel @0006f3a (also folded into g138-c1-peel-prose)
- g155 general-v squeeze cert: **origin/g155-squeeze-downgrade @001fa37** ← canonical (SQUEEZE; g155-exact-precision b3c51db SUPERSEDED)
- D1 #57 prove-or-surface (deepest=min-rlct L1-separable, NO 2nd citation; P1/P2 landscape): origin/g160-d1-update @89f5915
- #44 squeeze structure (chart DROPPED, coreAbsorb + coreAbsorb_rlct; consuming side proven): origin/fm2/deepest-gauge-chart @b4229e0; sub-3 = cobuild-sub34's #53/#54 on origin/fm2/deepest-gauge-chart-sub34
- S-min value (canonical ResolutionAtlas, 3-conjunct): origin/cover/resolution-atlas-value @1c4b9b5
- bridge/atlas: RouteMBridge origin/fm2/route-m-bridge @472433b; RouteMAtlas origin/fm2/route-m-atlas @31063ec
- consolidation base: origin/integration/routeM-wip @0afee3a (g129 toolkit; has OLD 4-conjunct ResolutionAtlas —
  pull S-min from @1c4b9b5 instead)

**#28 plan (controller, at core-green):** consolidate onto expedition/aoyagi-full — RouteMAtlas = local core
branch; pick g150-gauge-chart-fix (T̃) + g138-c1-peel-prose + S-min @1c4b9b5 (3-conjunct, NOT the 4-conjunct on
routeM-wip); dedup Mval_nonneg; flush this synthesis. At merge, fold pp2's g140 gloss ("inductive RouteMTree"
→ "the WF.fix atlas's leaves (nested Σ/Sum)" — fm3's encoding is WF.fix, not a materialized inductive; ι +
achiever unaffected). PR only after the full general-M `aoyagi_learning_coefficient` is sorry-free (operator:
no PR until the hero task is done).

## Prior read (2026-06-21): ★ R1 EXECUTION — S1.5 sorry CLOSED (6→5) @1304cf2; (2,2,2) route PINNED ★

**Milestone @`1304cf2` (pushed origin, rv-2 auditing):** the S1.5 wire is in — `rlct_additive_smooth_block`
now `exact …_aux` (closes a sorry, **6→5**), axioms `[propext, Classical.choice, Quot.sound]` (no sorryAx,
no monomial_rlct). `resolution_charts` **re-scoped to the CORE form** `rlctAt M (dlnLoss M 0) (0:Params M)
= ⨅ i, monomialThreshold (d i)(k i)(h i)` (rlctAt, deepest=0 — replaces the old false full-loss form);
`resolution_charts_case111` realigned to it, STILL axiom-free (the genuine M=(1,1,1) instance). Only declared
axioms in-tree: `monomial_rlct` (S2) + `opaque rlctOrderAt` (θ-seam). 5 sorries, all in Skeleton (the rungs).

**Measure engines all axiom-clean** (verified by explicit build + #print axioms): Fubini `_aux` (S1.5),
G5-step `g5_flat_cover` (#52), `rlctAt_mono`, `product_min_rlct` (#56), `product_min_rlct_of_ne` (#57).

**R1 design COMPLETE — (2,2,2) deeper-point pin RESOLVED (pp + decorrelated Codex, identical):** the δ-pivot
chart's "unit" U=ξ²+η²+(bξ+r)²+(bη+s)² is a nondeg smooth-4-block (Hessian det 16) vanishing EXACTLY at
{ξ=η=r=s=0} = the deeper stratum **B=0** (fm SPECIFY-catch, chart-exact §8 caveat). Route = **STEP-3
sub-blowup** (option b); the δ-pivot was never a leaf — its 4 step-3 children ARE part of the **stable 24-leaf
set** (8 unit d=2, k=![1,1], h=![3,2] + 16 block d=3, k=![1,1,1], h=![3,2,3], all RHS 3/2; ⨅=3/2=lambdaCore(2,2,2),
θ=1). **Soundness DISCHARGED:** deeper stratum B=0 has codim 4 > minMval 3 ⟹ its exceptional ratio 2 > binding
3/2 ⟹ NEVER binds — chart-exact form of "centers=admissible strata, no center beats min". Full Jac = **α³·ρ²**
(α³ = step-1 A-blowup). Durable in r1-222-cover card §δ-CHART-DEEPER-POINT-PIN + §δ-BRANCH-BUILD-ROUTE-FORK.

**Route-fork adjudicated (controller call):** the product_min-skip route is SOUND (shear unimodular even with
b free; rlct(U)=2; positivity-OK) but **heavier** — it needs a NEW weighted-product-split lemma (because #56
is **TRIVIAL-weight** and the δ-leaf carries the α³ρ² Jacobian). step-3 is lighter for (2,2,2) (uniform monomial
machinery, no new lemma). The weighted-split is a reusable **general-M down-payment** → **DEFERRED** (general-M
gated on G3 = roadmapped, not the active target). ⟹ build (2,2,2) δ-branch via step-3; #56 serves trivial-weight
call-sites only ((2,1,2) #55 TBC).

**Green-gate GAP found + fixing:** `lake build DLNFibre` builds only the aggregator's closure → not-yet-consumed
engines (S1ProductMin #56, S1G5 #52, ParamsFlat) escaped it (caught via "S1ProductMin.olean does not exist" on
axiom-check). Built them explicitly (green; #56 axiom-clean). fm to (a) import stable engines into the aggregator
+ (b) restore AxCheck.lean. Lesson banked. "Green build" ≠ "every module compiles."

**Since the milestone (trunk now @930a6a0, all pushed):** rv-2 AUDIT **PASS** on @1304cf2 (S1.5 wire / re-scope /
case111 — decorrelated, validated the min-on-core + n/2-via-Fubini decomposition). **Green-gate gap CLOSED**
(@73c52f9 + @930a6a0): all 9 measure engines now imported by the aggregator + **AxCheck.lean restored**
(emits `#print axioms` every build — 5 results clean, headline sorryAx). **#57** `product_min_rlct_of_ne`
gated @2e8dc4c. **#58** pivot-blow-up atom gated @930a6a0 (pivotBlowup/Deriv/_det=(x 0)^n/_injOn, parametric
n — serves all 3 (2,2,2) blow-up nodes). Lesson banked: green `lake build <lib>` covers only the aggregator
closure (orphan engines escape).

**Active (trunk @536740b; LADDER 2/3 — (1,1,1) + (2,1,2) DONE + axiom-free):**
- **(2,1,2) #55 — DONE @536740b, axiom-free.** `case212_rlct = [propext, Classical.choice, Quot.sound]` (AxCheck);
  6→0: product-MIN heart (`product_min_rlct`), both block-RLCT bridges (EuclideanSpace↔Pi via
  `PiLp.volume_preserving_toLp`, in-seat), coord-split (the (1,1,1)-`entryME` pattern), `prod212_entry`
  (lean-formaliser). Merged + aggregator/AxCheck-wired. rv-2 auditing. Audits PASS so far: milestone/#58/#61/#52.
- **(2,2,2) #54** — fm-2, on flat `Fin 8→ℝ` (carrier **FORCED**: product `(Fin4→ℝ)²` lacks `IsAddHaarMeasure`).
  Node toolkit done/near: #58 (C¹/det/InjOn full-block), #61 (argmax cover), #64 (spectator), #65 (hmeas),
  #67 (argmaxCellOn flat-subset cover) — all gated; + `pivotBlowupOn` det (fm-2's +91 WIP, green+sorry-free,
  gating pending fm-2's confirm) → **#69 g5_pivotNode** (single reusable node, in progress). **#68 per-leaf
  VALUE lemmas DONE (fm half of #54).** REMAINING: pivotNode → 24-leaf 3-deep assembly (+ φ_L2 splice) + the
  **#66 seam** — route (ii): fm-2's OWN explicit m.p. `Params≃ᵐFin8` via `piCongrLeft` + an explicit a00..b11
  bijection (order pinned by construction, sidesteps the noncomputable equivFin). **Measure-instance verify-first
  flagged:** the piCongrLeft m.p. must land on Params's *actual* MeasureSpace instance (= rlctAtOn's), via the
  generic reindex lemma — not a parallel canonical-Pi measure. rv-2 audits the seam (the silent-hole point).
- **Case222 wrapper** (fm) — thin (2,2,2) validate headline, gated on #54's result. **pp** on-demand.
**Roadmapped (operator-gated scope):** G3 (general-M wall), #19 keystone (#37/#45/#46), weighted-product-split
(general-M). **Fixed-M ladder = active target: (1,1,1) DONE · (2,1,2) DONE · (2,2,2) #54 (the last rung).**

## Prior read (2026-06-20): ★ CONTRACT IS BEDROCK @296d3e4 — structural-proof phase OPEN ★

**rv-2 FINAL re-audit @`296d3e4` CLEAN → BEDROCK DECLARED.** The 9-issue fidelity arc is CLOSED. The contract
is genuine bedrock: domain PROVABLY complete (hr middle-width + hL L=0, systematic corner sweep proved no
10th hole), keystone clean, A1-clean + L1 genuinely proven (no sorryAx, not vacuous), headline assembles
axiom-clean through D1▸L2, S2 the ONLY citation (no leak), every rung name=content/non-vacuous. `git diff
2ee02b2 296d3e4` is hL-ONLY (zero drift). The rock the structural proofs now stand on.

The 9 issues (all caught by proof-attempts/decorrelated checks BEFORE anything built on them, all fixed):
6 in the original adversarial pass (L1 vacuous, L2 over-claim, D1 under-claim, S1.1 measure, R1 analyticity,
S1.5 analyticity); 7th deepestPoint false (middle-width) → hr; 8th lambdaCore weak existential → strengthen
(#19, sequenced); 9th deepestPoint false (L=0) → hL. Two sweeps closed the vacuity + domain classes wholesale.

Two honest residuals (NOT bedrock defects — off the criterion): deepestPoint_exists is a `sorry` (fm
mid-proof — a PROOF obligation, not a statement defect); A1 lambdaCore (#19) + A2 weak existentials (flagged,
off the headline path, strengthen sequenced).

### Earlier status (pre-bedrock, retained for the arc):
Two structural rungs landed during the contract phase. Honest status:

**Landed / green:**
- **Keystone `paramsEquivFlat`** (`Params H ≃ᵐ (Fin N → ℝ)`, measure-preserving) — fm-2 @`d7b1ba3`
  (Route A++). **rv-2 PASS (bedrock-clean):** isolated `/tmp` green-gate (2851 jobs, no shared-tree race),
  ParamsFlat ZERO sorries, axioms `[propext, Classical.choice, Quot.sound]` (no sorryAx/stray), NO leaked
  global instance (threads by `rfl`; bare `Matrix` still has no MeasurableSpace), flatDim correct by decide.
  Unblocks the (1,1,1) bridge, S1.1's use-site, R1's measure facts. (Nit: unused `forall_true_left` in
  `measurePreserving_piCurry` — fm-2 cleans on next touch.)
- **A1 `clean_eq_printed`** — fm, committed @`c234651` (genuine ℚ identity, rv-2 9324-case verified). KEEP.
- **A1 `lambdaCore_eq_clean`** — fm, committed @`f8233f2` (worktree-rung0-defs, sorry 13→11) — but it's the
  **WEAK existential (8th fidelity issue)**: closed by FREE CHOICE (ℓ=1, m=![1,(min Mval).toNat], needs only
  min≥0) — proves NOTHING about M, NOT Aoyagi Lemma 3. fm flagged it (good). DECISION: strengthen to genuine
  Lemma 3 (lambdaCore M = clean form at Def-3-selected widths, m BOUND to M; ~200-line balanced-split
  exchange). OFF the headline critical path (headline uses aoyagiLambda directly) ⇒ SEQUENCED after L1; weak
  proof KEPT with loud docstring flag as honest interim. pp DELIVERED the genuine statement (card
  `threads/14-r1-design/a1-statement-card.md`): `∃ ℓ ∈ {1..L}, lambdaCore M = cleanCore ℓ (sortedSmallest M ℓ)`
  — `m` PINNED to M's ℓ+1 smallest reduced widths (genuine: forced by (M,ℓ)). ⚠️ NOT an extremum: `min_ℓ`
  AND `max_ℓ` are BOTH FALSE (pp refuted Codex's "cleanest" via M=[1,1,4] / [2,2,2]) — formaliser must keep
  the `∃ℓ`. Verified 1360/1360. fm formalizes #19 (replace weak stmt+proof) AFTER deepestPoint_exists (off
  critical path). Def-3 sidestepped entirely.
- **L1 `block_elimination`** — fm @`fb65243` (worktree-rung0-defs), GENUINE explicit block-normal form (not
  the vacuous rank claim), ~220 lines via adapted-basis (`Basis.sumQuot` + `basis_toMatrix_…`). sorry 10→9.

**Weak-existential sweep (rv-2, complete):** exactly 2 weak rungs — A1 `lambdaCore_eq_clean` + A2
`aoyagiTheta_eq` (both on the fix list). L1, deepestPoint_exists, R1 GENUINE. Discriminator banked (lessons):
`∃ x, LHS(data)=f(x)` is WEAK iff f free-covers a CONCRETE LHS (x choosable free of data), GENUINE iff the
LHS is OPAQUE/pinned (witness must encode data). R1 genuine despite A1-shape (rlctAt = opaque sSup). No
surprises lurking — fidelity class fully catalogued.

**The 7th bug (caught by fm's proof attempt, MISSED by the bedrock audit):** `deepestPoint_exists`
(`Nonempty {w // IsDeepLayers H r B w}` under `hB : B.rank = r` ALONE) is FALSE — H=(3,1,3), r=2,
B=diag(1,1,0): the MIDDLE width H 1=1 bottlenecks the product to rank ≤1<2 ⇒ empty fibre ⇒ Nonempty FALSE.
The HEADLINE is then false too (⨅ over ∅ = ⊤ ≠ finite). Root cause: "rank B=r ⟹ r≤H s" holds only for the
OUTER widths. **Fix (decided): add `(hr : ∀ s : Fin (L+1), r ≤ H s)`** to deepestPoint_exists + deepestPoint
+ deepestPoint_isDeep + product_reduction + deepest_point_reduction + aoyagi_learning_coefficient. It is also
the well-definedness domain of `aoyagiLambda` (M⁽ˢ⁾=H⁽ˢ⁾−r needs r≤H⁽ˢ⁾). **FIXED + MERGED @`2ee02b2`** (hr
threaded through all 6 decls, headline assembles, deepestPoint_exists kept as sorry under new sig; contract
now TRUE, no empty-fibre ⊤). 7th bug closed. **9th issue (L=0 corner):** even WITH hr, false for L=0 (empty
product = identity ⟹ fibre needs B=I; `L=0,H=![2],r=0` has hr✓ but empty fibre) → fix `(hL : 1 ≤ L)`
(L=0 = no network = out-of-model; verified sufficient 484/484). Same DOMAIN-UNDER-SPECIFICATION class as the
7th. fm applying hL + proving deepestPoint_exists (one pass, then I merge). rv-2 commissioned a SYSTEMATIC
DOMAIN-CORNER SWEEP (catch the domain-hole class wholesale, like the weak-existential sweep) + HOLDS the
final contract PASS until hr+hL merges + sweep clean. (Fidelity-issue tally: 9 — all caught before proofs
build on them; the contract is converging to genuine bedrock.)

**rv-2 re-audit @2ee02b2 + DOMAIN-CORNER SWEEP (done):** hr-fix PASS (build green 2851, 10 sorry, axioms
clean, witness CONSTRUCTED for (1,1,1)/r=0 per the standing rule; A1/L1 genuinely proven, no sorryAx; L1 not
vacuous). 9th bug (L=0) INDEPENDENTLY confirmed (decorrelated counterexample). **Sweep result: NO further
hidden corner beyond L=0 — `hr ∧ hL` CLOSE the existence/headline domain COMPLETELY** (r=0→origin OK;
hr-equality boundary OK; only L=0 uncovered). ⇒ once hL lands + the final re-audit runs, the contract domain
is PROVABLY complete (no 10th domain hole lurking) = BEDROCK. The domain-bug class is closed.
Full rung×corner matrix (rv-2): R1 `resolution_charts` is SAFE at L=0 with NO hr/hL (the ONE unguarded
rung — at L=0 dlnLoss is constant ⇒ `rlctAt=⊤` either way, R1's ∃ discharges via `ι=Empty`, ⨅∅=⊤); all
other rungs (S2/S1.x/L1/A1/A2) clean at every corner (L=0, r=0, r-extremal, zero-width, d=0). So R1 needs
NO domain hypothesis — good for its formalisation. **Convention noted:** `rlctAt(≡0 loss)=⊤` in this dev
(rv-2 proved it; literature leaves F≢0's RLCT undefined) — BENIGN (the ≡0 case only at hL/analyticity-
excluded corners; the headline's rlctAt is for a non-≡0 loss, vanishing AT the deepest point not identically,
so the convention never taints the headline). Docstring note on `rlctAt` queued for convention-honesty.

## Live status (per-track)

- **fm-2 (measure track)** — keystone (d7b1ba3) + bridge (b342cd2, axiom-free) + continuity-to-ParamsFlat
  (fb50adc) ALL DONE; measure track COMPLETE. **NOW on the real S1.1 `weightedThreshold_transport`** (heavy
  transport rung; infra banked: continuity homeomorphism + 2-sided box-iff + sSup). Then the deepestPoint r>0
  telescoping (dependent-Fin, routed here post-S1.1). Commits to expedition; rv-2 green-gates behind. Trunk
  @`fb50adc`.
- **fm (algebra track)** — branch `worktree-rung0-defs` (Skeleton-only), based @1bb9e31 (I merge forward;
  no rebase needed — Skeleton independent of keystone). A1-clean + A1-lambdaCore(weak) + L1 + hr-fix DONE +
  MERGED @`2ee02b2`. NOW on `deepestPoint_exists` PROOF (reuses L1 adapted-basis) → then #19 lambdaCore-
  strengthen (waits for pp's genuine statement). **Trunk @`296d3e4`: keystone + A1 + L1 + hr + hL; Skeleton
  sorry 9.** hL MERGED; rv-2 running the FINAL bedrock re-audit (domain now provably complete → closes the
  9-issue fidelity arc). **deepestPoint_exists FULLY PROVEN + MERGED @`9402bba`** (axiom-clean, no sorryAx;
  the r>0 prodAux telescoping CLOSED — fm de-risked the algebra + delegated the HEq cast-wrangling to a
  formaliser + reviewer subagent; statement byte-identical; rv-2 re-auditing). Critical-path rung DONE (feeds
  D1). Skeleton sorry 10→9. **fm now on #19 proof** (genuine lambdaCore, ~200-line balanced-split exchange).
- **pp (design)** — R1 design DELIVERED + 2 increments (binding-divisor correction; value-match downgrade).
  Standing down on-demand; re-engage for R1 value-match execution when fm's L1 lands.
- **rv-2 (review)** — green-gating keystone d7b1ba3; queued: re-audit the hr-corrected contract. Decorrelated.

## Integration topology (current)
expedition/aoyagi-full = integration trunk (fm-2 commits here directly). worktree-rung0-defs = fm's Skeleton
branch (I merge → expedition). Files DISJOINT (fm-2: ParamsFlat/Case111; fm: Skeleton) — contract change is
Skeleton-LOCAL (verified: no refs to deepestPoint/headline/L2/D1 outside Skeleton). Merges are clean. MAIN
working tree has no Lean WIP between fm-2 commits. Controller green-gates via rv-2 (isolated builds) to avoid
the shared-tree build race.

## PROOF-MODULE PATTERN (S1.1+) — eliminates Skeleton contention
Heavy rungs that are Skeleton sorries are proven STANDALONE in Foundations modules, then I WIRE each into
Skeleton single-writer (`exact <lemma> …`, verbatim statement). S1.1 `weightedThreshold_transport` →
`Foundations/S1Transport.lean` (fm-2, option B approved); S1.3/4/5 likewise if fm-2 takes them. Result: fm
owns Skeleton's INLINE rungs (deepestPoint, #19 lambdaCore); fm-2 owns Foundations PROOF-modules; I do the
1-line Skeleton wires at integration. Zero fm↔fm-2 Skeleton collision + it's the per-rung modular split
(build-time), done as-needed rather than big-bang. The wired lemma's statement must match Skeleton's verbatim.
**Refinements (rv-2 full-trunk catch @92a1101):** (1) the proof-module lemma gets a DISTINCT name (`_aux`/
`_impl`) — same FQN as the Skeleton contract decl = duplicate-declaration landmine at wire-in; wire =
`Skeleton.<rung> := <rung>_aux …` (verbatim statement still unifies). (2) a Foundations proof-module is
ORPHANED from the root `DLNFibre.lean` closure until wired (Skeleton imports it) — so the DEFAULT
`lake build DLNFibre` SKIPS it (gate WIP via explicit module-builds; `scripts/sorries` globs so counts it,
but the root build doesn't compile it). The FULL-trunk `lake build DLNFibre` (not module-scoped) is the gate
that catches orphans + collisions — run it at integration, not just the module build.

## 10th fidelity issue — S1.1 bare equality FALSE (analytic-implication gap; fm-2 caught @6dbc880)
The bare-hypothesis Skeleton `weightedThreshold_transport` EQUALITY is FALSE — the reverse `≥` fails two ways:
(1) **surjectivity gap** (w*∉range π ⟹ π⁻¹{w*}=∅ ⟹ RHS=⊤≠finite LHS) → needs `hsurj : Surjective π`;
(2) **Luzin-N gap** (hderiv off-E doesn't make π(E) null; a Cantor-staircase π sends null E→positive π(E), an
F-singularity there adds LHS mass the off-E CoV misses) → needs `hImE : volume (π''E)=0`. The Skeleton
docstring ASSUMED "π(E) null via Luzin-N" but the hyps don't encode it (Mathlib Luzin-N needs DifferentiableOn
ℝ π E). **NEW CLASS** — not a domain-corner (the sweep cleared S1.1's corners) but an analytic-IMPLICATION gap
(hyps don't imply the conclusion), only the proof attempt surfaces it — even on the IsAddHaarMeasure-pinned
statement. fm-2 ESCALATED (didn't silently fix) + delivered both sorry-free: `weightedThreshold_le_transport`
(unconditional ≤) + `weightedThreshold_transport_of_surjective_image_null` (full = under hsurj+hImE, conclusion
defeq Skeleton). FIX: add hsurj+hImE to Skeleton S1.1 (LOCALIZED — doesn't ripple to D1/L2/R1 statements, which
don't expose π; their PROOFS supply the hyps, both hold at the R1 resolution use-site: chart surjective +
exceptional divisor null). Pending rv-2 decorrelated confirm (7th/9th protocol) → fm wires
(`exact …_of_surjective_image_null` + import + the 2 hyps, Skeleton single-writer). R1 design note: R1's
per-chart S1.1-transport invocation must supply hsurj (chart onto nbhd) + hImE (exceptional divisor null).
**rv-2 CONFIRMED (decorrelated + Codex)** both gaps (π=exp surjectivity; π=id+Cantor-staircase Luzin-N) +
fm-2's 2 lemmas PASS; Codex Q3 resolved (hsurj+hImE COMPLETE, no 4th gap). Executing: fm wires S1.1 (+ S1.4).

## S1 batch status (proof-module pattern, fm-2 owned modules → fm wires)
- **S1.1** `weightedThreshold_transport_aux` (S1Transport.lean @20ab62a) — PROVEN under hsurj+hImE (10th issue,
  CONFIRMED). fm wiring (add 2 hyps + `exact` + import; also resolves orphan FLAG 1).
- **S1.4** `rlct_germ_local_aux` (S1Local.lean) — PROVEN, bare statement SOUND (no gap). fm wiring (`exact` + import).
- **S1.3** `rlct_unit_invariant` — **11th fidelity issue:** bare statement FALSE without `Measurable u`
  (non-measurable u → u·F non-measurable → not Integrable → rlctAt=sSup∅=0 ≠ rlctAt F). Fix `Measurable u`
  **rv-2 CONFIRMED** (decorrelated + Codex; Vitali-set counterexample, `IntegrableOn⟹AEStronglyMeasurable`
  crux Lean-verified). `AEMeasurable u` is the minimal hyp but `Measurable u` is the contract choice (cleaner,
  use-site-safe — analytic unit continuous). fm-2 PROVEN `rlct_unit_invariant_aux` under it (S1Local.lean,
  axiom-clean); fm wires (add Measurable u + exact). **All 3 S1 _aux ready to wire: S1.1/S1.4/S1.3** (fm batch).
- **S1.5** `rlct_additive_smooth_block` — **12th fidelity issue (DEEPER):** the disjoint-block additivity is
  FALSE two ways (non-measurable G [gap-class]; G≡0 ⟹ rlctAtOn(0²)=⊤ ⟹ RHS=n/2+⊤=⊤≠LHS [≡0-convention]) AND,
  even fixed, needs heavy Laplace-asymptotic machinery (Mathlib-gap); can't be cited. fm-2 delivered the honest
  substrate @`2cb79cc` (sorry-free: `rlctAtOn_zero_eq_top` [also discharges #24 docstring], `smoothBlock1D_rlct`
  n=1; the false aux NOT carried as a sorry). rv-2 confirming the counterexamples. **L2-ARCHITECTURE STRATEGY
  routed to pp** (additivity-with-hyps vs R1-on-full-loss-subsumed vs smooth-block-alone restatement — how L2
  combines regular ⊕ core). fm-2 proving the smooth-block VALUE `rlctAtOn(Σxᵢ²)=n/2` (general n, needed
  regardless; Mathlib-gap radial integrability). This is a design node, not just a hyp-gap.
  **RESOLVED (pp + Codex, l2-architecture-card):** DROP additivity AND R1-on-full-loss (the latter needs mixed
  principalization of (x,m) — heavier; F=Σx²+core is a SUM not monomial×unit). **Restate S1.5 to the
  smooth-block FUBINI LEMMA:** `rlctAt(Σxᵢ² + core)` in a core normal-crossing chart `= n/2 + min_j(h_j+1)/(2k_j)`.
  PROOF LIGHT (no Laplace): `∫(|x|²+s)^{-c}dx = C·s^{n/2-c}` (radial x=√s·ρ, Beta, finite iff c>n/2) + Fubini
  (s=core≥0) ⟹ core RLCT at shifted exponent ⟹ n/2 + λ_core. Chart-form core=monomial is nonzero-a.e. +
  measurable ⟹ dodges BOTH gaps by construction. APPLIED PER-CHART in R1: λ_full = min_chart(n/2 + λ_core) =
  n/2 + ½ min_t Mval. So L2's regular⊕core = Fubini-lemma + R1-core-resolution + min-over-charts (NOT a
  standalone additivity). fm-2 proving the Fubini lemma; fm restates+wires Skeleton S1.5.
  **Fubini ROUTE (fm-2's call):** the smooth-block case is genuinely CLOSED-FORM (NOT Laplace — Laplace only
  for general both-arbitrary additivity, not ours). Route B (iterated-1D: n=1 Fubini `∫(x²+s)^{-c}=C·s^{1/2-c}`
  iterated, stays on Params-flat product measure) likely cleaner than Route A (radial via
  `integrable_fun_norm_addHaar` [Mathlib HAS it, corrects the earlier gap-flag] + EuclideanSpace-Haar bridge).
  **UPDATE: general-n single-block n/2 PROVEN** (`smoothBlockND_rlct` rlctAtOn(Σxᵢ²)=n/2 on EuclideanSpace,
  S1SmoothBlock.lean @505e0a2, axiom-clean, 201 LoC — the Mathlib-gap was NOT real, radial `integrable_fun_norm_addHaar`
  + ball-truncation + rpow-iff). The FUBINI lemma (the +core combination = n/2+λ_core) is the s>0 EXTENSION of
  that radial machinery (`∫(‖x‖²+s)^{-c}=C·s^{n/2-c}`, Fubini, + monomial-core threshold) — CLOSED-FORM (NOT
  Laplace), in flight (fm-2). S1.3 also PROVEN + ON TRUNK now (S1Local 0-sorry @505e0a2).
  **FUBINI DE-RISK (fm-2 SPECIFY + Codex):** the exact radial identity holds ONLY at ε=∞; finite-ε (RLCT nbhd)
  is asymptotic-only + Mathlib has NO parametric radial integral. So directions SPLIT: ">=/integrability LIGHT"
  (a.e. comparison + Integrable.mul_prod + radial_ball_iff, ~4-6 sublemmas); "<=/non-integrability" (the CUSP
  lower bound — pp re-adjudication SHAVED to ~5-7 sublemmas via EXACT ball-volume `vol{‖x‖²≤s}=V_n·s^{n/2}`
  [measure_ball/addHaar_ball — NOT a parametric radial integral, dodges the gap]; monomial divergence finish).
  **≥ DIRECTION DONE (fm-2, S1Fubini.lean, 110 LoC, axiom-clean, module-green 2676):** `cmpF` (split engine
  `(s+t)^{-(a+b)}≤s^{-a}t^{-b}`) + `joint_integrableOn_weighted` (a.e. cmpF comparison + Integrable.mul_prod +
  volume_eq_prod). rv-2 PASS (#40, axiom-clean, right condition, hGne faithful). Off-Skeleton; controller wires
  into the aggregator at the equality. **≤ DIRECTION fully de-risked** (every atom + Step A `[‖x‖²≤G](2G)^{-c}w ≤
  |F|^{-c}w` handling BOTH G>0 antitone + G=0 hygiene-corner, cuspVol exact `vol{‖x‖²≤s}=ofReal(√s^n)·Vₙ`,
  notIntegrable_rpow, joint_lintegral_top sig — all in scratch; remaining = mechanical Tonelli + factor +
  hcore_top⟹⊤). **STATEMENT-SHAPE DECISION (load-bearing, supersedes the (i)-vs-(ii) routing Q AND the card §B
  "explicit monomial core"): (A) ABSTRACT-CORE SHIFT THEOREM.** fm-2 found the standalone multivar monomial
  divergence `∫_box ∏|y_j|^{a_j}=⊤` is NOT the ~30-LoC elementary fact first estimated — Mathlib has the pi-product
  factorization only for the FINITE/integrable case, not a lintegral=⊤ divergence (custom pi-Tonelli = heavy).
  So BOTH the standalone build (heavy) and S2-reuse (axiom-import) are dodged by stating S1Fubini ABSTRACTLY:
  `rlctAt(Σxᵢ² + core) = n/2 + rlctAt(core)` — the pure "+Σx² shifts the RLCT by exactly n/2" shift theorem, with
  the core's integrability (≥, hGne+hy) and divergence-at-shifted-exponent (≤, hcore_top) as EXPLICIT hypotheses
  (symmetric, honest, dodge both 12th-finding levers by construction). The monomial+S2 obligation MOVES to R1's
  per-chart use-site: R1 supplies rlctAt(core)=S2's ⨅axisRatio for its resolved monomial, and hcore_top follows
  from that value by the sSup definition (NO hand-built multivar integral). Strictly cleaner — S1Fubini stays
  axiom-clean + monomial-machinery-free, the shift is its sole content, and S2 lands exactly where it belongs
  (the monomial RLCT). pp confirming the R1 use-site discharge (3 hyps + cover-composition) in parallel. **λ_core=0
  EDGE (rv-2):** the c=a+b split (b>0) covers c<n/2+λ_core only for λ_core>0; the λ_core=0 regime routes through
  `smoothBlockND_rlct` (=n/2) directly — fm-2 handles in the equality-lift (likely vacuous at the deepest point
  where the core is genuinely singular, but kept general). The <= IS NEEDED (R1 UPPER = binding-chart divergence;
  S2 alone doesn't cover the SUM Σx²+monomial — +Σx² shrinks the integrand so divergence is non-trivial). So R1
  is heavier than first scoped (Fubini-per-chart + multiplicity-control R1.2 + cover R1.6) but all designed +
  tractable, and the abstract shift makes the Fubini-per-chart step a clean plug-in.
**Use-site obligation (tracked):** hsurj+hImE (S1.1) + Measurable u (S1.3) must discharge at D1/R1 (resolution
charts: surjective onto nbhd, exceptional-image null, analytic unit measurable). The bare-under-specification
gap-class is RECURRING across the analytic rungs — caught reliably by the proof attempts + escalation.

## R1 design BANKED (pp, thread 14) + R3b DECISION + value-match DOWNGRADE
- **Value/atlas split.** VALUE `rlctAt(‖∏C‖²)=½·min_t Mval(t)` (pinned by codim S(t)=Mval, thread-03) vs
  explicit CHART ATLAS (Aoyagi affine blow-ups).
- **Binding-divisor mechanism** (pp self-corrected the wrong "telescoping" framing): per branch, ONE blow-up
  of the residual-block-zero center (codim EXACTLY Mval(t)) is the binding divisor (k,h)=(1,Mval−1), ratio
  ½·Mval; min over branches = ½ min_t Mval = λ. (Telescoping per-rank-drop would give ½·min(cᵢ) = TOO SMALL.)
- **VALUE-MATCH DOWNGRADE (pp §8, verified L=3):** the headline's value-match does NOT need the full atlas —
  only the minimizing branch's binding divisor, produced by **iterated L1 to the residual block (REUSES fm's
  L1 + deepestPoint_exists machinery)**. Route: (i) iterate L1 → codim-Mval residual block; (ii) residual =
  codim-Mval coord subspace (thread-03); (iii) blow up → divisor-ratio lemma → ratio ½·Mval [UPPER bound,
  L1-reuse, cheap]; (iv) cover/exhaustiveness inequality over strata [LOWER bound, the residual real work].
  Full normal-crossing atlas DEFERRED (only to strengthen the statement beyond value-level). R1's "mountain"
  status partly downgraded.
- **Residual-block claim NAILED (pp §8, general-L; verified L=2,3,4 + decorrelated Codex):** after the
  pivot split, the residual cutting S(t) is a REGULAR SEQUENCE of length EXACTLY Mval(t) — not
  over-determined (the full interval rank-pattern r_{ab}, a≥2, adds NO independent generators; inner
  constraints are CONSEQUENCES), not coarser. So {residual=0} is a clean smooth codim-Mval(t) coordinate
  subspace ⇒ binding divisor (k,h)=(1,Mval−1), ratio ½·Mval(t), rigorous at general L. STRUCTURE: the
  residual is NESTED Schur-blocks R₁..R_L (R_j = D_j−C_jA_j⁻¹B_j per layer), `S(t)∩chart = {R₁=…=R_L=0}`,
  Σ|R_j|=Mval — jointly coordinates ⇒ one smooth center. CAUTION: a final-PRODUCT residual alone cuts the
  COARSER {∏=0} (union over profiles), NOT S(t) — must use ALL R_j. CAVEAT (Codex): ratio ½·Mval holds at a
  GENERIC point of the minimizing stratum (nongeneric suffix-vanishing points need more blow-ups but don't
  affect the value-match). pp self-caught + dropped a wrong "inner intervals stay generic" sub-claim (what
  holds is codim=Mval exactly, which is all the mechanism needs).
- **Codex correction adopted:** prefix-stratum partition right for the VALUE but too coarse for a literal
  atlas (charts refine by full rank-pattern); R1↔Adm is VALUE-level, NOT a chart bijection.
- **R1 LOWER BOUND + complete decomposition (pp, done) — MULTIPLICITY-CONTROL finding (pre-execution catch):**
  UPPER (≤ ½ min Mval) = ONE binding-divisor chart (cheap, L1-reuse). LOWER (≥ ½ min Mval) needs the FULL
  cover + a sharp finding: **the lower bound CANNOT come from codim alone** — the divisor ratio `(h_E+1)/(2k_E)`
  depends on F's VANISHING ORDER k_E, not codim (counterexamples: `rlctAt(x^{2k})=1/(2k)<½·codim`; `(x²+y²)²`:
  1/2≠1). So **R1.2 = MULTIPLICITY CONTROL** (`h_E+1 ≥ k_E·min Mval` per divisor), HOLDS for our core via
  regular-sequences⟹k_E=1 but PROVEN per-divisor, NOT a codim shortcut. DECOMPOSITION (execution-ready): R1.1
  chart family[L1] + R1.2 multiplicity[NEW] + R1.3 codim=Mval[thread-03] + R1.4 Fubini-per-chart + R1.5
  S1.1-min-over-cover + R1.6 cover/exhaustiveness[NEW] + R1.7 S2. NEW lifts = R1.2 + R1.6 (the real lower-bound
  work). Route: complete explicit resolution + per-divisor monomial check (one-citation-clean); SoS+codim DEAD.
  Subtleties: strata-not-components (Z=⋃S(t)); local-vs-global codim (origin sees min Mval); properness (w/ S1.1).
  pp+fm EXECUTE when S1.1+Fubini land (close); R1.2 first.
- **DECISION R3b** (self-contained, one-citation). R3a (cite LR `rlct=codim/2`, arXiv:2411.19920) OUT:
  violates one-citation scope (codim = THE new content) + Aoyagi-independence. Surfaced to operator as
  informational/override-able.
- **No hidden hypotheses** (Codex §4): char-0, positive widths, r≤H s (=the hr fix). Toric/Newton route DEAD.

## WIN — λ-citation ELIMINABLE — now DEMONSTRATED END-TO-END (bridge @`b342cd2`)
The (1,1,1) bridge `case111_rlct_eq_monomialThreshold` is CLOSED sorry-free (fm-2) ⇒ **`case111_rlct` is the
FIRST fully sorry-free + axiom-free end-to-end RLCT result** (`#print axioms = [propext, Classical.choice,
Quot.sound]`, NO sorryAx, NO monomial_rlct, NO native_decide). So λ is PROVABLY axiom-free for (1,1,1) — the
WIN is no longer just probed, it's demonstrated. General case = labour (no wall). Reviewer-agent fidelity
survived; rv-2 green-gating decorrelated. **Banked REUSABLE S1.1 infra (general in H):**
`continuous_paramsEquivFlat`/`_symm` (flattening is a HOMEOMORPHISM), `prod_paramsEquivFlat` (coord-product
preserved), `prodBoxSymm_rpow_integrableOn_iff` (2D 𝓝0 box-iff) — feeds the real S1.1 + R1. Only θ-order
stays the genuine analytic seam (S2 order-half).

## #19 genuine A1 statement — MERGED to trunk @`7986597`, rv-2 PASS, GREEN
Weak free-choice existential REPLACED by pp's candidate-d: `∃ c ≤ L, 1 ≤ c ∧ lambdaCore M = cleanCore c
(sortedSmallest M c)` (m PINNED via `sortedSmallest` = M's c+1 smallest reduced widths). **rv-2 PASS** (genuine
per discriminator; matches pp's ACHIEVER, NOT an extremum — verified 19600 cases, min_c/max_c refutations
reproduced; sortedSmallest faithful). 8th issue resolved at the STATEMENT level on trunk. Skeleton compiles
green (2534 jobs). Proof = sorry (~200-line balanced-split exchange, off-critical-path) — fm sinking it next
(gate OPEN). **Skeleton sorry 9→10 — correct + honest: a genuine sorry replaced the vacuous weak PROOF.**
Also merged: deepestPoint r=0 + Dblock_rank (r>0 telescoping still sorry, fm's). Cosmetic lints in fm's code
(show→change @534, deprecated Finset lemma @706, <;> @738) — non-blocking, fm cleans on next touch.
**#19 PROOF progress:** Step 1 `balancedSplit_min` PROVEN (balanced split minimises Σq²; e9e251d, reusable).
ROUTE-GAP found (proof attempt, again): card step-3 "per-c lower bound" was the FALSE `min_c` reading
(cleanCore NOT monotone in widths — `[1,2,4]`vs`[1,2,7]`: 2 vs −2; min_c/max_c refuted) — STATEMENT still
correct+total, only the ROUTE needs reframing to: per-T bound on T's OWN breakpoint widths (via balancedSplit_min)
+ **PERM-INVARIANCE of lambdaCore** (`lambdaCore M = lambdaCore M∘σ`, ~200-line Adm-cone exchange) + sorted-M.
#19 OFF the headline path — fm doing the S1 WIRES (S1.1/S1.3/S1.4, critical-path) FIRST.
**#19 keystone PARKED (decision d):** fm probed it — perm-invariance of lambdaCore is a MIN-LEVEL no-bijection
wall (Adm cones + Mval-multisets genuinely DIFFER under σ — 560/1700 & 1140/1700; holds only AT the min ⟹
multi-hundred-line explicit minimizer characterization, no slick transport). OFF-headline-path (headline uses
aoyagiLambda's min-def, closes sorry-free WITHOUT #19's proof). **THEN UN-PARKED via ROUTE B (fm, 2df8bf4):**
cleanCore depends only on the width MULTISET (Σm², Σm symmetric), so #19 needs NO global perm-invariance — a
LOCAL achiever analysis (T* breakpoint-multiset = sortedSmallest, via multiset-symmetry) + the per-T lower
bound (balancedSplit_min, DONE) suffices. ~200 lines, perm-invariance-FREE (avoids the wall, not solves it),
3900/3900. **pp VALIDATED + reframed (a1-route-reframe.md):** perm-inv = COROLLARY of the sorted-form
characterization (`lambdaCore M = lambdaCore (sort M)`), NOT proven via the Adm-cone bijection (saves the
beast). Residual hardness = the SMALLEST-WIDTHS-FORCING sub-lemma (on sorted M the minimizer's breakpoint
widths = the ℓ*+1 smallest, FORCED over every T via the `(M^S−H)` factors) — MUST be per-T-over-Adm-cone, NOT
a widths-extremum (exactly where the false min_c lived; the trap). UPPER (achiever) + LOWER (per-T
balanced-split + forcing). fm executing route B. So #19 is now a clean bounded build. fm sequence: wire
S1.1+S1.4 → #19 route B → R1/L2/D1
(critical-path beats off-path as Fubini lands for R1).

**S1 WIRES — S1.1 + S1.4 CLOSED + GREEN-GATED on trunk @`7258a36` (fm `aacdc7a`, FF-merged + full `lake build
DLNFibre` GREEN, 2855 jobs).** Skeleton sorry 10→7. Both rungs INDEPENDENTLY axiom-clean (controller `#print
axioms`): `weightedThreshold_transport` (S1.1, +hsurj+hImE [10th]) and `rlct_germ_local` (S1.4) = `[propext,
Classical.choice, Quot.sound]` — no sorryAx, no monomial_rlct. Orphan FLAG resolved for S1Transport+S1Local
(now in Skeleton's import closure). **7 remaining sorries:** S1.3 rlct_unit_invariant (138 — wire next,
Measurable u [11th] blessed + _aux proven), S1.5 rlct_additive_smooth_block (169 — awaits fm-2's Fubini lemma),
L2 (882), D1 (896), R1 (921), #19 lambdaCore (1055), A2 (1196). rv-2 auditing S1.1/S1.4 + the Fubini ≥ half.
NEXT (fm): wire S1.3 → then D1 `deepest_point_reduction`. S1Additive/S1SmoothBlock/S1Fubini stay orphans until
S1.5/L2 wire them (controller adds S1Fubini to the aggregator at that point).

**#19 CHECKPOINT (fm @`88cf38e`, worktree-rung0-defs) — ENGINES PROVEN + ROUTE CORRECTED + KEYSTONE PARKED (decision b).**
Two engines axiom-clean: `balancedSplit_min` (lower-bound engine `Σ balancedSplit² ≤ Σqᵢ²` at fixed sum;
re-derived solid after trunk syncs, `43b443e`) + `cleanCore_perm` (cleanCore multiset-symmetry, route-B crux,
`cfeec6f`). **ROUTE CORRECTED AGAIN (fidelity catch, now in the lambdaCore_eq_clean docstring):** the route-B
"per-c lower bound / min_c" framing is FALSE (M=[1,1,4]); AND Codex's first "single-c achiever rule
(aᵢ ≤ ⌈Sᵢ/i⌉)" is ALSO FALSE (278/3900 fail). The CORRECT rule (0 failures exhaustive widths 0..3 L≤4 +
3900/3900 widths 1..5): `c* = largest c with the CUMULATIVE predicate ∀1≤i≤c, aᵢ ≤ ⌈Sᵢ/i⌉` on sorted M, plus
the exact per-T identity `Mval = Σₖ gapₖ·(wₖ−Hₖ)` over strict-descent positions. **KEYSTONE PROPER = a dedicated
multi-session lift (~250-350 lines), NOT a bounded sub-thread:** two sub-lemmas on unsorted M — (1) per-T lower
bound (descent-set **dependent-Fin reparametrisation** of each T + complete-square + balancedSplit_min) +
(2) achiever construction + Adm-membership. The dependent-Fin descent reindexing is the genuine hard bulk (the
minimizer's breakpoint widths aren't literally sortedSmallest — they coincide only at c*; the "perm-invariance
wall" persists at this level). **DECISION (b): PARK the keystone, ROADMAP it** — it is WELL-SET-UP (genuine
statement + 2 engines + corrected cumulative-predicate route all banked → a dedicated tide later, after the
headline / when capacity); #19 is OFF the headline path (headline uses aoyagiLambda's min-def directly). **fm
PIVOTED to CRITICAL-PATH:** S1 wires (S1.1/S1.3/S1.4) → D1 `deepest_point_reduction` → R1 EXECUTION (with pp,
when Fubini lands) → L2 → T. Bounded #19 engine-nibbling (e.g. the per-T Mval identity) is FILL only, never over
the critical path.

**#19 ROUTE ADVANCE (fm @`85b0077`, supersedes the dependent-Fin descentSet plan — much cleaner):** the
**EDGE-VARIABLE TRANSFORM** `q_j = M⁽ʲ⁺¹⁾ + (u_j − u_{j+1})` on the FIXED level sequence — a fixed-`Fin L`
reparametrisation, NO dependent-Fin descentSet reindex (that was the hard bulk; dissolved). Exhaustively verified
(0 failures L≤4). NEW engines axiom-clean: `karamata_sq` (Karamata-for-squares via Abel summation, general/
reusable), `edge_identity` (`2·Mval = Σ(edgeQ)² − Σ(Mseq)²`), + QFeasible positional prefix bounds (Adm ⟹
QFeasible). **#19 now reduces to ONE clean gate** (in the docstring): the **smallest-k-sum majorization**
(`∀k, Σ(k smallest edgeQ) ≤ Σ(k smallest Y)` ⟹ karamata_sq). Mathlib v4.29 has NO Karamata/Schur/k-smallest API
(confirmed) ⟹ ~150-250 lines new combinatorics; proven irreducible (pointwise-after-sort FALSE q=[1,3]vs[2,2];
prefix/tail split undershoots — convexity essential). **STILL PARKED (decision b, reaffirmed 3rd time):** the gate
is a DEDICATED TIDE LATER (after the headline), even better set-up now (edge-transform + karamata_sq + QFeasible
all banked = one self-contained majorization theorem). fm REDIRECTED to the pending critical-path Skeleton tasks
(S1.3 wire + the 13th-finding restatement, which it had skipped for this #19 work) → then D1. Process note logged:
don't dispatch sub-formalisers per task (seat-reuse) + no further cycles on parked #19.

## Measure-side architecture — ROUTE A++ (DECIDED; now ACTUALLY green)
Matrix-wall paid-ONCE + contained by interface discipline. `Params.volume`=nested Measure.pi is **rfl**; fiber
instance = section-local `instance` (NOT a global Matrix instance, NOT a goal-type `letI` — elaboration order).
**Σ-form throughout via `piCurry.symm`, never `curry`/`×`** (`MeasurableEquiv.curry` has NO measurePreserving
companion in Mathlib; `piCurry` does); final reindex `Σ…≃Fin N` via `equivFin`; `measurePreserving_pi` =
piCongrRight MP, pass μ,ν explicitly. (pp corrected an earlier overclaim — it had verified type-level +
individual lemmas but the MP body was sorry'd; now the FULL body compiles EXIT=0 v4.29. Decision unaffected,
firmer.) These gotchas are REUSABLE for S1.1 + R1 measure facts. Downstream states facts on `Fin N → ℝ`, pulls
back via `integrableOn_comp_preimage` — never re-touch Matrix.

## Rung map (scoped)
- DONE: keystone paramsEquivFlat (d7b1ba3); A1 clean_eq_printed (c234651, to merge).
- NEXT (fm): hr statement-fix [contract-critical] → lambdaCore_eq_clean → L1 → deepestPoint_exists proof.
- NEXT (fm-2): (1,1,1) bridge (#12) → then S1.1 (heavy) + S1.3/4/5.
- THEN: L2 (needs L1+S1.5) · D1 (needs S1) · R1 value-match (needs L1 + S1.1; pp re-engaged) · A2 (θ-seam, post-R1).
- Assembly T: assembles from D1+L2 (+ hr threaded).
- Two hard builds remain: S1.1 + R1's cover-inequality (lower bound).

## STATUS @ 2026-06-21 ~01:30 (trunk @c32b694; Fubini @e2a3f0c)
- **S1 WIRE BATCH COMPLETE — S1.1/S1.3/S1.4 ALL CLOSED + green-gated + axiom-clean** (@c32b694; build green 2855,
  Skeleton 6 sorries; rv-2 PASS on S1.1/S1.4, S1.3 audit queued). The S1 transport/locality/unit substrate is DONE;
  only S1.5 (Fubini) remains of S1. 6 sorries: S1.5, L2, D1, R1, #19, A2.
- **R1 EXECUTION LAUNCHED** (pp leads math, fm formalises): pre-Fubini parts first — R1.1 chart construction
  (L1-reuse) + R1.2 multiplicity-control (`h_E+1 ≥ k_E·min Mval` per divisor, NOT codim shortcut); R1.4
  (Fubini-per-chart) plugs fm-2's shift theorem when the lift lands; obligations folded in (unit-absorption via
  S1.3, hcore_top endpoint, min-over-cover factorises n upstream-fixed). The mountain.
  - **R1.2 ROUTE — VERDICT: route B REFUTED → route-A-CONCRETE (pp + decorrelated Codex, INDEPENDENTLY IDENTICAL +
    witnesses).** ⚠️ CORRECTS my prior "L1-pivot charts resolve it" bank — that reading is WRONG. **THE DECIDER:**
    a residual product of length q≥2 has ‖∏C̃‖² with ordinary VANISHING ORDER 2q (NOT 2); regular changes (= L1)
    PRESERVE ordinary order ⟹ **L1-alone can NEVER expose the core as a smooth coordinate-square block** (route B
    is FALSE). The product-structure concern I gated on was REAL + it KILLS B. WITNESSES: (1,1,1) F=c₁²c₂² (monomial
    NC, only easy case); (1,2,1) F=(a₁b₁+a₂b₂)² (singular quadratic cone, first non-monomial); (2,2,2) F=‖AB‖²
    ord_0=4, Hessian ZERO, codim-3 irreducible, rlct=3/2 via radial/angular blow-up. So a **genuine BLOW-UP is
    REQUIRED + multiplicity-control is NON-VACUOUS** (k=1 on the EXCEPTIONAL divisors, post-blow-up, via the
    pos-def-REAL initial form — over ℂ fails at (x²+y²)²). **BUT not the abstract-infra mountain: route-A-CONCRETE**
    = explicit POLYNOMIAL blow-up charts (A=tA'; (2,1,2)=(x,xy,z,zw); etc.) with vanishing Jacobian on the
    exceptional locus, **S1.1 carrying the change-of-variables** (its hsurj+hImE hyps are EXACTLY for the blow-up's
    non-injectivity / null exceptional image — the 10th-finding design was built for this). NO Mathlib blow-up
    primitive. R1 = MEDIUM (explicit-poly-chart resolution + S1.1 + non-vacuous mult-control + cover). fm: do NOT
    build (B); the validate-small φ's (φ=id (1,1,1); explicit-poly (2,1,2)/(2,2,2)) ARE route-A-concrete charts.
    Codex sharpenings folded: (#2) R1.2 stays BARE (divisor inequality), assembly
    applies 1.unit-absorption → 2.monomial_rlct → 3.R1.2 → 4.S1Fubini SEPARATELY; (#3) Mval = CORE codim (reduced
    widths), assembly = **n/2 + B/2** (don't double-count the regular n). **fm seeded with R1.2a/b** (axisRatio
    arithmetic, zero-dep) + the route-independent (1,1,1) gate (xcheck vs `case111_rlct`); pp designing R1.1 charts
    validate-small-first ((1,1,1)→(2,1,2)→(2,2,2), symbolically verified). Climb order: R1.2a/b → R1.3 codim →
    R1.1 charts → R1.6 cover → assembly.
  - **14th FIDELITY FINDING (pp, load-bearing) — `resolution_charts` ORPHANED + MIS-SCOPED → RE-SCOPE to CORE
    (controller APPROVED):** (1) it's consumed by NOTHING (product_reduction doesn't call it ⟹ R1 was about to be
    built proven-but-unplugged); (2) it states the FULL-loss RLCT = ⨅ monomialThreshold (a MIN), but the full-loss
    RLCT = n/2 + ½·min Mval (a SUM — the reg n/2 is ADDITIVE via Fubini, not a min-direction) ⟹ FALSE for r>0; the
    (1,1,1) validate case had r=0 (n=0) so it didn't exercise the reg-term. FIX: re-scope to `rlctAt(core) wstar =
    ⨅ monomialThreshold` (R1's genuine content), and WIRE the assembly into product_reduction:
    `dlnLoss(deepestPt)` →[block_elimination] reg⊞core →[S1Fubini] n/2+rlctAt(core) →[resolution_charts(core)]
    n/2+⨅monomialThreshold →[A1] n/2+½·min Mval = aoyagiLambda. Clean separation: **R1 = core resolution; L2 =
    the assembly (split+Fubini+R1+A1); A1 = arithmetic.** The re-scope is REQUIRED for composition (S1Fubini takes
    rlctAt(core)). pp pins the corrected stmt + the `core` (∏C^(s)) object → fm restates + wires product_reduction;
    R1.1 charts resolve the CORE ‖∏C‖² (NOT full dlnLoss). Supersedes the stale-docstring item (whole stmt re-scoped).
- **S1.5 restatement+wire deferred to ONE pass** at fm-2's Fubini lift-close: I relay the complete signature
  (hGmeas + hGne + `[ProperSpace]`/`[IsFiniteMeasureOnCompacts]` instances) → fm restates + wires `exact` in one go.
- **FUBINI n=1 EQUALITY PROVEN** (fm-2, S1Fubini.lean @e1cf73c, 564 LoC / 17 thms, ALL axiom-clean): `step_rlct :
  rlctAtOn(x²+H)(0,y0) = ½ + rlctAtOn H y0` (H≥0, Measurable H, hHne germ-a.e.≠0; core space ProperSpace +
  IsFiniteMeasureOnCompacts). The **hardest analytic content of the whole expedition is DONE** — both directions:
  ≥ (step_rlct_ge: integrability split + sSup-lower-bound, ENNReal split idiom, admissible_downset); ≤
  (step_rlct_le: the cusp — step_lintegral_top contrapositive + core_adm_of_joint_adm open-witness wrapper via the
  {H≤R²}∪{H>R²} split; NO continuity needed for measurable H, the resolved subtlety). Measure-route B (1-D
  interval vol, no addHaar/EuclideanSpace bridge — lighter; cusp proven ONCE + reused per induction). **✅ S1.5
  ENGINE COMPLETE @ad1f313 — `rlct_additive_smooth_block_aux` (general-n shift `rlctAtOn(Σxᵢ²+G²)=n/2+rlctAtOn(G²)`)
  DONE + controller-VERIFIED axiom-clean (builds 2644 jobs, [propext,Classical.choice,Quot.sound], no sorryAx / no
  monomial_rlct).** The HARDEST analytic content of the expedition is proven (both dirs + cusp + down-set + sSup +
  λ_core=0 + the finPeel/chartN measure-preserving iteration). Minor: unusedSectionVars lint on [BorelSpace Y]
  (cosmetic). REMAINING for S1.5: fm wires `exact rlct_additive_smooth_block_aux` into the restated Skeleton
  statement (Skeleton-import pulls S1Fubini into the closure) → green-gate → rv-2 audit. **The whole S1 analytic
  substrate (S1.1/S1.3/S1.4 wired + S1.5 engine proven) is now COMPLETE.**
- **R1 DIFFICULTY MAP (pp general-atlas design + honest correction):** **R1.3 = LIGHT** — codim is a ℕ COUNT
  identity (∑ residual block sizes = Mval), NOT the determinantal-codim theorem; **Mathlib v4.29 gap GONE**
  (decorrelated-Codex + verified). **R1.1 = MEDIUM** (pivot recursion on L; base L=1 = smooth block via
  smoothBlockND_rlct, step = explicit-poly blow-up + recurse). **R1.6 (general cover) = THE MOUNTAIN** — the
  headline EQUALITY needs the LOWER bound (rlct ≥ ½min Mval), which needs the COVER complete (no missed worse
  divisor; codim-shortcut FALSE per x^{2k}/(x²+y²)², D1 doesn't give per-point LB) ⟹ critical-path, no shortcut.
  pp HONESTLY corrected its own "R1 medium" drift → R1.6 is where the difficulty concentrates; general-M may be a
  GENUINE WALL.
  - **R1.6 SHARP BOUNDARY + HEADLINE-REACH DECISION (pp detailed cover design + decorrelated Codex; controller
    adjudicated):** FIXED-M = INTRICATE-STANDARD, **provable now** (resolution = finite tree depth ≤L−1, unrolled
    to a finite explicit leaf-chart list; cover = finite sum, ONE Mathlib single-c-o-v per leaf; (2,2,2)=24 charts;
    NO recursion infra). GENERAL-M = **RESEARCH-WALL** (decorrelated-identical pp+Codex): n/tree/φ_i depend on M ⟹
    needs the recursion-as-a-theorem = the two missing-infra obligations **G3 (strict-transform tracking over
    arbitrary rank vectors) + G5 (gluing iterated c-o-v into ONE global integral identity; Mathlib has SINGLE
    c-o-v only)**. The cover is UNAVOIDABLE for the lower bound (Codex Q3 FACT; codim-shortcut false).
    **DECISION: (1) fixed-M LADDER near-term + (2) general infra (G3+G5) ROADMAPPED; (3) axiomatize-cover RULED OUT**
    (breaks one-citation / awkward-middle). LADDER (each a complete axiom-clean-mod-S2 headline instance +
    validates a machinery piece): (1,1,1) monomial [no cover] → (2,1,2) **Fubini-PRODUCT** [disjoint vars separate,
    NO blow-up — pp refinement] → (2,2,2) first TRUE cover [24 charts] → up the M-ladder. **DELIVERABLE FRAMING:**
    the full machinery (S1·Fubini·R1-fixed-M·A1·assembly) + the headline PROVEN for ladder cases; the FULLY-GENERAL
    headline = those + the named G3+G5 research obstruction (honest partial, NOT a false general claim). Assessing
    whether **G5 (abstract c-o-v-tree-gluing) is separable + buildable now** as a down-payment on the general lift.
    **OPERATOR SCOPE FLAG:** the general-M headline is gated on the G3+G5 research-infra lift — surfaced for the
    operator's steer (attempt the lift vs deliver ladder+roadmap); proceeding with the ladder meanwhile (no stop).
  - **(2,2,2) FULL COVER CLIMBED + VALIDATED (pp, exact-symbolic):** two nested blow-ups (faithful to Aoyagi
    Lemma 2/Thm 3): step-1 blow up {A=0} (4 charts, x-divisor ratio 2) → Lemma-2 regular split → step-2 blow up
    (3 charts, s-divisor ratio 3/2 = binding). **GENUINE HOLE caught+closed (validate-small working):** the 3
    step-2 charts are NOT uniform — E-/F0-pivot residuals are positive units (clean monomial×unit leaves), but the
    **δ-pivot residual U(origin)=0 is a SMOOTH-4-BLOCK** (v²+w²+G'²+H'²), so the δ-leaf = x²s²·(Σ⁴y²), NOT
    monomial×unit. Closed by CHECKING (not assuming): block rlct = 2 ≥ binding 3/2 ⟹ s-exceptional still binds at
    3/2 = ½·Mval(deepest), θ=1. Cover SOUND. **FIDELITY → Option A (BLESSED, fixed-M):** monomialize the smooth
    block (ratio-preserving — the cone Σⁿy² blows up to exceptional ratio EXACTLY n/2 = its rlct), so RHS
    `⨅ monomialThreshold` stays LITERALLY TRUE + leaves uniform. **DESIGN REFINEMENT:** the atlas has a THIRD
    block-monomialization layer ((2,2,2) is NOT 4×3=12 simple leaves; δ-branch subdivides into a 4-chart Σy²
    blow-up). **A-vs-B for GENERAL-M (open, part of the tractability verdict):** Option A's 3rd layer may COMPOUND
    G3/G5; Option B (block leaves bounded directly via smoothBlockND_rlct+Fubini, no extra layer, heterogeneous
    cover sum) reuses existing machinery — pp weighing as part of the general-M verdict. (2,1,2) confirmed NOT a
    cover (Fubini-product, disjoint vars, rlct=min(1,1)=1=½·Mval — separate small lemma).
  - **LOWER-BOUND SOUNDNESS SETTLED (pp + decorrelated Codex) — the general result is now mathematically PROVEN
    (on paper), so G3+G5 is pure FORMALIZATION labour, NOT open math.** The worry: a weakly-decreasing
    NON-admissible (t_L≠0) stratum with Mval < min_Adm (e.g. (2,2,2) t=(1,1), Mval=1 < min_Adm=3) — if blown up,
    exceptional ratio 1/2 < 3/2 would BREAK the LB. RESOLUTION: on {∏C=0} the product has rank 0 ⟹ **t_L=0 ALWAYS
    on the zero-locus ⟹ non-admissible strata are NEVER centers** (admPred's t_L=0 = "in the zero-locus"); every
    exceptional is admissible, k=1, h=Mval(t)−1, ratio ½·Mval(t), min over Adm ⟹ the bound. So the LB is
    structurally TRUE via the flag-resolution. **Codex Q4 lct-shortcut REJECTED as a trap** (rlct=½·lct(I)): (1)
    real-vs-complex unproven coincidence, (2) 2nd citation + breaks Aoyagi-independence (Lehalleur–Rimányi/
    multiplier-ideals), (3) black-boxes R1's content — cross-check only, NOT a proof path. So the headline-reach is
    now: **general theorem PROVEN on paper (decorrelated-sound); general Lean formalization = G3+G5 construction
    labour (roadmapped); fixed-M ladder formalized.** Operator scope flag refined: the lift is formalization-labour
    of a SETTLED result, not open research.
  - **G5-ABSTRACT SEPARABLE + BUILDABLE NOW (pp, checked vs Mathlib) → wall reduced to G3 alone.** G5 = `∫⁻_U|F|^{-c}
    = Σ_leaves ∫⁻(|F∘φ_i|^{-c})|Jac φ_i|` = [lintegral cover-additivity] ∘ [single c-o-v per chart], by finite
    induction on the depth-≤L−1 tree. Both Mathlib FACTS: single c-o-v = `lintegral_image_eq_lintegral_abs_det_
    fderiv_mul` (Jacobian.lean:1189) — over **lintegral (ℝ≥0∞) ⟹ NO integrability side-conditions** (the key; the
    threshold integrand is ∞ above rlct, ℝ≥0∞ handles it); + cover-additivity. ONE friction (not a wall): the lemma
    wants InjOn (blow-ups injective only OFF the null exceptional) → ADAPTER: apply to chart-minus-exceptional, the
    exceptional is null (`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`). Intricate-standard, REUSABLE. **DECISION:
    BUILD G5-abstract (assigned fm-2, the measure specialist) — it's needed for the (2,2,2) cover's ∫=Σ∫ anyway (a
    G5-instance), reusable, and ISOLATES G3.** RESIDUAL (honest): **G3 (strict-transform tracking over arbitrary
    rank vectors — quiver-determinantal geometry Mathlib lacks) STILL the genuine general-M research piece**;
    G5-abstract isolates it, does NOT dissolve it. Refined roadmap: **general headline = ladder instances +
    G5-abstract (BUILT) + G3 (named open obstruction).**
    - **#52 SIMPLIFIED (pp, g5-abstract-statement.md): the LADDER needs only the SINGLE-STEP lemma** `∫⁻_U g =
      Σ_i ∫⁻_{V_i\Z_i} |det fderiv φ_i|·g∘φ_i` (finite a.e.-disjoint null-cover) — NO abstract rose-tree datatype.
      The (2,2,2) cover = finite compositions of the single-step lemma (A-blowup 4 ∘ step-2 3 ∘ block 4 = 24
      leaves). The abstract-tree form is DEFERRED to general-M (part of the G3 roadmap, not the down-payment).
      Mathlib anchors all checked (lintegral_image_eq_lintegral_abs_det_fderiv_mul + addHaar_image null + lintegral
      set-additivity); ℝ≥0∞-not-Bochner load-bearing. So #52 is the reusable single-step atom, tractable now.
      SEQUENCING: fm → (2,1,2) [product-MIN, no G5 dep] ∥ fm-2 → #52 single-step; then fm → (2,2,2) instantiates it.
- **13th FIDELITY FINDING (fm-2, proof-attempt-as-audit):** the committed Skeleton `rlct_additive_smooth_block`
  (line 169) is stated BARE (no hygiene on G) and is LITERALLY FALSE — germ-vanishing G² (or G≡0) ⟹ RHS=n/2+⊤=⊤,
  LHS=n/2; Lean-provable from `rlctAtOn_zero_eq_top` (S1Additive:67). The docstring ADMITS false but the SIGNATURE
  is bare = self-contradictory contract (the 12th finding's restatement was documented, never executed in the sig).
  FIX (controller-decided, fm executes single-writer, keep sorry): add `Measurable G` + a germ-non-vanishing hyp.
  **CONTROLLER CALL: hHne (G²≠0 a.e. near y0), NOT fm-2's hGfin (rlctAtOn(G²)<⊤) — hGfin is UNSOUND.** They are
  INDEPENDENT (not equal as fm-2 believed): hGfin admits a FALSE case. AIRTIGHT WITNESS (controller-derived,
  n=1,Y=ℝ,y0=0): G(y)=y·[y>0] ⟹ G²=y²·[y>0]; rlctAtOn(G²)(0)=1/2<⊤ (hGfin HOLDS) but LHS rlctAtOn(x²+G²)(0,0)=1/2
  (the y≤0 slice is pure x², ∫(x²)^{-c} diverges for c≥1/2, CAPPING the joint) ≠ RHS 1/2+1/2=1 ⟹ equality FALSE
  under hGfin. hHne excludes it (G²=0 on positive measure ⟹ ¬hHne). hGfin ALSO over-excludes true cases (G²=1:
  rlctAt=⊤, equality ⊤=⊤). So hGfin is wrong both ways; hHne is the sound hyp AND what fm-2's step_* already carry
  (the H=0 corner + cmpF a.e.-positivity). fm-2 ACCEPTED hHne. **EXACT LOCKED FORM** (relayed to fm; restate
  batched with S1.3, keep sorry): `(hGmeas : Measurable G) (hGne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), G z ≠ 0)`
  (germ form, G≠0 a.e. ⟺ G²≠0 a.e.). **FINAL COMPLETE SIG (fm-2 pinned, relayed to fm):** instances
  `[PseudoMetricSpace Y][MeasureSpace Y][ProperSpace Y][IsFiniteMeasureOnCompacts (volume)][OpensMeasurableSpace Y]`
  (the down-set needs them; NOT SigmaFinite as first guessed) — STRENGTHENING IS REQUIRED (the proof needs them ⟹
  a weaker Skeleton sig breaks the `exact _aux` wire; the "keep [TopologicalSpace] general" alt does NOT work).
  RHS `(n:ENNReal)/2 + rlctAtOn (fun y => G y^2) y0`. fm restates (batch w/ resolution_charts re-scope + (1,1,1)
  gate). USE-SITE: core's Y = Fin d→ℝ provides all 4 instances (bridge if Params-typed). R1's monomial ∏|y_j|^{2k_j}
  discharges hGne (≠0 off null coordinate hyperplanes). fm-2's proof _aux lands at iteration-close (one dependent-Fin
  snag: finPeel.continuous_invFun, no math depth) → fm wires `exact`.
- **R1 USE-SITE CONFIRMED (pp + Codex identical): CLEAN to relocate (confirms A) + 2 obligations folded into R1:**
  (1) **unit-absorption** — R1 chart core = unit·∏|y_j|^{2k_j}, so R1.2's S2 invocation MUST first absorb the
  nonvanishing unit via `rlct_unit_invariant` (S1.3), THEN S2 on the pure monomial (THE main hidden gap; Jacobian
  same); (2) **hcore_top endpoint** — free from the down-set property for strict c'>λ, +monomial-endpoint fact if
  literal ∫=∞ at λ (fm-2 pins which). min-over-charts CLEAN (n=r(H¹+H^{L+1})−r² upstream-fixed ⟹ factorises).

## GENERAL-M TRACTABILITY VERDICT (pp + decorrelated Codex) — THE WALL IS G3 ALONE
The definitive headline-reach picture. **A-vs-B (does the block-monomialization layer compound the wall?): NO.**
Codex flagged residual entanglement as FACT; pp LOCATED WHERE IT LANDS — at the T1 unit-termini (harmless:
monomial×unit either way), NOT the split-relevant T2 smooth-block termini (there the exceptional is pulled out
front ⟹ disjoint ⟹ product-MIN split holds). So: A's block blow-up compounds ONLY G5 (more leaves), no new G3;
B/hybrid (default B, cone-blowup only where entanglement occurs) is lighter for general M (reuses smoothBlockND +
the (2,1,2) product-MIN). **VERDICT: fixed-M (2,2,2) keeps Option A (uniform, execution-ready); general-M uses
B/hybrid; the block layer does NOT compound the wall.** CLIMB-OR-ROADMAP (assessed, not assumed): lower bound
SETTLED · G5-abstract BUILDABLE (down-payment, task #52) · block layer non-compounding ⟹ **G3 (explicit
flag-resolution / strict-transform for arbitrary M = quiver-determinantal geometry Mathlib lacks) is THE ONE
genuine research-wall — ISOLATED + NAMED.** ⟹ CLIMB fixed-M ladder + BUILD G5-abstract; ROADMAP G3. **Honest
general headline = ladder instances + G5-abstract + G3 (single named open obstruction)** — the best possible
roadmap shape (one well-scoped wall, not diffuse difficulty). OPERATOR SCOPE FLAG sharpened: general-M gated on
G3 ALONE. METHOD LESSON (pp, logged): when a decorrelated model flags a failure mode as FACT, the value is often
"locate WHERE it lands," not "abandon" — an obstruction confined to where it doesn't matter is a refinement, not
a refutation (dual of the Q4-trap: both = interrogate the SCOPE of the model's claim).

## G3 SPEC — the named wall, sharpened to its internal crux (pp, g3-spec-the-named-wall.md)
G3 = the EXPLICIT combinatorial flag-resolution of {∏C=0} (route-A-concrete, explicit poly charts — **NOT general
Hironaka**). Claim: for every M, a finite rose tree of explicit charts with (G3.1) coordinate-subspace stratum
centers, (G3.2) **strict-transform = smaller chain product [THE CRUX]**, (G3.3) leaves bottom out, (G3.4) cover
up to null, (G3.5) binding ratio (k=1, h=Mval−1) ⟹ rlctAt = ½·min_Adm Mval = lambdaCore.
**DONE vs OPEN:** G3.1 designed (R1.3 ℕ-count), G3.4 designed (cover + lower-bound settled), G3.5 done (R1.2a/b +
k=1 validated). **G3.2 (the in-chart residual re-identifies as a smaller matrix-chain product — the iterated
"Schur-complement-of-a-matrix-chain is a smaller chain product" fact) is THE genuinely-open crux.** CRITICAL:
**Aoyagi PROVES G3.2 on paper (pp.15-21) — so G3 is a FORMALIZATION gap, NOT open math.** The dedicated-tide build:
explicit pivot-chart φ+Jacobian → the Schur-complement lemma (G3.2, substantial) → recursion (terminates) →
cover+ratio wiring → glue with G5-abstract. Multi-rung tide.
**HONEST HEADLINE SHAPE — LOCKED:** PROVEN = the fixed-M ladder + the general machinery (S1/L1/L2/D1/A1/A2/
G5-abstract); ROADMAPPED = G3 (crux G3.2 = Aoyagi pp.15-21 to formalize). One well-scoped, paper-proven,
formalization-only wall — the cleanest possible roadmap (a known proof to formalize, not open research).
**OPERATOR SCOPE (sharpened):** the general-M headline is gated on the G3.2 Lean construction — a dedicated tide;
everything else proven/buildable. Choice: deliver now (ladder + machinery + G3 roadmap) vs commission the G3 tide.
**G3.2 AS A PRECISE LEMMA + ON-RAMP (pp, final sharpening):** G3.2 = "if the leading t₁×t₁ minor of the partial
product is a unit in a pivot chart, UNIMODULAR row/col changes give ∏(QCQ)=diag(E_{t₁}-regular, ∏C') with C' the
Schur-REDUCED chain (widths M^s−δ_s), and ‖∏C−B‖²=‖reg generators‖²+‖∏C'‖² ⟹ rlctAt=½·reg-dim+rlctAt(‖∏C'‖²),
recurse" = **Aoyagi Thm 3 + the chain-Schur recursion** (verified L=1; well-founded, ΣM^s strictly drops, base =
smooth block). **ON-RAMP: G3.2 REUSES `block_elimination` (L1, DONE) + `product_reduction` (L2)** — it's their
GENERAL-M chained form. So the G3 tide is "**generalize the already-built L1/L2 to an arbitrary-rank-vector
recursion + glue with G5-abstract**," NOT from-scratch resolution infra; the fixed-M product_reduction wiring is
the PROTOTYPE the tide generalizes. The roadmap is genuinely set up: one named wall, a precise lemma, a known
paper proof, AND a concrete on-ramp.

## D1 RE-SCOPED (fm proof-attempt-as-audit) — NOT a light standalone rung
D1 `deepest_point_reduction` is blocked on TWO real deps: (1) the **RLCT-monotonicity lemma** `|G|≤|F| a.e. near
w* ⇒ rlctAt G ≤ rlctAt F` — MISSING + measure-theoretic (the 0^neg a.e.-domination corner: |G|^{-c}≥|F|^{-c} a.e.
where G≠0, reverses at {G=0}); **assigned fm-2** (reusable by L2's per-point argument). fm has the pointwise core
`rpow_neg_antitone`. (2) D1 depends on **L2** (homogeneous-scaling Thm-2 argument needs core-homogeneity, not the
raw mixed-degree dlnLoss B ⟹ per-point core reduction ≈ L2-per-point). So critical-path order is
**S1✓ → [monotonicity lemma + L2(needs R1/Fubini)] → D1**, NOT S1→D1. Rung map corrected.
**fm BLOCKER cleared:** resolution_charts re-scope (#47) was decided but never LANDED in Skeleton — fm landing it
now (pp's core form, BLESSED) + the S1.5 wire (fm-2's verified package) in one batch → green-gate → (1,1,1) gate.

## STATE @ ~03:20 — R1.2 LIGHT confirmed (de-risk) + (1,1,1) gate spec'd; trunk @995a674
- **R1.2 IS LIGHT (pp confirmed, §8 literal):** post the L1/Lemma-2 unit-Jac changes, the residual/reg entries ARE
  coordinates (the changes DEFINE them so — F₂/F₃ are the L1 coord changes) ⟹ ‖reg‖² + residual block = Σ(coord)²
  = smoothBlockND + rlctAtOn_comp_homeomorph. NO IFT, no general reg-seq, no S1.1-diffeo. And the (2,2,2) Option-A
  cover is EVEN LIGHTER — all leaves monomial×unit ⟹ per-leaf = WEIGHTED monomial threshold, NO block-rlct. So
  the fixed-M ladder is cheap throughout; no R1.2 sub-mountain. fm-2's #54 block-rlct under Option A = quick.
- **(1,1,1) gate SPEC'D (pp → fm):** ι=Unit (1 chart), φ=id, |Jac|=1 (so BARE rlctAtOn is correct here — contrast
  the WEIGHTED (2,2,2)); d=2, k=(1,1), h=(0,0); monomialThreshold = 1/2 = lambdaCore(1,1,1) = ½·Mval, θ=2; box =
  Fubini-product = the done Case111Bridge. No cover, no G5 — fm SPECIFYs directly. The R1-batch's last item.
- fm: WIRE rlct_additive_smooth_block ((b) keep+exact, closes S1.5 sorry 6→5) + re-scope resolution_charts + the
  (1,1,1) gate → (2,1,2) [#55]. fm-2: product_min_rlct (#56) → (2,2,2)-measure (#54). pp: on-demand. rv-2: queued.
- **PROPERNESS GAP (fm SPECIFY-catch) → AVOIDED via g5_flat_cover (controller adjudicated):** a single explicit
  blow-up chart does NOT satisfy S1.1 `weightedThreshold_transport`'s GLOBAL `IsProperMap`+`Surjective`. Resolution:
  R1's per-chart transport = the **lintegral c-o-v inside g5_flat_cover** (per-chart `InjOn` off the null exceptional
  only — NO global proper/surj); global coverage = R1.6 (the cover). So `rlctAt(core)=⨅ monomialThreshold` =
  g5_flat_cover (∫=Σ∫) + per-chart weighted-monomial threshold (S2+unit-absorption) + sSup algebra. NOT
  G1/G2/G3-bespoke — g5_flat_cover is the GENERAL version of how (1,1,1) bypassed S1.1. (2,1,2) uses product_min_rlct
  (Tonelli, no transport) ⟹ gap moot there. **S1.1 ORPHAN FLAG:** S1.1 is NOT R1's chart-transport (earlier
  "S1.1 carries the blow-up CoV" was imprecise — g5_flat_cover does) ⟹ revisit whether S1.1 is used by D1/L2 or is
  now an orphan (proven, hsurj+hImE 10th-finding banked, possibly unplugged) — pp checking; name honestly; doesn't block.

## STATE @ ~03:00, trunk @c92501d — R1 DESIGN PHASE COMPLETE; execution remains
- **rlctAt_mono ON TRUNK** (D1/L2 engine; green-gated 2855 jobs, controller-verified axiom-clean). fm built it with
  the **zero-set-inclusion hyp (G=0→F=0)** — BETTER than the hGne alt (pointwise, no a.e. machinery; use-site:
  D1's scaled core has F's zero set). 15th finding (bare monotonicity false, G≡0/F=|x|⁴) caught at SPECIFY by both
  fm+fm-2; fm's fix adopted. (Also merged: R1.2a/b + the #19 engines, banked on trunk.)
- **FIXED-M LADDER DESIGN COMPLETE + CERTIFIED (pp R1 design role DISCHARGED):** (1,1,1) [done] · (2,1,2) [#55,
  product-MIN, min≠sum CERTIFIED via the c=3/2 ∫r^{-2}=∞ divergence test] · (2,2,2) [#54, 24-leaf cover, cover-
  complete 12063/12063, a G5-instance]. Roadmap mapped: lower-bound settled · G5-abstract build-ready (#52) ·
  A-vs-B verdict (wall is G3 alone) · G3 spec (crux G3.2 = Aoyagi pp.15-21 formalization gap). **Residual = pure
  formalization labour** (fm + fm-2 execute) + the G3 tide if commissioned.
- **EXECUTION UNITS:** fm → the R1 BATCH (S1.5 wire + resolution_charts core re-scope + (1,1,1) gate) FIRST [still
  not landed — fm redirected to it 3×; recurring fm→adjacent-work drift], then #55 (2,1,2) + #54-assembly; fm-2 →
  #52 G5-step + #54-measure; pp → on-demand (G5 questions / assembly / G3 tide). rv-2 → S1.5 PASS done; queued.
- **G5-ABSTRACT FLAT-COVER DONE (#52, fm-2 @48b9468, axiom-clean):** `perChart` (single-step c-o-v on V\N + null
  drop) + `g5_flat_cover` (∫⁻_U=Σ∫⁻ over a finite a.e.-disjoint chart-cover, lintegral_biUnion_finset₀). The (2,2,2)
  cover = this **composed 3×** (nested levels 4∘3∘4), NOT the abstract tree (deferred to G3). Over ℝ≥0∞ ⟹ no
  integrability hyps.
- **product_min_rlct HYP UNIFIED (pp):** positivity-guard (both ∫⁻>0) + disjoint + measurable, NOT "vanish only at
  0" (over-strong, excludes monomials) ⟹ ONE lemma covers block×block (2,1,2) + monomial×block (δ-leaf) +
  monomial². The (2,1,2) tool IS the δ-leaf tool. S1.5-PASS = the L2/additivity SUM-engine (NOT the δ-leaf PRODUCT).

## Next tick (state @ ~02:30, trunk @da24204)
**S1.5 FUBINI ENGINE COMPLETE @ad1f313** (controller-verified axiom-clean) — whole S1 substrate proven. R1 lower-bound
soundness SETTLED (general result PROVEN on paper). **(2,2,2) cover EXECUTION-READY** (pp, 24 leaves, cover-complete
12063/12063, a G5-instance). **G5-abstract BUILDABLE + assigned fm-2** (Mathlib lintegral c-o-v; reduces general wall
to G3 alone). Headline-reach DECIDED+flagged: fixed-M ladder now + G3 named obstruction.
LIVE: (1) **fm** — Skeleton batch (S1.5 `exact` wire + resolution_charts core re-scope + product_reduction wiring) +
the (1,1,1) gate → report green-gate. (2) **fm-2** — G5-abstract (cover-gluing lemma) + (2,2,2) per-chart measure
pieces. (3) **pp** — (2,1,2) Fubini-product design (completes the ladder design). (4) **rv-2** — audit the S1.5 engine
(#50) + queued wires. Then: fm formalises the (2,2,2) cover (pp leaf-list + fm-2 G5-abstract) → L2 (=block_elim+
S1Fubini+R1-core+A1) → D1 → T (fixed-M headline). #19 PARKED. G3 = the one named general-M research obstruction.
Watch the fm→#19 pull (parked 3×). Don't stop in a blocked state.

### (prior next-tick) state @ ~02:00
TWO BIGGEST RISKS RETIRED: Fubini n=1 equality PROVEN (@e1cf73c) + R1 route VALIDATED (A-concrete, B refuted).
Remaining = execution + assembly. **Re-scope PINNED** (pp → fm): `resolution_charts(M) = rlctAtOn(dlnLoss M 0)(0)
= ⨅ monomialThreshold` (reduced widths M = core) + product_reduction wiring chain (block_elim → S1Fubini n/2 →
resolution_charts-core + S2 + A1 → aoyagiLambda). **λ_core=0 edge HANDLED** (fm-2, core_admissible_zero, no
λ_core>0 hyp). Iteration keystone `rlctAtOn_comp_homeomorph` banked (@f254397).
INTEGRATE as they land: (1) fm-2's Fubini ITERATION (Fin-peel homeomorph + Σ-peel) → general-n
rlct_additive_smooth_block → report final sig → fm restate+wire (ONE pass) → I aggregator-wire S1Fubini +
green-gate → rv-2 audit. (2) R1 CLIMB (validate-small-first): fm closes the **(1,1,1) gate** (φ=id chart + S2 +
arith, NO general geometry, xcheck `case111_rlct`) → (2,1,2)/(2,2,2) explicit-poly charts; pp designs the GENERAL
atlas R1.1/R1.3(codim=Mval, heavy)/R1.6(cover) in PARALLEL (math validate-small'd via witnesses). fm also restates
resolution_charts (core) + wires product_reduction. (3) L2 → D1 → T. #19 PARKED. Critical path: Fubini-iteration
+ R1-(1,1,1)-gate → general R1 atlas → wire product_reduction → D1 → T. rv-2 decorrelated (R1 = heaviest audits).
Watch the fm→#19 pull (parked 3×). Don't stop in a blocked state.
