# G1 RouteMTree — FINAL build spec (fm3, all interfaces locked, ready to grind)

Every design + interface question is CLOSED. This is the complete spec for the dispatcher grind.

## (2,2,2) MILESTONE BANKED + ARCHITECTURE GAP (g192, fresh formaliser + Codex g206 + pp2 g207)
A fresh focused lean-formaliser (off fm3/routem) took the #39 grind. RESULT:
- ✓ (2,2,2) IsRouteMCover FACTS banked + reviewed PASS (#87/#89): RouteMCoverLemmas.lean (abstract cover
  reductions: coverLe_scaling, routeM_coverLe_of_finiteness, routeM_coverGeDiv_of_boxDiverges — the
  FINITENESS-ONLY cover shape, Codex-confirmed) + Case222RouteMCover.lean (routeM222_Fmeas/Uopen/Umem/cover_le/
  cover_ge_div, field-for-field vs IsRouteMCover, over F=myF222 U=openBox ι=Fin 1, ⨅=3/2=lambdaCore;
  sorry-free, clean-three[+monomial_rlct]). The anchor case's cover is DONE. (e222-reindex to dlnLoss H222 0
  fenced for crux2's packaging.)
- ⚠ ARCHITECTURE GAP surfaced (correctly handed back, NOT built blind) — the GENERAL routeStep recursion is
  unsound as a RESOLUTION (two coupled parts, Codex g206 item 2 + pp2 g207, verified vs RouteMRecursion):
  (1) ROOT-ANCHORING: foldFamily_threshold_ge_of_pivotWitness needs ALL per-leaf codims PivotWitness against
      the SAME (root) M; routeAtlas recurses into (split c).red ⟹ deeper witnesses anchor at the REDUCED
      chain, minAdm(reduced)<minAdm(root) ⟹ value UNDERSHOOTS ½·m₀. Fix: root-anchor (codim = Mval(root M, T),
      T root-admissible — the geometric codim is intrinsic to the ambient, invariant under the det-1 reindex).
  (2) DEEPER (the real one): split.red is an ABSTRACT ChainDimSplit field — NOTHING ties it to what the pivot
      blow-up ACTUALLY produces. routeAtlas's child exponents describe dlnLoss (split.red) 0, but the actual
      pullback residual is whatever the pivot geometry gives. PivotWitness certifies codim/value, NOT the
      analytic descent. So the recursion is a SYNTACTIC tree, not a certified resolution — the SAME vacuity-trap
      principle as g161, now at the recursion level (I scoped the certified-RouteStep at g161/g162, deferred;
      now REQUIRED).
PROPOSED RULING (awaiting pp2 cert-author confirm, sent): certified recursion — (a) define schurState M pivot :
ChainDimSplit M concretely (pp2's g183/g194 C1: pivotBlowupOn + the residual), prove routeStep's split =
schurState so split.red IS the genuine reduced chain; (b) per-cell datum proves residual = dlnLoss
(schurState.red) 0 (lintegral-transported, g186) + root-anchored PivotWitness. HOLD #85 (general routeStep) +
#86 (general extraction) + #88 (value over routeMIota) until the ruling. Formaliser meanwhile on the
anchoring-INDEPENDENT general Fmeas (Continuous/Measurable (dlnLoss M 0)) + routeMBaseNbhd box (decision-free).
NOTE: this is a GENUINE find (the general recursion's soundness), NOT a regression — the (2,2,2) anchor stands
(it uses the concrete Case222 charts, sidestepping the abstract recursion). The certified-descent is the last
real design piece; once pp2 confirms the schurState-def + descent-cert shape, the general grind resumes.

## Target: ONE unified RouteMAtlas (crux2 @31063ec, headline GREEN given it)
structure RouteMAtlas M F U ι d k h := { isCover : IsRouteMCover F U ι d k h, isValue : IsResolutionAtlas M ι d k h }
routeM_rlctAtOn_eq_lambdaCore (atlas) : rlctAtOn F 0 = ofReal (lambdaCore M)  -- GREEN, one Eq.trans.
My G1 produces ONE (ι,d,k,h); discharge isCover + isValue over the SAME family. Bridge is
MECHANISM-INDEPENDENT — ingests the FINAL accumulated per-leaf (d,k,h), however built.

## CONSUME-SHAPE AUTHORITATIVE (g180, crux2 from LANDED RouteMAtlas/RouteMBridge @fm2/route-m-atlas)
crux2 gave the ground-truth consume-shape (NOT recall — #38 DONE, lives on route-m-atlas, NOT yet on my
fm3/routem; the production decl is crux2's on route-m-atlas, importing my geometry). PIN:
- BUNDLE: RouteMAtlas M F U ι [Fintype] d k h := ⟨isCover : IsRouteMCover, isValue : IsResolutionAtlas⟩.
  I hand crux2: DATA (ι [Fintype], d, k, h) + F + U + the two Prop groups. `stratum` does NOT appear in the
  consumed shape (it's MY producer scaffold; decorrelated away — my branch's stale ResolutionAtlas.lean
  stratum/threshold_eq form is SUPERSEDED by the landed threshold_ge/achiever form).
- isCover = IsRouteMCover, ABSTRACT (Q2 = (b) CONFIRMED): NO `dlnLoss∘chart = monomial·unit` eqn. Takes
  TWO INTEGRAL Props over the leaf family + Fmeas/Uopen/Umem:
    cover_le : ∀ c', ∫⁻_U |F|^(−c') ≤ ∑_i ∫⁻_{unitBox(d i)} monomialIntegrand (d i)(k i)(h i) c'
    cover_ge_div : ∀ c', (∃ i, monomialThreshold (d i)(k i)(h i) ≤ c') → ∀ open Ω∋0, ¬IntegrableOn (|F|^(−c')) Ω
  The per-node→per-leaf COMPOSITION is ENTIRELY MINE: compose my G2 per-node light pullbacks
  (node_loss_pivot_factor + node_jacobian_det) + ReducedTransport.descent down the tree to PROVE
  cover_le/cover_ge_div for the leaves. The bridge consumes only the two resulting inequalities (my
  argmaxCellOn/g5_pivotNode ae-cover must LAND as these two Props, NOT appear as a field).
- isValue = IsResolutionAtlas (the LANDED threshold_ge/achiever form, keyed to m₀ = ((Adm M).inf' Mval).toNat):
  built by of_mult_and_achiever from (i) the A+K mult-bound ∀i∀j, m₀·(k i j) ≤ (h i j)+1 + (ii) one binding
  leaf (k i₀ j₀, h i₀ j₀)=(1, m₀−1). My PivotWitness (codim=Mval) + regular-seq k=1 + foldFamily_achiever feed
  these. (My foldFamily_threshold_ge_of_pivotWitness gives threshold_ge directly; of_mult_and_achiever is
  crux2's path to the same — either works; the landed bridge wants the mult-bound + binding-leaf inputs.)
PRODUCTION FLOW (crux2's decl on route-m-atlas, importing my geometry): ⟨⟨Fmeas,Uopen,Umem,cover_le,cover_ge_div⟩,
of_mult_and_achiever M … (mult-bound)(binding-leaf)⟩ → routeM_rlctAtOn_eq_lambdaCore → resolution_charts.
MY DELIVERABLES (on fm3/routem, standalone, NO route-m-atlas import): the (ι,d,k,h) producer (routeAtlas,
routeStep) + cover_le + cover_ge_div (the composed integral Props) + the mult-bound + binding-leaf facts.
Shape STABLE (landed sorry-free). The cover_le/cover_ge_div composition = the analytic grind (my G2 pullbacks
+ ReducedTransport.descent + the argmaxCellOn cover-split, normalized via the banked Case222 adapters).

## ⚠ ReducedTransport is the WRONG per-node mechanism for R1 (g186, crux2 flag + Case222 verified)
crux2 flagged: rlctAtOn_reduced_transport (via comp_homeomorph) is SUPERSEDED FOR THE LOSS (the transvection
is det-1/MP but the loss is NOT invariant — L unipotent ⇏ orthogonal; the clean factor-through-a-c-o-v is
unreachable; pp2 #129/#130, the GeneralR1Recursion SUPERSEDED note). I verified against Case222Resolution
(the authoritative (2,2,2) anchor) — and crux2 is RIGHT, my g179 ReducedTransport is the wrong layer:
- Case222Resolution architecture note (lines 12-14): "everything at the lintegral level (the blow-up nodes
  are NOT homeomorphisms — only lemma2Hom is, entering as a single-chart change-of-variables INSIDE an
  integral, NEVER an rlctAtOn transport)." Case222Resolution uses rlctAtOn_reduced_transport / squeeze
  ZERO times. The blow-up nodes are NOT injective at the exceptional divisor ⟹ NOT homeomorphisms ⟹
  rlctAtOn_reduced_transport (which needs redEmbed a HOMEOMORPHISM) does NOT apply per-node.
- So the per-node descent is LINTEGRAL-LEVEL inside cover_le (compose node_loss_pivot_factor pullbacks +
  the lemma2Hom MP change-of-variables AT THE INTEGRAL LEVEL → land the leaf monomialIntegrand). There is
  NO per-node rlctAtOn transport. The SINGLE rlctAtOn = ⨅ comes from crux2's bridge (routeM_rlctAtOn_eq_iInf)
  at the TOP, from cover_le/cover_ge_div — NOT a per-node rlctAtOn equality.
CONSEQUENCE: my ReducedTransport (g179, a per-node rlctAtOn transport bundling rlctAtOn_reduced_transport) is
TRUE as a lemma but the WRONG TOOL for R1's per-node descent — the per-node map isn't a homeomorphism, so
there's no per-node rlctAtOn transport to bundle. ReducedTransport is NOT a RouteStep.branch field for R1;
the descent lives inside cover_le (lintegral). DROP ReducedTransport from the R1 per-cell datum (keep it as
a TRUE-but-unused lemma, or delete). The per-cell datum = (split, codim, PivotWitness) + the LIGHT pullback
(node_loss_pivot_factor, used INSIDE cover_le's lintegral CoV), NO ReducedTransport field.
This is the SAME lesson as g173 (don't relay a transport framing without verifying against the code) — I
caught it via Case222's lintegral-not-rlctAtOn architecture. SURFACING to crux2 to confirm: R1 descent is
lintegral-only (cover_le), ReducedTransport/per-node-rlctAtOn NOT used. (My g178/g179 over-bundled it.)

## BRIDGE-WIRING + Nonempty CATCH (g181, crux2 from landed routeM_rlctAtOn_eq_iInf sig) — HANDLED
crux2 confirmed (ground truth): routeM_rlctAtOn_eq_iInf takes (ι,d,k,h) as EXPLICIT args — call directly with
(routeMIota S, routeD S, routeK S, routeH S) + the IsRouteMCover instance; NO adapter, my noncomputable defs
are valid args. ONE CATCH: needs `[Nonempty ι]` (achiever-side iInf_le). HANDLED (g181, route-checked green):
threaded Nonempty through the recursion — NodeChartFamily gains `nonempty : Nonempty ι`; RouteStep.branch gains
`(cellsNe : Nonempty cells)` (a branch always has ≥1 pivot cell = the no-stall/dispatcher guarantee); routeAtlas
derives nonempty per constructor (leaf → PUnit; branch → ⟨⟨c, i⟩⟩ from cellsNe × child.nonempty);
`instance : Nonempty (routeMIota M)` carries it. So routeM_rlctAtOn_eq_iInf's [Nonempty ι] resolves.
SCHUR NAMES (crux2 corrected my mp_schur_transvection_vec — doesn't exist): per-node workhorses (ALL on
fm3/routem, byte-identical) = schur_straighten_of_data + rlctAtOn_reduced_transport (the ReducedTransport
field) for descent; schur_node_squeeze_unif (c₁=(2(1+T²))⁻¹, c₂=2+2T²) explicit-constant bound; measure_drops
= ChainDimSplit FIELD (S.measure_drops). schur_straighten_squeeze_exists = HEAVY/L2 (NOT R1, g188/g175).

## COVER-FACT SIGNATURES SIGNED OFF (g182, crux2 field-for-field vs IsRouteMCover @31063ec) — no adapters
crux2 read the actual IsRouteMCover structure + verified my cover-fact signatures MATCH field-for-field:
(a) BOX: Skeleton.unitBox = Set.univ.pi (fun _ => Set.Icc 0 1) = [0,1]^d (Skeleton:84). My routeM_cover_le
    RHS uses the SAME Skeleton.unitBox → NO adapter (the staged unitBox-adapter was a contingency for a
    different box; I use the canonical one). ✓
(b) cover_ge_div WEIGHT: `* (fun _ => (1:ℝ))` verbatim — `¬ IntegrableOn (fun x => |F x|^(-c') * (fun _ => 1) x) Ω`.
    Copied exactly. LHS (cover_le): `∫⁻ x in U, ENNReal.ofReal (|F x|^(-c'))` — NO `*1` on LHS (only the
    RHS-integrand + cover_ge_div carry it). Mine = same. ✓
PACKAGING (crux2, the 5-field structure): IsRouteMCover = ⟨Fmeas, Uopen, Umem, cover_le, cover_ge_div⟩, so
routeMCover S := ⟨routeM_Fmeas S, routeM_Uopen S, routeM_Umem S, routeM_cover_le S, routeM_cover_ge_div S⟩.
crux2 packages it on route-m-atlas (trivial ⟨⟩) → routeM_rlctAtOn_eq_iInf gives rlctAtOn(core)=⨅; then my
isValue + crux2's RouteMAtlas bundle → headline. crux2 packages EVEN sorry-stubbed (the skeleton), so I
surface the (2,2,2) IsRouteMCover instance when green. EVERY signature now verified vs ground-truth — no
adapters, no shape gaps. The grind (routeStep + cover_le/cover_ge_div + Fmeas/Uopen/Umem + mult-bound/binding-leaf)
is pure formalisation against the signed-off interface. === COORDINATION ARC EXHAUSTIVELY CLOSED (g155→g182). ===

## cover_le LANDED with ∃-C shape (g189, crux2 @91159e1) — the FINAL stub target
crux2 WEAKENED + PUSHED cover_le (origin/fm2/route-m-atlas @91159e1; #81 done). The C is EXISTENTIALLY
quantified INSIDE cover_le (NOT a data field — IsRouteMCover is Prop-valued, a data field
`coverConst : NNReal → ℝ≥0∞` FAILS Prop-projection). LANDED field (verified):
  cover_le : ∀ c' : NNReal, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∫⁻ x in U, ENNReal.ofReal (|F x| ^ (-(c':ℝ)))
        ≤ C * ∑ i : ι, ∫⁻ y in unitBox (d i), ENNReal.ofReal (monomialIntegrand (d i)(k i)(h i)(c':ℝ) y)
So MY routeM_cover_le RETURNS the ∃ C (NO C-function threading — a per-c' finite witness):
  routeM_cover_le (S)(c') : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∫⁻_U |routeMCore S|^(-(c':ℝ)) ≤ C * ∑ i, ∫_{unitBox (routeD S i)}
    monomialIntegrand (routeD S i)(routeK S i)(routeH S i)(c':ℝ)
Provide ⟨(a^{−c'}·2^d as the finite C), (C < ⊤), (the ≤ bound)⟩ — my banked integrableOn_monomial_mul_unit_iff
(a^{−c'}) + integrableOn_Icc_symm_of_even (2^d) produce that bound with that C. This SUPERSEDES the
C : RouteState→NNReal→ℝ≥0∞ data-threading idea (g188) — the ∃-inside-Prop is cleaner (no C-function field).
UNCHANGED: cover_ge_div + Fmeas/Uopen/Umem (no constant); box stays unitBox [0,1]^d; wrap still 5 fields (C
lives INSIDE cover_le). crux2 verified full lib green (3702) + headline clean-three (C never enters the ⨅).
DEPENDENCY for the grind: routeM_cover_le's BODY + routeMCore/routeMBaseNbhd (extraction) need routeStep
CONCRETE (they extract the flat core/nbhd from the node). So order: routeStep (pp2 recipe) → routeAtlas
concrete → routeMAmbient/Core/BaseNbhd → cover-facts (the ∃-C statement is TRUE, stub-safe per g188). The
∃-C statement is stub-safe (true) the moment routeMCore is concrete; until then routeMCore itself is the gate.

## STUB DISCIPLINE — routeM_cover_le MUST stub WITH C(c'), never bare (g188, crux2 STOP)
crux2 STOP (right — lean-discipline enforced): do NOT stub routeM_cover_le with the BARE RHS (≤ Σ∫). It's
UNPROVABLE (a^{−c'}·2^d irreducible) — a bare stub = a sorry under a FALSE statement, which would WALL when I
prove it (build the whole dispatcher against a false target, then fail). C(c') is MANDATORY in the STUB
itself, not a fallback. So routeM_cover_le's STATEMENT (sorry-bodied or proven) is:
  routeM_cover_le (S) (c') : ∫⁻_U |routeMCore S|^(-(c':ℝ)) ≤ C S c' · ∑ i, ∫_{unitBox} monomialIntegrand
    (routeD S i)(routeK S i)(routeH S i)(c':ℝ)
C-THREADING (sync w/ crux2, #81): my side `C : RouteState → NNReal → ℝ≥0∞` (so `C S c'` for the fixed S),
finite (carries a^{−c'}·2^d). On crux2's IsRouteMCover.cover_le FIELD: `C : NNReal → ℝ≥0∞` (family fixed) —
matches mine as `C S` for the fixed S. crux2 adds C to the field (the field type = my lemma type, both with
C); wrap stays ⟨Fmeas, Uopen, Umem, cover_le, cover_ge_div⟩. crux2's structure change = #81, gated controller-go
(route-m-atlas #38). I HOLD the bare stub; stub WITH C once crux2 confirms the exact C-type so they line up.
cover_ge_div + Fmeas/Uopen/Umem UNCHANGED (no constant). === lean-discipline: statement TRUE before stub. ===

## cover_le SEAM — CONSTANT-CARRYING RHS (g185, fm3 flag + crux2 verdict, verified vs bridge proof)
I flagged: `∫⁻_U |F|^(−c') ≤ Σ_ι ∫_{[0,1]^d} bare-monomialIntegrand` is LITERALLY FALSE — the per-chart unit
lower bound a (≥a>0, g183) gives |F|^(−c') ≤ a^{−c'}·(monomial)^{−c'}, and the signed-box→[0,1]^d orthant
fold gives 2^d; both INFLATE. So bare cover_le (no constant) is unprovable (the (c) "fold into the box"
route is impossible — the a^{−c'}·2^d inflation is IRREDUCIBLE).
crux2's VERDICT (verified vs the routeM_rlctAtOn_eq_iInf proof body, RouteMBridge): the fix is (a) — WEAKEN
cover_le to carry a finite constant C(c'):
  cover_le : ∀ c', ∫⁻_U |F|^(−c') ≤ C(c') · ∑_ι ∫_{unitBox(d i)} monomialIntegrand (d i)(k i)(h i) c'
  where C : NNReal → ℝ≥0∞ finite (C(c') = a^{−c'}·2^d < ⊤ for c' finite, a>0).
SOUND (I verified the bridge proof, RouteMBridge:routeM_rlctAtOn_eq_iInf):
- ≥-leg: `refine lt_of_le_of_lt (hcover.cover_le c') ?_` uses cover_le ONLY for finiteness (∫_U < ⊤ from
  Σ∫ < ⊤). With the constant: lt_of_le_of_lt (cover_le c') (ENNReal.mul_lt_top hC_fin hΣ_fin) — C·finite =
  finite. ✓ (verified: the ≥-leg is rlctAtOn_ge_of_integral_lt + the Σ_lt_top split, exponent-finiteness only.)
- t = ⨅ monomialThreshold is `set` from the EXPONENTS (d,k,h) ONLY (the ≤-leg via cover_ge_div + exists_lt_of_
  ciInf_lt); C(c') NEVER enters the ⨅. Headline ⨅ UNCHANGED. (Load-bearing: the constant moves finiteness, NOT
  the threshold.)
- ≤-leg uses only cover_ge_div — untouched (constants don't affect ¬IntegrableOn).
crux2 makes the STRUCTURE change on route-m-atlas (cover_le RHS gains C(c'); the ≥-leg gains the mul_lt_top).
MY cover_le deliverable RHS now = C(c')·Σ∫; I fold BOTH a^{−c'} (unit, g183) AND 2^d (orthant) into C(c') via
the banked integrableOn_monomial_mul_unit_iff + integrableOn_Icc_symm_of_even; box STAYS unitBox [0,1]^d.
CONFIRMED the shape to crux2. (Flagged controller: RouteMBridge change on route-m-atlas w/ #38.) GOOD FIND —
the bare cover_le would have walled the cover_le proof; the constant-carrying form is sound + headline-neutral.
CONVERGENCE (g187, crux2 retracted its stale "adapter staged" comment): crux2 confirms NO constant-free
adapter — option (b) "adapter normalizes signed-box/monomial·unit → bare-monomial/[0,1]^d" = the SAME
impossibility as (c) (∫_U ≤ Σ∫ bare-monomial literally false; no adapter erases a^{−c'}·2^d > 1). Lands on
(a), matching g185. THE DIVISION (crux2 + fm3): I keep charts on the NATURAL SIGNED BOX (chartDomOn — NO
orthant grind on my side) AND fold BOTH a^{−c'} (integrableOn_monomial_mul_unit_iff) + 2^d
(integrableOn_Icc_symm_of_even) into C(c'); I produce `∫_U ≤ C(c')·Σ∫_{[0,1]^d} monomial` (the constant IS
the output, not erased); crux2 weakens the structure to accept C + consumes C·Σ∫. CONFIRMED to crux2.
Σdrop (crux2 re-answered, prior crossed): hdrops needs only Σdrop>0 (agnostic =2 vs ≥1, both terminate); but
schurState.red MUST equal what nodeC1's pullback ACTUALLY clears — wire Σdrop=2 (red = M'_0−1, M'_1−1) ONLY
if nodeC1 genuinely clears row+col; row-only → Σdrop=1. CHECK schur_node_loss_presentation's residual when
building schurState (the row-split ‖row0‖²+‖lower‖² is row-only ⟹ likely Σdrop=1 unless the full peel runs).

## CONSUME-SHAPE MINIMAL — already right, NOT over-enriched (g184, crux2 HOLD + verified)
crux2 HOLD before enriching NodeChartFamily: read the bridge proof body of routeM_rlctAtOn_eq_iInf — it
references ONLY the 5 fields (cover_le/cover_ge_div/Fmeas/Uopen/Umem) + Skeleton atoms; NEVER a chart φ_i /
pullback eqn / Jacobian. The CoV (|x_p|^{−2c'}·|res|^{−c'}·|x_p|^{card−1} = monomialIntegrand) happens ENTIRELY
INSIDE my cover_le proof — it's HOW I establish the integral inequality; the bridge runs on the inequality
alone. So NodeChartFamily (the bridge-consumed output) needs ONLY (ι,d,k,h) + the 2 Props + Fmeas/Uopen/Umem.
VERIFIED I'm already minimal: my NodeChartFamily = {ι, fintype, nonempty, data : ι → MonoData} = exactly
(ι,d,k,h)+instances, ZERO chart/pullback/jac fields. The PivotWitness + ReducedTransport live on
RouteStep.branch (my DISPATCHER input / proof machinery), NOT on NodeChartFamily — so the consumed record is
minimal by construction; I did NOT over-enrich. (crux2's caveat: enriching NodeChartFamily IS legit if MY
cover_le proof needs the composite chart accumulated — a producer-side convenience for MY proof, my call,
NOT a consume-requirement. If I add a composite-chart field later it's for my cover_le, not the bridge.)
NOT blocked on a richer consume-shape — there isn't one. consume-contract = 5 fields over (routeMIota,
routeD, routeK, routeH), unchanged. (#26 authoritative on MY producer packaging; for crux2 still the 5-field ⟨⟩.)

## TWO COVER-PROOF REFINEMENTS — INTERNAL, zero interface impact (g183, crux2 confirm)
crux2 confirms both are INSIDE my cover-fact proofs, NOT interface hyps (IsRouteMCover's cover_le/cover_ge_div
are integral inequalities, agnostic to HOW proven):
(1) routeMBaseNbhd S must be BOUNDED (a bounded open box ∋ 0, NOT univ): the ≥-direction
    (rlctAtOn_ge_of_integral_lt, downstream of cover_le) needs the bounded witness; univ breaks THAT. My
    choice in defining U + proving the Props; crux2's package just takes the U I give.
(2) the per-chart unit lower bound is `≥ a > 0` (NOT `≥ 1`): the bedrock-correct general fact (a step INSIDE
    my cover_le proof — node_loss_pivot_factor's unit `core∘hardPivotAt` is bounded-below-by-a-positive, not
    necessarily 1). `≥ 1` where free is fine; `≥ a>0` is the honest general form. The bridge never sees it —
    only the resulting integral inequality.
NEITHER changes crux2's packaging. (Hold #26 for the authoritative packaging if it pins different; crux2
consumes #26's then.) === ALL INTERFACE + INTERNAL-PROOF CHOICES NOW SETTLED; the grind is fully scoped. ===

## Encoding (controller-accepted): WF.fix / NodeChartFamily, Fintype-as-field
RouteState(L,M); routeMeasure = lex(L,ΣM,ncDefect); routeRel_wf. routeAtlas = WellFounded.fix.
NodeChartFamily per-leaf record (crux2 leaf-level): {composite chart φ_i, pullback L∘φ_i=monomial·unit
(pointwise on chartDomOn, unit≥a>0), Jacobian, (d,k,h)}. routeMIota/Fintype/routeD/routeK/routeH banked-shape.
FOUNDATION BANKED: RouteMState.lean @origin/fm3/routem 7c6401a (green, leaf=unit).

## C1 node (triply-converged: my (a)/(b) + pp2 g144 + controller lock): blow-up ⊕ Schur-descent ⊕ recurse
- BLOW-UP: pivotBlowupOn active p → core∘φ = x_p²·(core∘hardPivotAt) (G2 node_loss_pivot_factor),
  Jac (x_p)^(card−1) (node_jacobian_det). x_p² = k=1 weight, ΣM UNCHANGED.
- SCHUR-DESCENT (the ΣM-drop, route-independent): the triangular D↔S+ba peel (det-1, S⁻¹-free) clears
  pivot row+col, Â→blockdiag[1,S], residual ‖S·A2red‖²=dlnLoss M' 0. schurState = M' (M'_0=M_0−1,
  M'_1=M_1−1, M'_s=M_s s≥2). measure_drops = crux2's ChainDimSplit.measure_drops, Σdrop=2 (drop_0=drop_1=1).
  Loss-pullback FACT = Framing A row-split (my schur_node_loss_presentation, ‖Â·A2‖²=‖row0‖²+‖lower‖²).
  {S=0} bilinear center needs the triangular peel (pivotBlowupOn hits coord subspaces only); {Γ=0} direct.
- PRECONDITION M_0,M_1≥2 (else width-1 pinch → C4).
- RECURSE on schurState. lex↓ via Σdrop=2.
Build C1 against g138/g140-BOTH-STEPS (efff7ca/2f80d44), NOT g138-c2c5-fix 5bcac11 (pre-#36, wrong).

## C2/C4/C5 (g140 taxonomy)
- C2 full-rank pass-through: passState (L drops); downstream-descent.
- C4 separating/width-1 pinch: Fubini split, two children (leftState/rightState, L drops). The C4-terminal
  proviso (empty-Schur/width-1 → C4, not C1) is the no-stall guard, baked in classify.
- C5 mixed partial-drop: C1+C2 composite.
- C3 NC-completion: per-leaf (d,k,h) post-pass (k≥2), not a tree node.

## isCover (= IsRouteMCover, crux2's bridge consumer)
- Fmeas/Uopen/Umem (easy: dlnLoss polynomial-measurable; U = bounded open box ∋ 0).
- cover_le: ∫_U |F|^{−c'} ≤ Σ_ι ∫_{unitBox d_i} monomialIntegrand. PROOF = g5_pivotNode/recStep cover
  split (argmaxCellOn cover + aedisjoint) + per-chart CoV (node_loss_pivot_factor + node_jacobian_det
  composed down the path) landing monomial·unit on chartDomOn [−1,1]^d. NORMALIZATION (signed-box [−1,1]^d
  + monomial·unit → bare-monomial [0,1]^d): crux2's STAGED adapter monomialIntegrand_abs_invariant (2^d-
  orthant) + the unit-factor reduction (integrableOn_monomial_mul_unit_iff, banked). crux2 completes on flag.
- cover_ge_div: ε-uniform leaf divergence at/above threshold (generalize Case222 rlctAtOn_myF222_le route,
  cites monomial_rlct/S2 for ≤). monomialIntegrand_lintegral_box_eq_top is the banked atom.

## isValue (= IsResolutionAtlas, cover's S-min @1c4b9b5, via of_mult_and_achiever)
- threshold_ge (C≥): ∀ i, ½·m₀ ≤ monomialThreshold (d i)(k i)(h i). From k=1 mult-control
  (monomialThreshold_ge_of_mult', banked) + admissibility (every center codim = some Mval(T) ≥ minAdm).
- achiever (C=∃): ∃ i₀, monomialThreshold = ½·m₀. = pp2's g147/g148 binding branch (i₀ = the C1 path
  resolving each C_s to T*-rank, j₀ = binding divisor (1,m₀−1)). Transcribe pp2's cert; my routeMIota
  nested-Σ/Sum path is the i₀ shape (depth-2 for (2,2,2): C1@A-pivot → C1@incidence → leaf).

## Banked precedent for every piece
G2/Schur/LossHomog (mine, banked) · schur_lossDiff_mem_ideal + ChainDimSplit.measure_drops (crux2) ·
g5_pivotNode/argmaxCellOn_cover/_aedisjoint/pivotBlowupOn(Deriv_det) (atlas) · monomialThreshold_ge_of_mult'/
_le_regularSeq + monomial_rlct/S2 + monomialIntegrand_integrable_of_lt/_lintegral_box_eq_top (Skeleton/Case222) ·
integrableOn_monomial_mul_unit_iff + integrableOn_Icc_symm_of_even (Case222, the normalization) · pp2 achiever cert.

## NET
No open interface/design questions. The grind = classify (rank-pattern dispatcher) + the 4 reduction
state-maps + descent proofs + the enriched per-leaf accumulation → concrete routeAtlas; the extraction
(routeMAmbient=flatDim/routeMCore=flat dlnLoss/routeMBaseNbhd=bounded box, needs ParamsFlat import); the
isCover facts (Fmeas/Uopen/Umem easy; cover_le the hard one; cover_ge_div) + isValue (threshold_ge + achiever).
crux2 packages into RouteMAtlas on route-m-atlas + completes the normalization adapter. Commit+push each green decl.

## ACHIEVER CERT (pp2 g147, DELIVERED) — the routeM_achiever transcription target
Cert: origin/g147-achiever-cert @6e6b00d, g147-Smin-achiever-CERTIFICATE.md. The (i₀,j₀) witness for
of_mult_and_achiever (encoding-independent; pp2 re-spells i₀ in my routeMIota once it has the signature, sent):
- T* = (Adm M).inf' Mval minimiser; m₀ = Mval(T*).
- i₀ = the routeMIota path resolving each C_s to its T*-rank t_s (nodeC1/C5 pivot, or nodeC2 where t_s=t_{s-1}).
- j₀ = the codim-m₀ binding divisor: (k i₀ j₀, h i₀ j₀) = (1, m₀−1). ⟹ monomialThreshold = m₀/2 = ½·m₀.
- of_mult_and_achiever hk₀ (k i₀ j₀=1) + hh₀ (h i₀ j₀=m₀−1) → monomialThreshold_eq_half_of_binding → achiever.
- (2,2,2) concrete: T*=(1,0) rank-1 incidence codim-3, i₀ = ρ-chart path, j₀ = ρ-divisor, (k,h)=(1,2), 3/2.
- Realizability (why i₀ exists): T* via Core.OrbitKostant/Orbit.baseChange_normalForm (RealizableRank =
  range rankFn; Gabriel normal form hits T*), seam prefix:RealizableRank M→Adm M. Only the MINIMISER need
  be reached (weaker than full surjectivity); the nodeC1/C5 branch picks the T*-rank pivot per node.
- Verified (g147): (2,2,2)→(1,2); (3,3,3)→(1,6); (2,2,2,2)→(1,2); (4,3,2) T*=(2,0)→(1,5); (2,1,2)→(1,1).
ALL UPSTREAM CERTS NOW DELIVERED — the grind has no remaining external dependency.

## ACHIEVER i₀ RE-SPELLED IN MY ENCODING (pp2 g148, zero translation gap)
Cert: origin/g148-iota-respell @febc15a, g148-achiever-iota-respell.md. i₀ built by the SAME WellFounded.fix
recursion as routeAtlas, per-RouteCase:
  .c1 cs dec → i₀@S = ⟨c*, i₀'⟩ : Σ c:cs, (routeAtlas (schurState S c.1)).ι   (c* = the T*-rank PivotChoice cell)
  .c2 c dec  → i₀@S = i₀'                                                     (descend, same ι)
  .c5 cs p   → i₀@S = Sum.inl ⟨c*, i₀'⟩                                       (complement-via-C1, the minimiser's binding center)
  .c4 s      → i₀@S = Sum.inl i₀' | Sum.inr i₀'                               (the block with T*'s binding center)
  .leaf md   → i₀ = PUnit.unit                                               (md = binding divisor (1, m₀−1))
So i₀ = ⟨c*₁, ⟨c*₂, …, PUnit.unit⟩⟩. Wiring: ι := routeMIota ⟨L,M⟩, d/k/h := routeD/K/H; of_mult_and_achiever
(i₀, j₀): j₀ = the binding coord on i₀'s MonoData (routeK _ i₀ j₀=1, routeH _ i₀ j₀=m₀−1) →
monomialThreshold_eq_half_of_binding → achiever.
(2,2,2): i₀ = ⟨c*, PUnit.unit⟩ (c* = ρ-chart pivot, schurState → leaf md₁=(1,2)), threshold 3/2. ✓
DEPENDENCY: classify/PivotChoice stubbed → i₀'s SHAPE wireable now (the recursion selecting the T*-rank
cell), concrete c* lands with #39's rank-pattern un-stub. (2,2,2) anchor wireable immediately. Realizability
(cs nonempty at the T*-rank cell) rides Core.baseChange_normalForm, stub-independent.
pp2's λ-path arc g132→g148 COMPLETE. No remaining translation gap on any consumed cert.

## ACHIEVER FINAL (pp2 g148-222fix2 @34c1d6c) — fully pinned to my encoding, zero gaps
- i₀ = ⟨c*₁, ⟨c*₂, …, PUnit.unit⟩⟩, per-rank-unit nested Σ/⊕ following the T*-rank PivotChoice at each node
  ("resolve C_s to t_s" = (t_{s-1}−t_s) per-rank-unit C1 steps).
- (2,2,2): i₀ = ⟨c*₁(A-pivot rank2→1), ⟨c*₂(incidence), PUnit.unit⟩⟩, TWO C1 nodes. (2-node, authoritative.)
- j₀ = the axis with LARGEST card = m₀ (the C1 step whose pivotBlowupOn center is the full codim-m₀
  stratum); it binds the ⨅ at ½·m₀; other axes (smaller card) have larger ratio (don't lower the ⨅).
- ROUTE (NOT bare single-axis eq): monomialThreshold = ½·m₀ via le_antisymm —
  (≤) monomialThreshold_le_regularSeq at j₀ ((k,h)=(1,m₀−1)); (≥) threshold_ge (all axes, mult-bound).
  of_mult_and_achiever bundles both (hk₀/hh₀ at j₀ + the m₀·k≤h+1 mult-bound).
- Wires once classify/PivotChoice un-stub (the c* lands with the rank-pattern combinatorics; the
  card=m₀-at-binding-step is the (S-min) datum, stub-independent).

=== COORDINATION + DESIGN ARC COMPLETE ===
No open questions: interface (unified RouteMAtlas, crux2), value (cover S-min + of_mult_and_achiever),
achiever (pp2 g147→g148→222fix2, re-spelled in my encoding), cover_le normalization (crux2 adapter),
C1 mechanism (blow-up ⊕ Schur-descent ⊕ recurse, triply-converged), encoding (WF.fix, controller-accepted).
All upstream certs delivered. The grind (classify + reductions + per-leaf accumulation + isCover facts +
isValue) is dependency-free formalisation against this locked spec.

## C1 PEEL TRANSPORT (pp2 g152, pre-answered) — det=1 MP, rides measurePreserving_lemma2, NO new lemma
The per-node C1 triangular peel w := D − ba is MEASURE-PRESERVING, det EXACTLY 1 (a shear/transvection:
Jacobian lower-triangular with 1's on diagonal [[1,−b,−a],[0,1,0],[0,0,1]], det=1 identically, at ANY rank
— I verified the shear is det-1 for matrix S in /tmp/peel_rank_r.py; pp2 g152 confirms). So schurState's
peel rides measurePreserving_lemma2 / rlctAtOn_comp_homeomorph (det=1, no Jacobian weight) — the EASY MP
side, NO new bounded-unit-Jacobian lemma needed.
DISTINCTION (don't conflate): C1 per-node peel = det=1 MP (measurePreserving_lemma2). The g150
deepest-point GAUGE chart (crux2 #51) = det-UNIT non-MP (det(A)^{-(r+M2)}det(B)^{-M0}, bounded unit ≠1,
rides rlctAtOn_unit_invariant_aux + germ-locality) — DIFFERENT transport, because it's the whole-chain
gauge slice accumulating endpoint dets, not a single Schur shear. For nodeC1 I'm on the MP (easy) side.

=== ALL BUILD-RELEVANT DETAILS NOW CLOSED ===
Every interface (RouteMAtlas/IsRouteMCover verbatim), cert (achiever g148, value of_mult_and_achiever),
design (C1 = blow-up ⊕ det-1 triangular peel ⊕ recurse, rank-r = same op iterated), and transport
(C1 peel = det=1 MP / measurePreserving_lemma2; cover_le normalization = banked + crux2 adapter) is pinned.
Zero open questions, zero banked-lemma gaps. The grind is pure formalisation against this spec.

## C1 PEEL det=1 RANK-r CERTIFIED (pp2 g153 @0006f3a, decorrelated with my /tmp/peel_rank_r.py)
The general-rank-r peel W:=D−b·a is det=1 EXACTLY (block shear: ∂(W,a,b)/∂(D,a,b) block-lower-triangular,
identity on the D-block diagonal since ∂W/∂D=I, f(a,b) D-independent). Verified r=1,2,3 × several (m,k)
(pp2 g153) + my rank-r check — CONVERGED. So nodeC1's peel rides measurePreserving_lemma2 (det=1 MP) at
ANY rank, NO bounded-unit lemma, NO rank-dependent unit. Fully de-risked. (The bounded-unit case is ONLY
the g150 deepest-point gauge chart, crux2 #51 — not the per-node C1 peel.)
=== COORDINATION + DESIGN ARC EXHAUSTIVELY CLOSED (g132→g153). The grind is pure formalisation. ===

## ACHIEVER WIRING — eq_half_of_binding bundles the multi-axis le_antisymm (pp2 g154)
of_mult_and_achiever calls monomialThreshold_eq_half_of_binding (d i₀)(k i₀)(h i₀) _ hm₀pos (hmult i₀) j₀ hk₀ hh₀
where (hmult i₀) = the within-chart mult-bound (m₀·k≤h+1 on ALL of chart i₀'s axes, the C≥/≥) and j₀ = the
card=m₀ binding axis (the C=∃/≤). So eq_half_of_binding IS the le_antisymm internally — it does NOT assume a
single-axis chart; it composes for my 2-axis (2,2,2) path directly. WIRE IT AS ONE LEMMA CALL (eq_half_of_binding
@ j₀ + hmult), NOT a manual le_antisymm. (2,2,2): u0 (card4,ratio2) + u2 (card3,ratio3/2), ⨅=3/2, j₀=u2,
the within-chart mult-bound pins the min at u2. Consistent g147/g148/g154. Achiever fully routed, no obstruction.

## C1 measure_drops — CORRECTED (crux2 record-correction + controller; supersedes the ΣM≥1 steer)
nodeC1.measure_drops = the det-1 triangular PEEL's Σdrop=2 (the schurState lemma, w:=D−ba / #37 change),
NOT ΣM≥1 (crux2's earlier "Framing A ΣM≥1" steer was imprecise — controller-flagged, retracted). The peel
is NEEDED because {S=0} is bilinear (pivotBlowupOn only hits coordinate subspaces); it clears pivot row+col,
ΣM−2. schurState's M' = (M_0−1, M_1−1, M_2,…), Σdrop=2 via crux2's ChainDimSplit.measure_drops (or my own
schurState lemma threading D↔S+ba). Loss-pullback FACT still = my green schur_node_loss_presentation (the
row-split ‖row0‖²+‖lower‖² — how I PROVE the pullback); the measure_drops WIRING = Σdrop=2 (the peel). I
already have this (g152/g153-converged + /tmp/peel_rank_r). The VALUE (⨅ monomialThreshold = lambdaCore) is
framing-independent. (Same det-1 triangular peel at BOTH per-node C1 (w:=D−ba) AND crux2's #44 deepest-point
gauge chart (g150 T̃) — one mechanism, two levels.)
(pp2's Σdrop=2 / the det-1 triangular peel is the FULLER per-node Schur clear — available if a node ever
needs the one-step ΣM−2, but A's row-split + recurse is the default; same terminating lex, A is simpler.)

=== ALL WIRING + DESIGN CLOSED. Framing A locked. The grind is pure formalisation against this spec. ===

## NON-DEGENERACY HYPOTHESIS (resolved fidelity finding — controller-accepted)
⚠ THIS BLOCK'S "interior" FRAMING IS SUPERSEDED — the LIVE form is ALL-s (∀ s : Fin (L+1), 0 < M s), see
"hMid FORM = ALL-s — CONTROLLER RULING (g191)" below + the committed Skeleton:1030. The "interior" wording
here is the original g154 finding text, kept for history; do NOT quote it as the current predicate.
THE FINDING: the lambdaCore identity rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M) is FALSE for ANY M_s=0
(ANY layer — interior 0-dim cut OR endpoint M_0/M_L=0 = empty matrix): prod_M ≡ 0 ⟹ RLCT=⊤ ≠ finite
lambdaCore. So R1 ASSUMES 0 < M s for EVERY s — NOT discharged. Forced by the formula's correctness.
FRAMING (controller-corrected, precision-faithful): this is OUR FORMALISATION CARVE-OUT — refining the
paper's realisability (r≤min(d⃗), NON-strict ≤, Lehalleur–Rimányi main.tex:1874) to exclude the prod≡0
degeneracy the combinatorial lambdaCore can't see. Sound + consistent within Aoyagi's realisable domain,
but NOT a verbatim-stated Aoyagi assumption. FENCE IT next to the claim as "the formalisation's
non-degeneracy carve-out", NOT "Aoyagi-faithful verbatim". (Optional, deferred, not a gate: deep-read the
DLN preprint to pin whether Aoyagi's genericity implicitly excludes it — nice-to-have for the final
fidelity note.)
THREADING (controller-assigned): I thread it through R1's lemmas; crux2 threads L2 + headline
(aoyagi_learning_coefficient + deepest_point_reduction).
⚠⚠ SUPERSEDED PREDICATE (g154, interior-only — WRONG, kept ONLY for finding-history; DO NOT READ AS CURRENT):
  [headline/L2 (A): ∀ s, 0<s.val → s.val<L → r<H s ;  R1 (B): ∀ s, 0<s.val → s.val<L → 0<M s ;
   "interior 0<s<L, endpoints free, VACUOUS at L=1" — the ENDPOINTS-FREE was the ERROR (g159/g186/crux2:
   M_0=0 / M_L=0 also break the reduced core: prod M ≡ 0 if ANY M_s=0, endpoint or interior; hGne fails).]
CURRENT LIVE FORM = ALL-s (g159/g168, see the "hMid FORM — ALL-s" section below + crux2's PROVEN witness
DeepestCoreNonvanishing dlnLoss_deepest_core_ne_zero_witness needs ∀ s, 1≤M_s): the R1/RouteMTree predicate
is `∀ s : Fin (L+1), 0 < M s` (ALL s, endpoints INCLUDED) — ALREADY committed @0cedc7e (Skeleton:1030).

## hMid FORM = ALL-s — CONTROLLER RULING (g191, git-verified) — CLOSED, do not reopen
CONTROLLER RULING (2026-06-23): git-verified Skeleton.lean:1030 @0cedc7e = `(hMid : ∀ s : Fin (L + 1),
0 < M s)`, docstring "ASSUMES 0 < M s for EVERY layer s." ALL-s is correct AND it is what I committed.
crux2's STOP was reading my SUPERSEDED g154 design TEXT (interior-only), NOT the committed code — the same
stale-text trap as the coreAbsorb gloss. PROCEED: RouteMTree on the all-s predicate (∀ s : Fin(L+1),
0 < M s); ANY M_s=0 (interior OR endpoint) → #70 (degenerate-boundary, design-done @g204, direct Morse
rlctAt=nReg/2, headline non-strict). No re-thread; the code is already right. === hMid CLOSED. ===

## hMid FORM — ALL-s is R1's NATURAL DOMAIN (g159 + g168 audit clarification; g190 crux2 re-confirm)
⚠ The interior-only lock (g154) was INCOMPLETE — missed the ENDPOINTS. SUPERSEDED.
RE-CONFIRMED (g190, crux2 STOP + controller #69/#70 route-B, dated 2026-06-22): the all-s form is RIGHT and
now has PROVEN Lean backing — crux2's DeepestCoreNonvanishing.dlnLoss_deepest_core_ne_zero_witness takes
`hpos : ∀ s, 1 ≤ M s` (ALL s) and the witness e00Witness indexes entry ⟨0, hpos 0⟩ (needs M_0≥1) AND
⟨0, hpos (Fin.last L)⟩ (needs M_L≥1) — the ENDPOINTS are LOAD-BEARING in the discharge of hGne. The
interior-only form does NOT discharge hGne (admits M_0=0/M_L=0 where the identity is ⊤). crux2's #69/#70
decoupling: headline stays NON-STRICT (r ≤ min, paper-faithful); the rungs prove the non-degenerate bulk
∀s M_s≥1; ANY M_s=0 (interior OR endpoint) = the separate #70 direct-Morse case (rlctAt = nReg/2, lambdaCore
= 0). My committed Skeleton:1030 ALREADY carries the all-s form `∀ s : Fin (L+1), 0 < M s` (g159 @0cedc7e) —
crux2's STOP was reacting to the SUPERSEDED g154 block text (now marked); I am ALREADY on B'. The (A')/(B')
split + the defeq bridge (r<H_s ⟺ 0<M_s, all s) confirmed: I thread B' (∀s 0<M_s) on RouteState.M, crux2
threads A' (∀s r<H_s) on L2/headline, #70 owns any M_s=0. L=1 re-check: the all-s form BITES at L=1 (s=0,1);
the (1,1,1) r=1 case (M=(0,0)) is #70 DEGENERATE (lambdaCore=0, rlctAt=nReg/2), NOT the non-deg bulk — the
old "vacuous-at-L=1" conflated the raw-leaf (no interior 0-cut) with the reduced core (can be all-zero-width
at the boundary). PAPER-CHECK (optional, crux2 noted): does Aoyagi state ∀s or interior-only? — our Lean core
needs ALL s regardless (it's the prod M structure, not the citation); if Aoyagi genuinely says interior-only
that's a fidelity question to escalate, but it doesn't change the Lean requirement.
⚠ UPDATE (g168, headline-fidelity audit REVERSED controller Decision A): the HEADLINE stays NON-STRICT
(r ≤ H_s, paper-faithful — the audit VERIFIED the boundary r=H_s is TRUE, so no narrowing to strict).
So R1's all-s domain is NOT inherited from a strict headline; it is R1's OWN NATURAL DOMAIN (the
decomposition genuinely needs all M_s≥1). The HEADLINE case-splits: non-degenerate (all M_s≥1) → the
rungs incl this R1; degenerate boundary (some M_s=0) → a separate direct-Morse lemma (controller #70).
NOTHING CHANGES in R1's work — resolution_charts's `∀ s, 0 < M s` (@0cedc7e) is correct + unchanged; it
is the rung's natural hypothesis, NOT a headline-inherited strict hMid.
R1 DOMAIN (the rung's natural form):
  M-form (R1/resolution_charts): hMid : ∀ s : Fin (L + 1), 0 < M s    [@0cedc7e, correct, unchanged]
  (the headline supplies it on its non-degenerate branch; degenerate → #70's Morse lemma, not R1.)
Historical (the L2/headline H-form, now NON-inherited — headline case-splits instead):
  H-form: ∀ s : Fin (L + 1), r < H s ; bridge M s = H s − r ⟹ (r < H s ⟺ 0 < M s), all s.
WHY all-s (the fidelity catch): R1's identity rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M) is FALSE
whenever ANY reduced width M_s=0 — INTERIOR OR ENDPOINT:
  - interior M_s=0 (0<s<L): prod ≡ 0 (zero-dim intermediate cut).
  - ENDPOINT M_0=0 (r=H_0) or M_L=0 (r=H_L): prod M A : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) is an
    EMPTY matrix ⟹ prod ≡ 0. r=H_0/H_L are REACHABLE under hr (r ≤ H, non-strict). So the endpoints break
    R1's identity (and L2's smooth-block) exactly like the interior. The interior-only form left M_0/M_L=0 in.
- R1 CARRIES it (NOT discharged — ⊤≠finite for any M_s=0). DONE @origin/fm3/routem 0cedc7e:
  resolution_charts carries `(hMid : ∀ s : Fin (L+1), 0 < M s)`, docstring fences both interior+endpoint
  degeneracies, green (2671). crux2 re-threads L2/headline to ∀ s, r<H s + builds the hMid⟹hGne bridge.
- NOT vacuous at L=1 anymore (the all-s form constrains M_0,M_1 even at L=1 — correct: a single zero-width
  layer makes the lone matrix empty ⟹ prod≡0). The earlier "vacuous at L=1" was an artifact of the wrong
  interior-only form.

--- SUPERSEDED (g154, interior-only — finding-history only; predicate text REMOVED to stop re-quoting) ---
[The g154 form was an interior-only guard (Fin-L-indexed, dropped s=0/H_0 and never reached H_L). The
 "endpoints free" was the GAP — r=H_0/H_L break R1's identity. CORRECTED to all-s (∀ s : Fin (L+1), 0 < M s),
 committed Skeleton:1030 @0cedc7e. The verbatim interior predicate is deliberately NOT reproduced here — it
 kept getting copy-quoted as the live form (4× this session). LIVE form is all-s, full stop.]

## ARCHITECTURE FINDING (g155, Codex-decorrelated + crux2's own design docstring) — RESHAPES #39
THE FORK on the general-M R1: my RouteMTree.lean re-invents a recursion-state (RouteState/schurState/
classify) that PARALLELS crux2's banked ChainDimSplit + schur_recursion_step_sound (GeneralR1Recursion.lean,
route-m-atlas). Codex xhigh (routeM-division-{prompt,answer}.md) + crux2's OWN docstring converge:
- crux2's GeneralR1Recursion docstring (line 20-22) STATES the intended division: "the general-M chart is
  the det-1 straightening (crux2) THEN a blow-up (monomial Jacobian → ⨅ monomialThreshold, **fm's cover
  lane**, applied to the residual G)." So the seam was crux2-designed: crux2 = straightening phase
  (schur_recursion_step_sound: rlctAtOn(dlnLoss M 0) = nReg/2 + rlctAtOn(dlnLoss Mred 0), MP-chart-gated);
  fm = the blow-up cover lane (⨅ monomialThreshold via the per-node pivotBlowupOn + cover-split).
- TWO orthogonal mechanisms, BOTH needed (refines Codex's "telescoping replaces cover" — too strong):
  (i) ADDITIVE-along-a-path: crux2's per-step nReg/2 descent → each leaf's accumulated value.
  (ii) MIN-over-branches: the ⨅ over leaves = min over reduction paths = MY cover-split (argmaxCellOn pivot
       cells, the branching). The ⨅ is NOT reconstructed by telescoping a single chain — it's the min over
       the BRANCHING the cover-split produces. So cover_le/_ge_div ARE the right vehicle for the min-half.
- PARALLEL-RECURSION HAZARD (Codex #3, AGREE): my standalone RouteState is a liability IF it duplicates
  ChainDimSplit's state-transition. FIX (Codex shape): the recursion DRIVER should be shared (crux2's
  ChainDimSplit step relation); fm owns the leaf MonoData ACCUMULATOR + threshold proofs + the cover
  branching, NOT an independent state-transition system. My routeAtlas should consume crux2's reduction
  state, not re-derive schurState.
- LOAD-BEARING ASSUMPTION (Codex flagged, VERIFIED): schur_recursion_step_sound's chart hypothesis
  (hfactor: dlnLoss M 0 ∘ χ = u·(∑x² + G²)) IS the per-node factorisation — dischargeable from my G2
  node_loss_pivot_factor + crux2's schur_straighten_of_data. Confirmed against the actual signature.
- hGne RE-SURFACES PER-STEP: schur_recursion_step_sound takes (hGne : ∃ U ∈ nhds 0, ∀ᵐ z, G z ≠ 0) on the
  REDUCED core EACH step. This is the hMid⟹hGne crux2 owns — but it's needed at every recursion level, not
  once. Confirms hGne is crux2's (the straightening lane consumes it); my cover lane does not.
DECISION OWED: the controller + crux2 must confirm the seam (straighten=crux2 / branching-cover=fm, both
needed) before I grind. NOT a unilateral call — it sits exactly on the crux2/fm3 boundary. SURFACED.
CONCRETE FORK-INDEPENDENT NEXT STEP (Codex #4, useful in every division): the per-step MonoData→(d,k,h)
threshold-update lemma — `monomialThreshold (addPivotDivisor d k h) = …` relating a node's added pivot
divisor (1, card−1) to its monomialThreshold contribution. Pure (d,k,h) combinatorics, no recursion,
no cover. Stackable now.

## VALUE-SIDE BEDROCK BANKED (fm3, @origin/fm3/routem 870afff) — appendDivisor min-fold
The fork-independent value-side accumulation atoms (RouteMState.lean, green, clean-three + monomial_rlct):
- `MonoData.appendDivisor md c := ⟨md.d+1, Fin.snoc md.k 1, Fin.snoc md.h (c-1)⟩` — snoc the codim-c
  exceptional axis (1, c−1).
- `iInf_fin_succ_eq_min_last` : ⨅ over Fin(d+1) = min(last, ⨅ castSucc-prefix). Generic ℝ≥0∞, clean-three.
- `monomialThreshold_appendDivisor` : monomialThreshold (md.appendDivisor c) = min(c/2, monomialThreshold md).
- `monomialThreshold_appendDivisor_ge` : append codim-≥m₀ ⟹ preserves ≥ m₀/2 (threshold_ge inductive step).
- `monomialThreshold_appendDivisor_le_binding` : append codim-m₀ ⟹ ≤ m₀/2 (achiever upper bound).
These are the per-node folds of IsResolutionAtlas's threshold_ge (C≥) and achiever (C=∃). They compose
along ANY append-recursion, so they survive whatever A/B/C division the seam decision picks. The achiever
transcription (pp2 g148) lands by folding _le_binding at the binding node + _ge elsewhere, down to a ⊤
leaf (leafMonoData_threshold) — le_antisymm gives = m₀/2. The MonoData accumulator is fm's regardless
(Codex #3: fm owns the leaf data accumulator + threshold proofs; only the state-transition DRIVER may
rebase onto crux2's ChainDimSplit).

PER-PATH FOLD BANKED (@origin/fm3/routem a446bcd): the closed-form per-leaf value.
- `MonoData.foldDivisors cs` : fold appendDivisor over a codim list (one path's appends).
- `ratioMinFold cs` (+ _nil/_cons) : ℝ≥0∞ min-fold of the ratios c/2.
- `monomialThreshold_foldDivisors` : monomialThreshold (foldDivisors cs) = ratioMinFold cs.
- `ratioMinFold_le_of_mem` / `ratioMinFold_ge_of_all_ge` : the two list-min bounds.
- `monomialThreshold_foldDivisors_eq_of_binding` : all-codim ≥ m₀ ∧ m₀ ∈ cs ⟹ threshold = m₀/2.
  ⟹ the IsResolutionAtlas achiever VALUE, in Lean, for one reduction path (pp2 g148 transcribed).
SESSION STATE (g155): hMid threaded (6f4e70f) + full value-side bedrock (3b2ba20→a446bcd), all green
sorry-free clean-three(+monomial_rlct). RouteMTree.lean stays UNCOMMITTED (all-stub) pending the seam
decision — do NOT bank the parallel RouteState recursion until controller+crux2 confirm the driver
(rebase onto ChainDimSplit vs standalone). The recursion DRIVER is the only piece blocked.

## SEAM DECIDED + REBASE (controller g156) — DRIVER = crux2's ChainDimSplit; drop RouteState
(a) SEAM: crux2 = per-step straighten / additive nReg/2 descent (ChainDimSplit, value-along-a-path);
    fm = the blow-up cover / ⨅-min-over-pivot-branches (→ ⨅ monomialThreshold). BOTH needed; the cover
    STAYS (it IS the ⨅), on top of crux2's descent. My refinement accepted (telescoping ≠ the cover).
(b) REBASE: YES. Drop the parallel RouteState; rebase the descent-STATE onto crux2's banked ChainDimSplit.
    Keep the cover-branching + the MonoData accumulator + threshold proofs ON TOP (fm's, per Codex #3).
    Coordinate the ChainDimSplit interface with crux2 (my 3 questions → crux2 answers + extends
    ChainDimSplit if the cover-branching needs more). Controller told crux2 to support it.
CONSEQUENCE for my files: RouteMState's RouteState/widthSum/ncDefect/routeMeasure/routeRel/routeRel_wf
become DEAD (superseded by ChainDimSplit + its hdrops/ΣM termination) — but MonoData + leafMonoData +
ALL the appendDivisor/foldDivisors threshold lemmas (3b2ba20→a446bcd) are KEPT (they're on MonoData,
recursion-driver-agnostic). RouteMTree's routeAtlas gets rewritten to recurse over ChainDimSplit
(consume crux2's reduction state), NOT WellFounded.fix on RouteState. AWAITING crux2's reply on the
ChainDimSplit interface shape + whether it carries the per-node pivot-branch data my cover needs (the
argmaxCellOn pivot cells per node = the branching). Until then: stay on fork-independent value-side.

## ChainDimSplit API STUDIED (g157) — the rebase is NOT a mechanical swap; the taxonomy changes
Read crux2's banked ChainDimSplit (GeneralR1Recursion.lean @route-m-atlas). Three findings reshape the rebase:
1. ChainDimSplit M = a SINGLE one-step width split {drop, red, hsum : drop+red=M, hdrops : 0<Σdrop}. NOT a
   branch family, NOT iterated. L is FIXED (it reduces WIDTHS M→red, never depth). Termination = ΣM drops by
   Σdrop≥1. So my old L-dropping C2/C4 taxonomy does NOT map — crux2's recursion is pure ΣM-width-reduction.
2. ChainDimSplit is only ever CONSUMED in GeneralR1Recursion (schur_straighten_of_data / _squeeze /
   rlctAtOn_reduced_transport all TAKE an (S : ChainDimSplit M)); it is NEVER CONSTRUCTED there. So the
   rank-pattern dispatcher (WHICH split at each node = my old classify) is UNPROVIDED — still the producer's
   (my) job. The rebase makes my recursion PRODUCE ChainDimSplits (consume the carrier type) rather than my
   own RouteState; it does NOT hand me a banked recursion.
3. NO banked WF recursion over iterated ChainDimSplit exists. I build the fix myself: recurse M → S.red via a
   per-node ChainDimSplit, terminating on ΣM (hdrops ⟹ ΣS.red < ΣM), base at L=1 / red≡0 (dlnLoss_one_layer_deepest).
SHARPENED QUESTION to crux2 (supersedes Q1/Q2): does crux2 CONSTRUCT the per-node ChainDimSplit (the
rank-pattern → split dispatcher) or do I? If I do, the rebase = (i) swap my RouteState carrier for
(M, ChainDimSplit M); (ii) keep my pivot-branch Finset + the ⨅-min on top (branching is mine — ChainDimSplit
is single-path); (iii) my recursion produces, at each node, a Finset of child ChainDimSplits (one per pivot
cell) + folds MonoData via appendDivisor; (iv) terminate on ΣM. The carrier becomes (M, ChainDimSplit M) not
RouteState, but the RECURSION + BRANCHING + CONSTRUCTION are still mine. The "rebase" narrows to: use crux2's
split TYPE + its transport lemmas, not a fresh state machine — value/cover layers unchanged.

## REBASE FOUNDATION BANKED (g158, @origin/fm3/routem 55db82d) — RouteMRecursion.lean
The construction-agnostic recursion driver, rebased onto ChainDimSplit (replaces the dead RouteState/
routeMeasure/routeRel_wf). New file RouteMRecursion.lean (imports GeneralR1Recursion for ChainDimSplit +
RouteMState for MonoData; NO RouteMBridge/RouteMAtlas — single-writer-safe; green, clean-three):
- `chainWidthSum M := Σ M` — the termination measure.
- `ChainDimSplit.redM_widthSum_lt` : Σ S.red < Σ M (from hsum+hdrops; extracted from crux2's inlined proof).
- `chainRel N M := chainWidthSum N < chainWidthSum M` + `chainRel_wf` (InvImage of < on ℕ) — the WF carrier
  for the iterated Route-M WellFounded.fix.
- `ChainDimSplit.redM_chainRel` : any split descends along chainRel (the recursive-call descent proof).
These hold WHOEVER constructs the per-node split — the recursion skeleton stands. STILL GATED on crux2's
"who builds the per-node ChainDimSplit" reply: the WellFounded.fix BODY (the per-node step: produce the
pivot-cell Finset + child splits + fold MonoData + layer the cover) needs the split-construction interface.
NOT building the fix body until the answer lands (avoids baking a wrong split-construction shape).
NEXT (when crux2 replies): the fix body over chainRel_wf → NodeChartFamily; then the cover-branching
(g5_pivotNode split per node) + wire isCover/isValue → RouteMAtlas.

## SEAM FULLY RESOLVED (crux2 #66) + FIX-BODY SKELETON ROUTE-CHECKED (g160)
crux2 #66 answer: **fm3 CONSTRUCTS the dispatcher.** ChainDimSplit = the consumed minimal width-only
carrier (never constructed in GeneralR1Recursion); the pivot-cell coord-center lives in the paired
IsSchurStraightenSqueeze datum (field 3, COORD-CENTER), NOT in ChainDimSplit. My termination lemma
redM_widthSum_lt = crux2's proposed sum_red_lt (don't double-add). CONSUMER RECIPE (3 transport pieces
my recursion folds per node): schur_straighten_squeeze_of_data (nReg/2 descent, consumes my squeeze datum)
▸ rlctAtOn_reduced_transport (G²→dlnLoss S.red 0 at redZero) ▸ recurse on S.red ▸ dlnLoss_one_layer_deepest
(L=1 leaf).

FIX-BODY SKELETON — ROUTE-CHECKED GREEN (RouteMRecursion.lean, UNCOMMITTED, single sorry = routeStep):
- NodeChartFamily M {ι : Type, fintype, data : ι → MonoData} (Type 1, carries the Type field).
- RouteStep M : Type 1 := leaf (md) | branch (cells : Type) (cellsFin) (split : cells → ChainDimSplit M)
  (codim : cells → ℕ). The dispatcher's output. [Type 1 needed — the Type-valued cells field.]
- routeStep M : RouteStep M := sorry  ← THE substantive dispatcher (rank-pattern → leaf|branch).
- routeAtlas := WellFounded.fix chainRel_wf (leaf↦PUnit chart with md; branch↦Σ over cells of
  rec (split c).red [(split c).redM_chainRel] + ((child).data).appendDivisor (codim c)). Fintype derives.
- routeMIota/Fintype-instance/routeD/routeK/routeH extraction. ALL type-checks around the one sorry.
RouteMTree.lean (old parallel-RouteState stub) DELETED (untracked, superseded).

THE OPEN CORE = routeStep (the rank-pattern dispatcher). FINDING (g160): NO banked construction precedent —
even the (2,2,2) case (Case222Resolution.lean) is hand-built concrete coordinate maps (step1A=pivotBlowupOn
{0,1,2,3} 0, etc.) over Fin 8/Fin 7, NOT a ChainDimSplit instance. So routeStep is from-scratch combinatorial
work: given M, decide leaf-vs-branch + (for branch) the Finset of pivot cells + each cell's (drop,red) split
+ codim, from the rank pattern (Adm cone / pivotBlowupOn argmaxCellOn structure). This is design-space
combinatorics — pp2's lane. CANNOT commit the fix-body until routeStep is filled (sorry-gate). The skeleton
green VALIDATES the rebase shape end-to-end; routeStep is the substantial remaining grind (likely needs a
pp2 split-construction cert: rank-pattern → (drop,red) per node, generalizing the (2,2,2) hand-build).

## CRITICAL SPECIFY FINDING (g161, Codex xhigh routeStep-type-{prompt,answer}.md) — the VACUITY TRAP
The bare `RouteStep.branch (split) (codim)` is TOO WEAK: it gives a SYNTACTIC recursion, not a mathematical
resolution. A routeStep returning ARBITRARY splits TYPE-CHECKS and routeAtlas produces SOME (d,k,h) — but
DISCONNECTED from dlnLoss M 0. The value identity rlctAtOn(dlnLoss M 0) 0 = ⨅ monomialThreshold would then
be UNPROVABLE (the (d,k,h) isn't tied to the loss). Codex CONFIRMS (decisive): filling routeStep with
arbitrary splits is STRICTLY WORSE than the sorry — it manufactures a misleading "resolution" object that
lets downstream prove a false-flavoured identity. THE GUARD: never use routeAtlas M as a resolution unless
paired with a correctness proof built from CERTIFIED steps.
THE FIX (Codex, my SPECIFY corrected): RouteStep.branch must carry (or a ValidRouteStep M predicate must
assert) the per-cell TRANSPORT DATUM — the IsSchurStraightenSqueeze-existence that PROVES each split
factorises the loss (core ∘ φ = unit·(Σx² + dlnLoss S.red 0)). Without it the split is meaningless.
SEPARABILITY (Codex): dispatcher and identity ARE separable AFTER enriching — the clean architecture is
  routeStep : M → RouteStep M        (raw plumbing — termination only)
  ValidRouteStep M (routeStep M)     (the per-cell squeeze/reduced/cover certificates)
then a GENERIC FOLD theorem `routeAtlas_correct_given_valid` : (every branch certified) ⟹ rlctAtOn = ⨅
monomialThreshold, by well-founded induction matching routeAtlas. The dispatcher's REAL obligation is
"construct cells + decreasing splits + the per-cell transport datum", NOT "choose smaller reds".
MY NEXT (the formaliser's lane, INDEPENDENT of pp2's split-construction): build ValidRouteStep + the
generic fold theorem (Codex's minimal-honest-step items 1-2) — the GUARDRAIL + the target shape pp2's #67/#68
designs against ("get target-shape from fm3 first"). pp2 designs the rank-pattern → certified-RouteStep
recipe (#68); I provide the certified type + prove the fold; pp2's construction populates it.

## SCOPING DECISION (g162) — co-design the ValidRouteStep fields with pp2's #68, don't build blind
The ValidRouteStep certificate must carry, per branch cell, crux2's schur_straighten_squeeze_of_data
consumed data: nReg, a reduced ambient Y (+ PseudoMetricSpace/MeasureSpace/ProperSpace/BorelSpace/Zero
instances), flatCore, G, redEmbed (≃ₜ Params S.red), c₁ c₂, the IsSchurStraightenSqueeze datum, the
node-loss-identification (flatCore = the node's dlnLoss in blow-up coords), and the cover fact. This is a
HEAVY dependent structure (the Y/instance/universe bundling — same friction as RouteStep : Type 1). The
EXACT field list depends on pp2's #68 construction (designing it blind = the very wrong-type iteration the
vacuity-trap find just caught — "state the suspect hypothesis as a known unknown, resolve before proving";
the certificate's field list IS that hypothesis, #68 is its resolution-in-flight). So: HOLD the certificate
construction for #68; co-design the fields once pp2's recipe lands. SENT pp2 the target shape (the consumed
data + the additive-vs-min reconciliation the 3 correctness args must satisfy).
BANKED THIS SESSION (all green, @origin/fm3/routem aeca9a3): hMid all-s (0cedc7e); value-side foldDivisors
achiever+threshold_ge (fd4a622); rebase foundation chainWidthSum/redM_widthSum_lt/chainRel_wf/redM_chainRel
(55db82d). UNCOMMITTED route-check artifact: the recursion skeleton (NodeChartFamily/RouteStep/routeAtlas/
extraction, single routeStep sorry) — validates the rebase shape; RouteStep type PROVISIONAL (→ ValidRouteStep
once #68 co-design lands). The recursion DRIVER stands; the dispatcher + certificate are the #68-gated grind.

## CONSISTENCY CONTRACT BANKED (g163, @bef5ba5) — controller's critical item (iii), machine-checked
The value-side ⟹ IsResolutionAtlas bridge — pp2's dispatcher leaf-monomials AGREE with my foldDivisors
achiever BY CONSTRUCTION, no separate consistency proof. RouteMState.lean, green, clean-three+monomial_rlct:
- `foldFamily_threshold_ge` (ι codimsOf m₀ ...) : (∀ i, ∀ c∈codimsOf i, m₀≤c) ⟹ ∀ i, ½·m₀ ≤
  monomialThreshold(foldDivisors (codimsOf i)). [crux2 IsResolutionAtlas.threshold_ge, C≥]
- `foldFamily_achiever` (ι codimsOf m₀ i₀ ...) : (minimiser i₀: ∀ c∈codimsOf i₀, m₀≤c ∧ m₀∈codimsOf i₀) ⟹
  ∃ i, monomialThreshold(foldDivisors (codimsOf i)) = ½·m₀. [crux2 IsResolutionAtlas.achiever, C=∃]
Stated over an ABSTRACT leaf family (ι, codimsOf) — branch-version-independent (my branch's
ResolutionAtlas.lean carries the STALE stratum/threshold_eq form; crux2's route-m-atlas has the
threshold_ge/achiever form; this bridge targets the latter via the two facts directly, not the struct).
THE CONTRACT for pp2's #68 (m₀ = (Adm M).inf' Mval = the min codim; lambdaCore = ½·m₀): design the
dispatcher's per-leaf codims so (a) ∀ path, ∀ pivot codim ≥ m₀ (no undershoot); (b) the min-Mval path's
binding pivot codim = m₀. Then (a)+(b) ⟹ IsResolutionAtlas ⟹ ⨅ monomialThreshold = lambdaCore. (2,2,2):
m₀=3 (codim-3 rank-1 incidence), binding path → (1,2) ratio 3/2 = lambdaCore; others ≥3. SENT pp2.
=== MEANWHILE-WORK (controller i/ii/iii) DONE: interface target shape (i) + consumer recipe (ii) sent;
consistency contract (iii) machine-checked + banked. The dispatcher itself = pp2 #68 → I transcribe. ===

## ADDITIVE-vs-MIN RESOLVED (g164, the (2,2,2) numerical check) — per-node op is MIN, not +nReg/2
Building the schematic fold guardrail, I checked the (2,2,2) leaf BEFORE committing to the per-cell
consequence shape — and it resolves the additive-vs-min tension decisively (find-confound: numerics
before build):
- (2,2,2) leaf (Case222Rlct): d=2, k=(1,1), h=(3,2). monomialThreshold = ⨅(axisRatio 3 1, axisRatio 2 1)
  = min(4/2, 3/2) = min(2, 3/2) = 3/2 = lambdaCore. TWO axes: (1,3) ratio 2 [step-1 A-pivot |det|=x³] +
  (1,2) ratio 3/2 [step-2]. The RLCT is the MIN over axes = EXACTLY my appendDivisor/foldDivisors min-fold.
- The per-node operation is MONOMIAL (core ∘ φ = x_p²·reduced — my G2 node_loss_pivot_factor; confirmed
  by myF222_step1A: myF222 ∘ step1A = y0²·Q), folded by MIN via the cover. NOT the additive +nReg/2.
CONSEQUENCE for the schematic fold: the value/min lane and the additive/transport lane are SEPARATE,
both real (g164 + pp2 g183 confirm, verified vs RouteMState). The CLEAN reconciliation (pp2, precise):
- ADDITIVE nReg/2 = the smooth Morse residuals ∑E² = SPECTATOR axes (k=0, axisRatio=⊤) in monomialThreshold;
  they do NOT bind the ⨅; in the cover integrand they're the bounded-below UNIT factor (monomial·UNIT).
  The additive nReg/2 is the TRANSPORT direction (how each cell's rlct relates to its reduced core ⟹
  proves cover_le) — NOT off-path, just not in the value/min. (My earlier "off-path" framing was imprecise:
  it's the transport/cover_le lane, distinct from value.)
- MIN over EXCEPTIONAL divisors (k=1) = what foldDivisors min-folds. The leaf's (k,h) carries ONLY these.
THE CRISP VALUE CONTRACT (pp2, verified vs my foldFamily_*): codimsOf(i) = [Mval of each C1/C5 pivot stratum
along path i] — EXCEPTIONAL divisors ONLY, nReg smooth dims NOT included. My foldFamily_threshold_ge/_achiever
already take exactly this (NO additive nReg/2 in them — pp2 checked RouteMState). (2,2,2) verified: unit-leaf
codimsOf=[4,3], block-leaf=[4,3,4]; all ≥3, 3∈[4,3] for minimiser ⟹ ⨅=3/2=lambda ✓.
GENERIC FOLD STRUCTURE (pp2): rlctAtOn(dlnLoss M 0) 0 = ⨅ over leaves of foldDivisors(codimsOf i), each
leaf's value justified BY the per-cell transport down its path. Keep the additive (transport, cover_le)
SEPARATE from the min (value, foldDivisors). So the per-cell certificate carries BOTH: the transport
(additive nReg/2 + reduced reindex = crux2's lane, the cover_le justification) AND the codim=Mval witness
(PivotWitness, the value/min). The transport-field's exact shape (crux2's IsSchurStraightenSqueeze vs the
lighter monomial-pullback) is STILL crux2's in-flight adjudication — but the value-side is settled + banked.

## pp2 #68 CERT LANDED (g183, origin/g183-routestep-dispatcher @1ac5de4) + §2 BRIDGE BANKED (g165)
pp2's dispatcher cert delivered — confirms g164 (per-node op = monomial min-fold, codims = Mval) + adds
the load-bearing refinements:
- §1.1 LEAF = `IsUnit residualCore` (NOT "no C1 applies" — Codex #5; scalar/rank-1 remnants would be
  misclassified, dropping a binding divisor).
- §2 THE C1-CONDITION (the single CERTIFIED-vs-green-wrong seam, Codex #1/#4 = pp2 #138, re-found):
  every pivot codim = Mval M T for an ADMISSIBLE T, NOT raw coord cardinality / Jacobian rank (the
  (4,3,2) thin-product trap). So `codim` is NOT a bare ℕ — it pairs with `witness : {T // Adm M T ∧
  codim = Mval M T}` + the mult-1 proof (k,h)=(1,c−1). Without it C≥ is unprovable.
- §4 REACHABILITY (C=∃): a named realizability lemma (∀ minimiser T*, a legal chart path reaching S_{T*}
  with binding codim = Mval(T*)); rides Core.baseChange_normalForm; only the minimiser need be reached.
- §5 validated (2,2,2)/(3,2,3)/(2,2,2,2)/(4,3,2) against the QIP minAdm ground-truth; codim-sequence =
  rank-descent, min codim on achiever path = minAdm.
- §6 ValidRouteStep field list (co-designed) — what I transcribe.
BANKED (g165, @dd6bdb5, the §2 value-side discharge):
- `minAdm_le_Mval_toNat` : T ∈ Adm M ⟹ minAdm ≤ (Mval M T).toNat (Finset.inf'_le; clean-three). The
  admissible-T witness mechanically gives no-undershoot.
- `foldFamily_threshold_ge_of_admWitness` : leaves built from admissible-T-witnessed codims ⟹ ∀ leaf,
  ≥ ½·minAdm. The §2 C≥ consequence, value-side — exactly what pp2's witness field delivers.
So the §2 green-≠-right guard is now machine-checked on the value side: the dispatcher's threshold_ge
holds BY the admissible-T witness. STILL AWAITING crux2 on the transport-field (additive-vs-min / which
lemma the per-cell consequence uses) before pinning the full ValidRouteStep + building the fold.

## SPELL-OUT DONE + ENCODING-MATCH VERIFIED (g177, pp2 g195 @1de75f0 + fm3 example-check)
pp2 spelled (2,2,2)/(3,2,3) against the pinned LIGHT RouteStep.branch @b8d3146 — both type-check,
reproduce Case222Resolution exactly. Per branch cell = (schurState split, (Mval M T).toNat codim,
⟨T,hAdm,hCodim⟩ witness); leaf = MonoData; transport = light node_loss_pivot_factor (discharged at the
cover-fact). (2,2,2): ROOT A-pivot, red=schurState(2,2,2)=(1,1,2) [ΣM 6→4], binding T=(0,0) codim 4
(=step-1 card4); RECURSE (1,1,2) step-2, binding T=(1,0) codim 3 (=step-2 card3=minAdm); LEAF unit;
codimsOf(binding)=[4,3] → ratioMinFold=min(2,3/2)=3/2=λ ✓. (3,2,3): red=schurState=(2,1,3) [ΣM 8→6],
binding T=(1,0) codim 5=minAdm, other T=(0,0) codim 6, ⨅=5/2=λ ✓.
ENCODING-MATCH (fm3, /tmp/routestep_shape_check.lean): I type-checked pp2's spell-out SHAPE against my
RouteStep as an example — RouteStep.branch cells inferInstance split codim witness elaborates; the leaf
arm elaborates; PivotWitness ⟨T,hAdm,hCodim⟩ matches. So NO re-encoding needed (pp2's last concern closed):
the transcription is mechanical. pp2's design lane is COMPLETE (g183 recipe → g186/187 fold-target →
g188 light → g189 transcription-ready → g190 per-node dischargeable → g194 C5 exercised → g195 spell-out).

## VALUE SIDE CLOSED + VERIFIED (g172, pp2 g190) — PivotWitness dischargeable per node
pp2 g190 verified PivotWitness @040a997 dischargeable per node across all validation cases (the rank-descent
construction): each C1/C5 pivot cell resolves one rank stratum; its PivotWitness carries T = that admissible
stratum (∈ Adm M), codim = (Mval M T).toNat; minAdm_le automatic. Verified (2,2,2) [step-1 T=(0,0) codim 4,
step-2 T=(1,0) codim 3=minAdm — matches the anchor], (3,2,3) m₀=5, (2,2,2,2) m₀=3, (4,3,2) m₀=6 (thin).
PRECISION pp2 confirmed (the subtlety in PivotWitness): T and codim are w.r.t. the NODE's M, codim = Mval of
the rank stratum the node RESOLVES (the geometric codim) — while the recursion's schurState tracks WIDTHS.
Consistent: the dispatcher constructs PivotWitness per pivot from the rank-descent T (the admissible rank
pattern resolved at that node), separate from the width-bookkeeping. So C≥ (foldFamily_threshold_ge_of_pivotWitness)
+ C=∃ (foldFamily_achiever, §4 achiever i₀ reaches T*) ⟹ IsResolutionAtlas ⟹ ⨅=lambdaCore BY CONSTRUCTION,
no new lemma. VALUE-SIDE VERIFICATION: DONE (pp2). The ONLY pending field = the per-cell TRANSPORT (crux2's
light-G2-vs-heavy-squeeze, the analytic wrapper — not the value side).

## TRANSPORT-FIELD FINAL (g178, crux2 #73 confirm) — ALIGNS with g175 light; splits A(mine)+B(crux2)
crux2's #73 reconciliation CONFIRMS g175 (R1 is light; heavy IsSchurStraightenSqueeze retracted = L2-
additive lane). The per-cell transport is LIGHT and splits into TWO, only ONE a crux2 field:
(A) MONOMIAL PULLBACK (x_p² blow-up → appendDivisor codim) = MINE (G2 node_loss_pivot_factor / cover-fact,
    value-side; pivotBlowupOn chart in S1G5Charts, Jacobian |u|^{Mval−1}). Threaded at the cover-fact level
    (monomialThreshold / appendDivisor). NOT a crux2 field.
(B) DET-1 REDUCED-CHAIN TRANSPORT = crux2's rlctAtOn_reduced_transport (BANKED, det=1 MP, recursion-CLOSING):
    per cell c (S = split c), the field datum = (G, redEmbed : Y≃ₜ Params S.red, hmp : MeasurePreserving,
    hemb : MeasurableEmbedding, redZero, hzero : redEmbed 0 = redZero, hredCore : ∀y, G y^2 = dlnLoss S.red 0
    (redEmbed y)) ⟹ rlctAtOn(G²) 0 = rlctAtOn(dlnLoss (split c).red 0) redZero. THIS is the per-cell transport
    field (NOT IsSchurStraightenSqueeze).
ASSEMBLY per cell c: (my blow-up → G² + appendDivisor codim c) ▸ (crux2's rlctAtOn_reduced_transport closes
descent to (split c).red, child basepoint redZero) ▸ recurse (ΣM drops, my redM_widthSum_lt) → ⨅ monomialThreshold.
DECISION: bundle B as a STRUCTURE field (matches PivotWitness's structure-sibling pattern; tidier than the raw
7-tuple). I define the `ReducedTransport M S` structure on my side (referencing crux2's rlctAtOn_reduced_transport
as the consuming lemma); crux2 confirmed it'll give the exact type if wanted. So the certified RouteStep.branch
per cell = (split, codim, PivotWitness [value], ReducedTransport [crux2's det=1 datum]); the monomial pullback (A)
is at the cover-fact, not a branch field. ALL THREE THREADS NOW ALIGNED on light.

## ReducedTransport BUILT (g179, route-checked green clean-three) — the light det-1 transport, bundled
I defined the bundled type myself (have rlctAtOn_reduced_transport's signature; no need to wait on crux2's
delivery). RouteMRecursion.lean (route-checked green; sorry-free DECL, only routeStep elsewhere has the sorry):
  structure ReducedTransport {L} {M} (S : ChainDimSplit M) (Y : Type)
      [MeasureSpace Y] [TopologicalSpace Y] [Zero Y] where
    G : Y → ℝ ; redEmbed : Y ≃ₜ Params S.red ; hmp : MeasurePreserving redEmbed volume volume
    hemb : MeasurableEmbedding redEmbed ; hzero : redEmbed 0 = (fun _ => 0 : Params S.red)
    hredCore : ∀ y, G y ^ 2 = dlnLoss S.red 0 (redEmbed y)
  ReducedTransport.descent (rt) : rlctAtOn (fun y => rt.G y^2) 0 = rlctAtOn (dlnLoss S.red 0) (fun _ => 0)
    := rlctAtOn_reduced_transport S rt.G rt.redEmbed rt.hmp rt.hemb _ rt.hzero rt.hredCore   -- clean-three.
DESIGN CHOICES (resolved): (i) Y = a STRUCTURE PARAMETER with [instances] (NOT a field — Lean can't make a
field an instance for later fields; the param-binder route works), bumping RouteStep to Type 1 (already is).
(ii) Type-valued (carries G/redEmbed so the dispatcher/cover reads them). (iii) redZero PINNED to the
layerwise-zero tuple `fun _ => 0 : Params S.red` (Params has NO canonical Zero — GeneralR1Recursion:647 — so
the deepest point is the explicit fun, NOT `0 : Params`; this was the build error, fixed). The descent closes
to the CHILD's deepest point, composing with the recursion. clean-three (rests on crux2's banked S1 transport,
not even monomial_rlct). CANNOT commit RouteMRecursion.lean (routeStep sorry) — route-checked, durably here.

## TRANSCRIPTION-READY (g171, pp2 g188/g189 @a60bfda) — no open combinatorial question
pp2 confirmed transcription-ready, three final pins all aligned with my banked value-side:
1. CODIM = the witnessed (Mval M T).toNat form (= my PivotWitness). pp2 verified Mval ≥ 0 on Adm M
   (g189_mval_nonneg.py: each summand (t_{j-1}−t_j)(M_j−t_j) ≥ 0 by admissibility, 9 cases) so the toNat
   round-trip is FAITHFUL.
2. VALUE → my EXACT banked bridges (cleaner than (a)+(b)): C≥ = foldFamily_threshold_ge_of_admWitness (the
   §2 witness feeds directly; minAdm_le_Mval_toNat gives no-undershoot, automatic); C=∃ = foldFamily_achiever
   (§4 reachability). ⟹ IsResolutionAtlas ⟹ ⨅=lambdaCore by construction. No new lemma.
3. TRANSPORT-FIELD = crux2-pending = the ONLY open piece (analytic wrapper, NOT recipe). pp2 g188 converges
   with my g164: light G2 node_loss_pivot_factor + rlctAtOn_reduced_transport; heavy IsSchurStraightenSqueeze
   off-path. Light-vs-heavy waits on crux2's lemma-mapping — wrapper only.

## ⚠ TRANSPORT-FIELD — g173 WAS WRONG (heavy); CORRECTED to LIGHT (g175, controller catch + pp2 g188 + code)
g173 (below, SUPERSEDED) accepted crux2's veto framing "R1 node → schur_straighten_squeeze_exists,
presentation in IsSchurStraightenSqueeze (heavy)". That is WRONG for R1. The controller caught the tension
vs pp2 g188; I verified against the (2,2,2) code (Case222Resolution): R1's per-cell datum is the LIGHT
monomial pullback, NOT the heavy squeeze.
EVIDENCE (grounded, not asserted): Case222Resolution has ZERO mentions of IsSchurStraightenSqueeze /
schur_recursion_step / c₁ / c₂. step1A = pivotBlowupOn {0,1,2,3} 0; myF222 ∘ step1A = y0²·Q (a MONOMIAL
pullback, my G2 node_loss_pivot_factor); step1A_det = y0³ (node_jacobian_det). The (2,2,2) leaves USE the
light pullback. The heavy IsSchurStraightenSqueeze (c₁Φ ≤ flatCore ≤ c₂Φ, additive nReg/2) is the L2 /
DEEPEST-GAUGE node (g150/g175 core_comparability_squeeze, #54) — a DIFFERENT node (the full-B regular-shift
reduction), NOT R1's blow-up node. crux2's veto conflated R1's blow-up node with L2's gauge node.
CORRECT R1 per-cell transport (LIGHT, all mine + the det=1 reindex):
  node_loss_pivot_factor (core∘φ = x_p²·(core∘hardPivotAt), banked G2) + node_jacobian_det ((x_p)^{card−1},
  banked G2) ⟹ per-cell rlct = MIN(codim/2, rlct(reduced)), recursing → foldDivisors MIN-fold; the reduced
  core reindexes via rlctAtOn_reduced_transport (crux2's det=1, the only crux2 piece R1 needs). NO
  IsSchurStraightenSqueeze, NO c₁/c₂, NO additive nReg/2, NO hnode production. My EARLIER g164 was RIGHT;
  g173's "crux2 veto resolved it to heavy" was the error (relayed crux2's L2-node framing onto R1).
- LEAF (L=1/red≡0): dlnLoss_one_layer_deepest.
- MIXED C5: compose (C2-survivor ⊕ C1-complement), the C1-complement is a LIGHT pivotBlowupOn node (NOT a
  heavy squeeze) — pp2 g192/g193 exercised on (3,3,2) (the complement residual ‖S·Γ‖² is the reduced core
  the NEXT light blow-up resolves, not a squeeze datum here). Reduces, no new lemma.
DATUM FIELD (corrected, the certified RouteStep.branch transport field): the LIGHT pullback witness —
node_loss_pivot_factor + node_jacobian_det + the cover fact + (PivotWitness sibling, value). HOLD committing
until crux2 reconciles its veto vs pp2 g188 (controller asked it; veto likely predates g188). Building against
the heavy interface = the wrong-type rework. The combinatorial recipe + value-side are datum-weight-INDEPENDENT
(unchanged); only the transport field corrects heavy→light.

--- SUPERSEDED (g173, the heavy reading — kept for the audit trail) ---
[Was: crux2's veto → R1 node = schur_straighten_squeeze_exists from my hnode (∑Erow²+‖b·Erow+S·Γ‖²); heavy
 IsSchurStraightenSqueeze datum. WRONG: that's L2's gauge node. R1 is the light pivotBlowupOn pullback.
 Mixed-node-reduces (g174) is still RIGHT, but its C1-complement is a LIGHT node, not a heavy-hnode node.]
Per-node recursion (crux2): classify → (main Schur ⟹ hnode ⟹ schur_straighten_squeeze_exists) | (leaf ⟹
dlnLoss_one_layer_deepest) | (mixed ⟹ compose) → rlctAtOn_reduced_transport closes descent → recurse on
S.red (ΣM terminates, my redM_widthSum_lt). INTERFACE CONFIRMED: ChainDimSplit = carrier I populate
(drop=resolved pivot dims, red=M−drop); presentation data in IsSchurStraightenSqueeze (mine), NOT ChainDimSplit.

## MIXED-NODE REDUCES — EXERCISED (g174, pp2 g192/g193) — closes g173's design-only caveat (per-node)
pp2 RAN a genuine partial-drop: M=(3,3,2), T=(2,0) [tt=(3,2,0), genuine t_0=3 > t_1=2 > 0 at s=1]. C5 split:
- SURVIVOR (rows 0,1, rank t_1=2): 4 smooth regular gens = the ∑Erow² block (C2 pass-through).
- COMPLEMENT (row 2, the rank-1 drop 3→2): on {E=0}, P_2=(S·b4,S·b5), S = the per-layer Schur complement
  T−Z(I+X)⁻¹Y (=a8 corner) ⟹ residual ‖S·Γ‖² (Γ=(b4,b5)) = the CLEAN main-Schur hnode (∑Erow²+‖S·Γ‖²,
  G²=‖S·Γ‖²). crux2's schur_straighten_squeeze_exists applies to the complement's C1 (pivot a8).
VERDICT (sent crux2): C5 REDUCES, NO new lemma — EXERCISED on (3,3,2) T=(2,0); complement-C1 = clean hnode.
crux2 HOLDS generalizing. HONEST CAVEAT (pp2, recorded): exercised the MINIMAL single-step partial-drop
(complement rank 1). Multi-partial-drop ((3,3,2,2,2), crux2's depth-6) compose the SAME reduction ITERATIVELY
(each step = C2-survivor ⊕ C1-complement) — NOT run explicitly; iteration = DESIGN, per-node step = EXERCISED.
The per-node reduction (what the existence lemma needs) is exercised; iteration is structural (WF recursion).
pp2 runs (3,3,2,2,2) on the word if multi-step exercise wanted.

FAITHFULNESS CHECK (fm3, g171): the (Mval M T).toNat round-trip needs Mval ≥ 0 — and PivotWitness's `hAdm :
T ∈ Adm M` field GUARANTEES it (Mval_nonneg_adm). So NO gap: my minAdm_le_Mval_toNat uses Int.toNat_le_toNat
(monotone regardless of sign — the ≤ is unconditional); the achiever EQUALITY's faithfulness (= ½·m₀, m₀ =
(inf' Mval).toNat) is correctly located in pp2's reachability cert (g189-verified), discharged when the
dispatcher constructs the achiever's PivotWitness with T=T*, (Mval M T*).toNat = minAdm. foldFamily_achiever's
hypotheses (m₀ ∈ codimsOf i₀, ∀c, m₀≤c) are pure ℕ/List — no Mval-sign dependency. Value-side SOUND as-is.
(RouteMState can't import ResolutionAtlas's Mval_nonneg_adm — forward dep — but doesn't need to: the witness
carries hAdm, and the faithfulness lands at the dispatcher's achiever construction, pp2's lane.)

## VALUE-CONSISTENCY CLOSED + PivotWitness PLACEMENT = SIBLING FIELD (g170, pp2 g186/g187)
pp2 closed value-consistency: the (a)+(b) contract maps 1:1 onto g183 §2/§4, verified all 6 cases incl
(4,3,2) [Mval set {6,8,12} all ≥ m₀=6 — the thin case where codim=Mval not cardinality is load-bearing],
folded into the cert with my foldFamily_* names (origin/g187-foldfamily-value-target @31f00ea). The leaf
monomials agree with my value-side BY CONSTRUCTION; no separate consistency proof. VALUE-CONSISTENCY: DONE.
DESIGN DECISION (fm3, the one open co-design pp2 flagged — where the PivotWitness lives on certified
RouteStep.branch): SIBLING FIELD, NOT folded into the transport datum's center-spec.
  branch carries: ... (transport datum, crux2's lane) + (witness : (c:cells) → PivotWitness M (codim c))
Decisive reason: the fold's C≥ consumes ONLY PivotWitness (foldFamily_threshold_ge_of_pivotWitness takes
no transport datum — pure Adm/Mval), so a sibling field keeps the value half provable WITHOUT unpacking
the analytic transport datum — respects the value/transport lane separation (g169) AND is robust to crux2's
pending transport-field shape (folding it in would re-couple the settled value witness to the pending
transport). Sent pp2 + flagged crux2.

## WAIT-STATE (g166, controller) — set to assemble on crux2's transport-field adjudication
Controller: R1's long-pole has collapsed to the SINGLE transport-field confirm (in flight — do NOT
re-ask crux2). Controller leans the lighter monomial-pullback read (my g164): per-cell consequence =
node_loss_pivot_factor (mine) + rlctAtOn_reduced_transport (crux2 det=1 reindex), NOT the heavy
IsSchurStraightenSqueeze additive datum. On crux2's reply (likely lighter): pin ValidRouteStep → build
the fold → transcribe pp2's recipe. Value-side COMPLETE + fork-independent.
Sent pp2 the full firmed target shape (RouteStep/ChainDimSplit/MonoData types + value-side interface +
paths + firm-vs-moving). pp2's g183 cert already designs against it; the codim field tightens to the
§2-witnessed form, the transport-field flagged crux2-pending.

## PivotWitness BANKED (g167, @040a997) — the §2 certified-codim structure (pp2 co-design target)
The §2 codim-witness, formalized as the concrete dependent structure pp2 verifies against (RouteMState.lean):
  structure PivotWitness (M : Fin (L+1) → ℕ) (c : ℕ) where
    T : Fin L → ℕ ; hAdm : T ∈ Adm M ; hCodim : c = (Mval M T).toNat
Data-carrying (Type, = pp2's {T // …} subtype) so the dispatcher constructs it + downstream reads T. The
certified-RouteStep codim field = (c, PivotWitness M c), NOT a bare ℕ — the (4,3,2) green-≠-right trap
closed by construction. Discharges:
- PivotWitness.minAdm_le : PivotWitness M c ⟹ minAdm ≤ c (clean-three).
- foldFamily_threshold_ge_of_pivotWitness : ∀ leaf codim PivotWitness-certified ⟹ ∀ leaf ≥ ½·minAdm (the
  §2 C≥, fully certified — what pp2 verifies the per-node obligation against).
VALUE-SIDE NOW COMPLETE: C≥ (PivotWitness → foldFamily_threshold_ge_of_pivotWitness) + C=∃ (foldFamily_achiever
← pp2 g147/g148 achiever + §4 reachability) = all the IsResolutionAtlas facts, dischargeable from pp2's
cert, fork-independent. The ONLY remaining field = the per-cell TRANSPORT (crux2 additive-vs-min, in flight).

### DURABLE: the route-checked recursion skeleton (RouteMRecursion.lean, UNCOMMITTED — preserve vs wipe)
The fix-body skeleton (route-checked green, 1 sorry = routeStep). Recorded here for durability (the
worktree-wipe lesson). On top of the committed foundation (chainWidthSum/redM_widthSum_lt/chainRel/
chainRel_wf/redM_chainRel @55db82d). ⚠ UPDATED (g181, NOT re-transcribed below): NodeChartFamily also
carries `nonempty : Nonempty ι`; RouteStep.branch also carries `(cellsNe : Nonempty cells)`; routeAtlas
derives nonempty per arm (leaf→PUnit, branch→⟨⟨c,i⟩⟩); `instance : Nonempty (routeMIota M)`. Also
ReducedTransport (g179) + the witness field (g176). The LIVE file is the source of truth; this block is
the wipe-recovery shape (the Fintype/Σ recursion core), augment with g176/g179/g181 fields on recovery:

    structure NodeChartFamily {L : ℕ} (_M : Fin (L + 1) → ℕ) where
      ι : Type
      fintype : Fintype ι
      data : ι → MonoData

    -- LIGHT-ENRICHED (g176): branch carries the §2 PivotWitness sibling (codim=Mval, value);
    -- the per-cell TRANSPORT is the LIGHT pullback (node_loss_pivot_factor), threaded at cover-fact
    -- level, NOT a heavy IsSchurStraightenSqueeze field here.
    inductive RouteStep {L : ℕ} (M : Fin (L + 1) → ℕ) : Type 1
      | leaf (md : MonoData)
      | branch (cells : Type) (cellsFin : Fintype cells)
          (split : cells → ChainDimSplit M) (codim : cells → ℕ)
          (witness : (c : cells) → PivotWitness M (codim c))

    noncomputable def routeStep {L : ℕ} (M : Fin (L + 1) → ℕ) : RouteStep M := sorry

    noncomputable def routeAtlas : {L : ℕ} → (M : Fin (L + 1) → ℕ) → NodeChartFamily M :=
      fun {L} => WellFounded.fix chainRel_wf fun M rec =>
        match routeStep M with
        | .leaf md => { ι := PUnit, fintype := inferInstance, data := fun _ => md }
        | .branch cells cellsFin split codim _witness =>
            letI : Fintype cells := cellsFin
            let child : (c : cells) → NodeChartFamily (split c).red :=
              fun c => rec (split c).red (split c).redM_chainRel
            { ι := Σ c : cells, (child c).ι
              fintype := by
                classical
                letI : ∀ c : cells, Fintype ((child c).ι) := fun c => (child c).fintype
                infer_instance
              data := fun x => ((child x.1).data x.2).appendDivisor (codim x.1) }

    def routeMIota {L : ℕ} (M : Fin (L + 1) → ℕ) : Type := (routeAtlas M).ι
    noncomputable instance {L : ℕ} (M : Fin (L + 1) → ℕ) : Fintype (routeMIota M) := (routeAtlas M).fintype
    noncomputable def routeD/routeK/routeH M i := ((routeAtlas M).data i).{d,k,h}

(imports: GeneralR1Recursion [ChainDimSplit] + RouteMState [MonoData] + Mathlib.Data.Fintype.Sigma;
open scoped BigOperators; namespace DLNFibre.DLN.RLCT.) routeStep → ValidRouteStep (certified, with
pp2's §2 witness + crux2's transport field) once the transport-field lands.
