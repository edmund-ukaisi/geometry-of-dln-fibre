<!-- COMPASS — the fork-history (WHY + how-we-know). Charter.md is the invariant core (WHAT); read it FIRST.
     Elder is sole author; controller commits. May grow; compacted deliberately. Target ≤2 pages.
     COMPACTED 2026-07-20 (post-checkpoint) to the CURRENT frame: objects A–E, ideal-level.
     The retired chart Engine's internals are HISTORY (journal ticks ≤340, RETIRED.md, git), not truth. -->

# Compass — aoyagi-engine

## The live question (current frame)
Build **Aoyagi's resolution machinery as reusable objects A–E at full generality** (charter §1). The
RLCT LOWER bound is **IDEAL-level** — the chart route is a proven category-dead end (F1). The
destination `aoyagi_learning_coefficient` unconditional is a corollary/test, not the objective.
**The hard part, named and front-and-centre: the COUPLED corank ≥ 2 resolution** (Object B, width ≥ 3) —
the case the chart drifts, the MVP shortcuts, and the per-layer recursion were all routes AROUND, each
failing late. It holds its own lane and is never scoped to a footnote.

## The load-bearing strategic picture — the RLCT lower bound is a three-part ideal composite
1. **RESOLUTION [Object B]** — the blow-up monomialises `⟨∏C⟩ = ⟨diag(b)⟩`; the `b_i` are monomials in
   the exceptional coords. `rlct⟨b_i⟩ = ½·min M_{s,k}` is the min over THESE divisors.
2. **LEMMA 1 — ideal-RLCT domination [Object A, category-NEW, Mathlib-absent]** — `⟨∏C⟩=⟨b_i⟩ ⟹
   Σ(∏C)² ≍ Σb_i²` locally ⟹ integral comparison (worked.tex:153–158). REPLACES the category-wrong
   chart-diagonalisation. The `≤`/`≥` structure is elementary in outline; **the full-generality Lean
   statement (both directions) is the workhorse to build** (do NOT pre-price it "elementary" — see counsel).
3. **DIVISIBILITY-CHAIN NORMAL CROSSING [Object B, established]** — `b_1|b_2|…|b_M` (worked.tex:484) ⟹
   `Σb_i² = dominant²·(unit ≥ 1)` per leaf ⟹ `rlct = ½·min` directly. Claimed toric-trivial (single
   dominant monomial) — VERIFIED only in the clean regime; UNVERIFIED at coupled corank≥2.
Objects C (monomial-ideal ½·min) and D (codim = minAdm = cCodim, θ, perm-inv; banked) feed the read-off.

## Settled forks, WITH WHY
**F1. The chart route is a GOAL-LEVEL category error — why we are ideal-level (SOUND, settled).**
Every `(∏C)ᵢⱼ` is a nonzero poly; any a.e.-injective/det-1 chart has open image; a nonzero poly is ≢0
on a dense open set; exact diagonalisation forces ≡0 (a non-open, det-0 projection). So NO det-1/
a.e.-inj map diagonalises the loss on an open set. Survived long because the gap is det-1 (invisible to
Jacobian + cover); only the value LOWER bound sees it — the value lane + decorrelated pnp caught it, the
order-blind det lane would have shipped green over an unbuildable spine. Witnesses:
`cert-full-value-walk §6` (+6 batteries), `cert-exactly-diagonal-mechanism`, `cert-collection-lemma`.
CONSEQUENCE: the ideal reframe is forced; the chart Engine is RETIRED (charter §3, RETIRED.md).

**F2. `⟨∏C⟩ = ⟨diag(b)⟩` transfers as an IDEAL fact — the salvaged truth (SOUND).** Unimodular Q,P are
ideal-preserving (worked.tex:375–390), a standard fact; so the InvVal3/prefix/b-chain REDUCTION the
chart route computed (Q1-verified end-to-end at 4 M's) is the IDEAL identity, NOT a chart identity — it
transfers to Object B unchanged. (The specific `diag(b)` SHAPE at COUPLED instances is part of the B
frontier, not yet verified — F4.)

**F3. Clean (uncoupled, width ≤ 2) telescopes — VERIFIED; the honest boundary (SOUND, scope-bounded).**
At (2,2,2,2): the per-chart ideal reduction is an EXACT symbolic matrix identity at depth-2 AND depth-3;
`δ=ρ` is DERIVED from the blow-up (mechanism depth-blind); RLCT 3/2 = ½·min. Controller-verified against
the batteries. EVIDENCE HYGIENE (do not inherit the gap): cite the PEEL IDENTITY (exact) + `structure_v2`,
NOT "5 batteries" — `ideal_equality_rigorous.py` exits 0 while PRINTING a superseded free-δ intermediate
(exit-0 ≠ content-true). BOUNDARY: (2,2,2,2) is all-width-≤2, the CLEAN shallowest instance, exercises NO
coupling. "Tractable in general" is EARNED only here; coupled width≥3 is the gate for any tractability
pricing. FIRST LANDING = clean recursion; NEXT PROBE = coupled diag(b) at width≥3 (load-bearing).

**F4. The coupling at corank ≥ 2 is REAL — flatten-style decompositions provably break (SOUND
obstruction; Object-B constraint).** At corank≥2 the carried monomials couple (the `b_i` share divisors
via `b_1|…|b_M`). A per-row-multiplicity FLATTEN — treating each `b_i`'s exponent independently — loses
the shared-divisor structure and returns the WRONG min. Witnessed exactly: `minAdm(3,3,4)=8` is achieved
COUPLED-ONLY (`battery/g-coupled-binding-334.py`; the (3,3,4) coupling = two coupled/equal divisors,
load-bearing); a flatten breaks (`battery/g-delta-flatten.py`). WARNING: any flatten/split of the coupled
ideal is a dead route — Object B must reproduce the coupled diag(b), not decompose it row-wise.

**F5. Aoyagi is the fidelity touchstone; Q2 LOCKED (tick 421).** The coupled resolution is her own
Cases 1&2 (read from the paper images; worked.tex references them): transcribe HER choice + verify her
claimed monomialisation — not our invention. At each route/statement ask "within Aoyagi's scope?" and
cite the page; a deviation is a DOCUMENTED typo-fix, never a silent Lean-convenience.

**F6. The carried invariant `FoldStepInvAt` UNDER-transcribed Aoyagi's induction hypothesis — the
10th+11th catches, ONE re-bake (elder-ruled 2026-07-23; SOUND, paper-first + Codex-decorrelated).**
Her ONE "inductive invariant" display (worked.tex:562–577) held both answers. **SHAPE** (support too
tight): her residual block `D_J` is `(M(S)−J)×(M^(S+1)−J)` — running min governs the row/cleared-prefix
axis, the COLUMN axis is the RAW next-layer width `M^(S+1)`; the Lean `supportAt` capped it at
`widthMinUpto` (docstring :551–555 conflated the blow-up CENTER, correctly capped, with the descended
RESIDUAL support, raw). FIX = `(a)` widen the descended branch to `layerCoords(S+1)`; `J=0`/`blockCoords`
unchanged. **FORM** (initially mis-ruled, then RETRACTED — the instructive arc, §8 of the ruling): the wall seemed
to need a carried field, FIRST ruled a coherent-product factoring conjunct. WRONG — fitted to a BROKEN
def. The 12th catch: `canonNormalizationOf` branch (ii) had the wrong recoord inverse (`A_{S+1}·Q₁⁻¹`,
`+γ`, DOUBLES the uncleared cross-term — the def faithfully rendered a certificate §1 DIRECTION error).
FIX = **R3**, the single-branch sign flip to `A_{S+1}·Q₁` (`−γ`), CANCELS it clean, unipotent (Codex Q1
confirmed the direction vs worked.tex:445 — the certificate's inverse was an old-to-new/new-to-old
confusion). CRISIS BOUNDED: the baked fold is a globally-invertible automorphism, so the RLCT VALUE was
never at risk and the resolution is VALID; only MONOMIALISATION (the `M_{s,k}` reading-off vehicle)
failed — no monument reopening, no operator escalation (both instruments concur). With R3 the residual is
CLEAN = Aoyagi's `[[1,O],[O,D_{J+1}]]` (worked.tex:619-629); the exceptionals live in the EXTERNAL
b-ledger (`foldB`), NOT inside `D_J` (Codex Q2 FACT, "not genuinely ambiguous"; her Case-1(1) `d=u_{s,k}d'`
is TRANSIENT). So the FIELD is RETRACTED entirely (both my additive form and the product form): READING B
(`foldResid` = clean residual, not the b-scaled product); boost-readiness DIRECT from clean `D_J` +
existing `foldB` (partial rows → center coord; complementary rows → reused exceptional from external
`b_i`); the 11th "form too weak" catch DISSOLVES; DEF EDIT 2 UNNEEDED or minimal. R4 (generator transform)
stood down (R3 smaller); pnp's R5 (restate to non-diag block) REJECTED unfaithful (she clears each step,
worked.tex:619-629). The re-bake shrinks to SHAPE-widen + R3. LESSON: the field (mine + the confirming
Codex read) was downstream of the broken def — an analysis fitted to a symptom; the def-fidelity §5 harness
(transcribe the baked def) caught it. Hedge CLOSED —
KILLED-BY-e: a scrambling `e` gives degree-2 in a base-`coreGen` extra coord, so the `∀e` wall is FALSE not
just unprovable ⟹ the `canonFlatten` base pin and the b-chain field are NECESSARY, no escape. `PerLayerDeg1From`
UNTOUCHED; numeric `M_{s,k}` ledger stays in Objects C/D. RETIRED predecessor flags: fix-β (row-cap the fan)
+ fix-γ (recoord-image subspace) — superseded by the INHERENT read-side arm (remnant-row read escapes with
no recoord, any pivot) AND by paper-first (there is no cap to preserve; her `D_J` column IS raw); the
fan/slot-coupling escape-diagnosis (the escape is inherent, not a fan artefact); the pnp-fan live-square
cover sub-question (moot once the support widens regardless — interior pivots monomialise, settled). These
lived in the predecessor's INTERIM cap-escape adjudication (`elder-capescape-interim-adjudication.md`), which
was DELIVERY-LOST (sent 23:05, never reached the controller; recovered verbatim from the wedged seat's
transcript during a liveness poll) and INTERIM by its own terms — its fix-β preference is formally retracted
here. Witnesses: `threads/design-round-2-ruling.md`
(the ruling); `threads/L4-case1-core/{recoord-cap-escape,empirical-invariant-table,invariant-candidates-VS,
capescape-def-confirm,scrambled-e-hedge}-note.md` + `verify/{recoord_cap_escape,empirical_invariant_table,
scrambled_e_hedge}.py` (exit-0); `codex/carried-invariant-fidelity-answer.md` (xhigh, all four sub-claims).
Skeleton anchor: `FoldStepInvAt`/`supportAt`/`Deg1SupportedSlot` (MonumentAtlas:544–595); consumer
`realBranch_boostReady_case11` (Case1Wire:386) becomes PROVABLE. WIDE-witness battery `(2,3,2,2)` — NOT
`(3,3,4)` (not wide on the recoord/col axis).

**F7. The destination = the OBJECTS + `via_engine` as their cite-free corollary; hbox/path-(A) is
aoyagi-FULL's programme, NOT this expedition's (SETTLED by charter §0/§1 + the summit landmark; the
literal-name-clean-three requirement is the OPERATOR's residual, #94).** The navigator's gate-audit found
TWO distinct Lean theorems conflated: **(B)** `aoyagi_learning_coefficient_via_engine` (LearningCoefficient:323)
— THIS expedition's geometric A/B/C/D route, its ONLY sorry `exists_coreResolution` = the cap/KILL/transport/
wall frontiers (= the §1 objects), cite genuinely dodged (cordon CITED-unused); **(A)** the literally-named
`aoyagi_learning_coefficient` (Skeleton:1680) — a DIFFERENT object closing via the #108/RouteMSJMint re-point
+ **hbox** (DecoratedDescent, the `(□)` box-finiteness mountain) + L=1 fold-in. WHY (B) is charter-faithful:
§0 steers by the OBJECTS (the headline is "a corollary and a test, NOT the objective"); §1 says hbox "is its
analytic shadow, **never a separate goal** — it falls out of A+B (or is decided false)." (B)'s frontiers ARE
the objects, so closing them = discharging §1 = this expedition's "done"; (A)'s hbox route is precisely the
analytic-shadow-as-separate-goal the charter forbids as headline-steering drift (§0), so it belongs on
AOYAGI-FULL's board, NOT here. OPERATOR-RESIDUAL (#94, definition-of-done): whether "done" additionally
requires the LITERAL NAME to be the clean-three theorem — resolvable by a CLEAN (hbox-free) re-point of the
literal name through `via_engine`'s geometry (cheap aoyagi-engine bookkeeping, satisfies both the summit
landmark's literal-name node AND objects-first) if one exists; if the only literal-name re-point bundles hbox
(#108/RouteMSJMint), then literal-name-clean-three is aoyagi-full's and this expedition's done = `via_engine`
+ the objects. Elder recommendation to the operator: done = `via_engine` frontiers-land + a clean hbox-free
literal-name re-point if available; hbox/DecoratedDescent NOT required and stays aoyagi-full.

**F8. The coupled resolution is NOT a monument; the lower-bound route is P — SETTLED (pnp #122 +
hcover-probe convergence + elder route-gate, 2026-07-25).** Obstruction hunt empty: resolution existence =
explicit finite blow-ups of smooth centres (NOT Hironaka); the (S,J)-maintenance "wall" = substitution-
encoding artifact, dissolved (b-chain divisibility absorbs the block-elim cross-terms, L-A/L-B/L-C, both
directions); Theorem 4 landed+wired for the core (r=0 all-variables homogeneous); the radial step `Δ=u·D̄` is
a smooth-subspace blow-up not a collapse, does not inherit terminal open-ness. The only destination monument
is the cited `rlct=½codim` — which the build DELETES. WHY route P not V: `exists_coreResolution:311 =
∃ res : Resolution` and the value engine rides the two-sided `Chart.hideal` (`IdealInvariance:447`), so the
build INHABITS `hideal_bwd` (= terminal single-monomial×unit via the retained pivot's leading 1; pnp radial,
coranks 2,3) — it does not dodge it. Route P is faithful (inductive normal crossing flattened as a flat Lean
`Resolution` of leaf charts — a Lean choice, not a math divergence) and subsumes V-upper + ratio-bound-at-depth.
V-lower-lighter = the F1-mirage 3rd cycle (retired, §3). PIVOTAL DE-RISK = the corank-2 two-sided END-TO-END
first-brick gate (render→built); RED-flip → objects-only close. Witnesses: `threads/pnp-coupled/adjudication.md`
(S1-S4 + radial addendum); `next-build-render.md §9` (hcover OBL-1/OBL-2 + route-a); `ideal-route-full-render.md`
(L-A/L-B/L-C + Phase-3a); `IdealInvariance:447`, `ProductResolution:114-116`, `LearningCoefficient:296`.

## Paper-fidelity ledger (documented Aoyagi typos; the mechanism stands)
- **Def-3 broken** (verified typo) — use the geometric `½·min_t Mval(t)`. Witness `battery/g-def3-broken.py`.
- **Lemma 1 direction**: worked.tex:156 prints `≥`; the correct/used direction is `≤` (`rlctAt_mono`) —
  harmless for the equality use.
- **T-profile total-comparability (NEW paper defect, thread-31; Def-3-class).** Aoyagi's claim that the
  carried `T`-profiles are totally comparable is FALSE: at widths (2,2,1,1) the profiles (1,1,1) and
  (2,1,0) are componentwise-incomparable, both with Mval = 1. Codex-found, battery-verified
  (`theory/aoyagi-2023-reproduction/g-monument-mval-instances.py`; controller+elder re-runs green). The
  v4.2 record is structurally immune: `hchain` orders the threshold-side b-monomials (`bexp`), never
  profiles — profiles have NO record field, so the false claim has no formal representation to corrupt.
  The b-chain `b₁|…|b_M` is Aoyagi's own invariant and SURVIVES; only the profile-comparability reading
  dies. Recorded so the monument seat does not transcribe it.
  **CODA (2026-07-21, threads/41 + the chain battery):** the excised display's truth is PER-BRANCH —
  the recursion's exponent accumulation nests same-branch divisors (the b-chain IS the profile
  nesting), so the printed "T ≤ T′ or T ≥ T′" is the per-branch invariant missing its quantifier,
  and ρ = max chain of binding minimisers is its correct form. The GLOBAL reading remains false
  ((2,2,1,1)); the defect entry stands; the coda completes it.
- **Case-2 raw-width vs running-min — CLOSED (thread-31; was UNCERTAIN).** Resolved structurally: the
  ideal-route record carries NO rank-profile label field (only `bexp` + `jac`), the exponent accumulation
  is governed by the RUNNING-MIN, so the p.20 raw-width head-reset label has no representation that could
  corrupt `hlb`/`hattain`; at the witness widths (2,2,3,2) the defect divisor is NON-BINDING. The earlier
  hypothesis that the fork dissolves in the ideal route (no separate T-label) is CONFIRMED. Witnesses:
  `g-monument-mval-instances.py`, `verify-case2-rawwidth-defect.md`,
  `threads/31-monument-construction/certificate.md` §d. Image residual CLOSED (elder pass
  2026-07-21): p.20 confirmed — raw-width head-reset printed, Case-1(2) inherits (p.17); worked.tex (T-E).
- **Realization "profile-set ⊇ Adm" (Engine-tree artifact; surviving kernel banked).** The paper's
  implicit stratum-completeness (the resolution realises every admissible profile) is FALSE for the
  built tree — but this was a property of the Engine's leaf-profile-set, which does NOT exist in the
  ideal route (it reads min over the `b_i` directly). The SURVIVING TRUTH: the min IS achieved
  (`minAdm ∈ P`, proved), so `rlct = ½·minAdm` stands = Object D (`minAdm=cCodim`, banked). Ledger:
  `verify-realization-gap-defect.md`. Not carried as a live constraint; recorded so the truth is not re-derived.

- **Per-step principality — the invariant SPLITS (thread-34; elder delta-ratified 2026-07-21).** The
  sketched per-step `PrincipalInv` (divisibility + Bézout bundled) is statement-FALSE at the root and
  every interior state: with a pending tail (S<L) every quotient vanishes at the deepest point, so a
  Bézout identity forces 0=1 by continuity; principality is BORN terminally (S=L ∧ J≥1). This is the
  paper's own structure (elder image-verified: p.15 inductive statement = the ideal identity WITH the
  pending tail, never principality; principality only at the terminal p.22 display; the pnp's cofactor
  Q̂ = diag(b')·Q₁⁻¹·diag(b')⁻¹ reproduces the printed P of pp.18/21 verbatim). The formal shape:
  per-step `StepInv` (region-quantified, divisibility-only, chain) + terminal `terminal_bezout`;
  `PrincipalInv` assembled terminally at the path fold. Recorded as a fidelity CORRECTION toward the
  paper (elder D4). Witnesses: `threads/34-case1-invariant/` (certificate + 3 batteries, controller
  re-run green); corroboration thread-28 + worked.tex:659.

- **The step map is a BLOCK-CENTER blow-up with spectators — full-ambient was a mis-reification
  (elder comb S1, 2026-07-21).** Aoyagi's interior blow-ups multiply only CENTER coordinates by the
  pivot (Case-1 center = {d-block ∪ u_{s,k}} p.16; Case-2 = the d-block p.19; Jacobian ledger
  u^{|center|−1}, p.15); spectators are untouched, and a shear cannot undo spectator multiplication.
  The reified σ = sh ∘ blowupMap (full-ambient) forced jac+1 = flatDim per step — at (3,3,4) it
  demands 21 where the ledger says {9,8,4}: L8 unsatisfiable, terminal_bezout wedged. MASKED by the
  d=(1,2) landing (center = whole space there — the shallow-instance confound, compass F3, verbatim).
  The original codex leaf-2 spec SAID `centerCoordFam m spectators`; the landed OriginBlowup knowingly
  did the spectator-free case and the omission leaked into the statement shape. Fix: the
  center-parametric `blockBlowupMap` atom (O9) + re-point the three Core Props + L7's cover atom.
- **δ is a STATE property ([J=0]), never a branch property (elder comb S2 + scout-mine certificate
  regression, 2026-07-21).** The paper's Let-blocks (pp.16/17/20) are uniform across 1(1)/1(2)/2: the
  u-factor multiplies the run starting at J+1, so the dominant gains it iff J = 0 — for BOTH Case-1
  children. The reified `if branch then 0 else 1` (installed to satisfy the collapse fix) contradicted
  the paper, the thread-34 certificate (line 16, verbatim δ=[J=0]), and its own docstring — false at
  every interior 1(2)-J≥1 state, weak at (J=0)-1(1). The true branch discriminator is PIVOT-KIND +
  residual re-binding (one center, two chart-pivots — 1(1) at the old u_{s,k}, 1(2) at a fresh
  d-entry). LESSON: fix a collapse by pinning the TRUE law, not A law — an invented discriminator
  passes the collapse test while breaking fidelity.

- **The closing principle of the statement-hardening rounds (elder, 2026-07-21): quantification
  severed from provenance is THE disease.** Every ∀-statement whose intended instances come from the
  fold must either (a) carry provenance that reconstructs the instance (L7's road — FoldProduced with
  the σ/center/pivot spine + the jac ledger-tie), or (b) be edge/reachability-indexed (L3/L4's road —
  the tree's own edges, the fold's own states). These are the only two honest shapes. Every refutation
  of the hardening cycle — the constant family (S3), the Σw² spectator support, the misaligned-spec
  q'-law non-polynomiality, the wrong-pivot atlas — was this one disease. Corollary already observed
  twice: the M'=1 compression discards structure that makes steps true; patching the free-standing
  form re-admits sharper probes — go to the construction, don't patch the universal. ONE data spine
  (EdgeSpec) serves both roads; do not multiply clauses beyond need (the card-tie may be derivable
  from the ledger-tie + squarefree).

- **The per-field severance audit (elder, 2026-07-21, after the (A′) reversal).** hsupp closed the
  center's CONTENT axis (support ⊆ center); its ⊆-monotonicity left the SIZE axis open — an
  over-large center passes ideal-membership while the substitution form over-divides (the d=![1,2,1]
  witness, THE center-size-axis regression). The (A′) ruling's reachability argument audited the PATH
  axis and missed the CENTER FIELD's freedom — the disease's sixth instance, the elder's second
  personal axis-miss. THE PRINCIPLE, now a standing guardrail: **every free field on a quantified
  structure is its own severance axis — the audit is per-field, never per-statement.** The repair:
  hsupp′ = center-EXACT degree-1 (coefficients center-independent, the agreement form) REPLACING
  hsupp; degree-1 re-established per-node inside L5's fold (the re-factoring content, now a stated
  obligation).

## The honest gap — coupled-B, stated plainly (front-and-centre)
- **KNOW:** clean regime exact (F3); `⟨∏C⟩=⟨diag(b)⟩` transfers as an ideal fact (F2); the coupling is
  real and flatten breaks (F4); minAdm = cCodim banked (D); the category error forces the ideal route (F1).
- **LANDED (strike wave 1, sorry-free at tip):** (a) Lemma 1 both directions + weighted forms,
  junk-guarded [A]; (c) the guarded S2 monomial rule — `DivChain` excludes the coupled counterexample
  [C]; the corollary reduction (linear flatten + m.p.-homeo invariance + homogeneous global=local-at-0,
  `GlobalHomog`). D banked earlier.
- **DON'T HAVE (the remaining new math):** (b) the COUPLED diag(b) ATLAS at corank≥2 — B's 4 leaves +
  `exists_coreResolution` (the monument; thread-31 certificate is the playbook); (d) order ρ / zeta-pole
  [E, deferred per §1-E].
- The coupled case is Aoyagi's ACTUAL content and the historical dodge-point. BUILD it; do not route around
  it, do not pre-declare it tractable. This gap is the thing the compaction must keep unmissable.

## The wall decomposition + pricing (elder, 2026-07-24, #73-producer audit) — the coupled monument IS #73

**Pricing verdict: exists_atlasRealizesExponents at coupled corank≥2 is (a) BOOKKEEPING-over-the-cleared-
leaves + the L7 cover-tiling — NOT (b) a further coupled Hironaka construction.** The coupled corank≥2
monument (Object B — the b_i-share-divisors resolution, the wall/case1, boost-split, cap, KILL) lives
ENTIRELY in L5's proof-content = the leaf-invariant = **#73** (the cleared chain: cap+KILL+transport →
per-leaf StepInv → PrincipalInv). Once #73 lands, the per-leaf principal forms are supplied and the atlas
ASSEMBLY is generic (coupled-agnostic): L1 (`principalInv_regionRepresents`) LANDED; L6 (`leafPath_chartGeometry`)
= package each PrincipalInv+RegionRepresents as a certified Chart (bookkeeping; the HARD-LOCK is only the
shrunk-nbhd soundness constraint); L8 (`leafPath_realizesExponents`) = the exponent read-off `jac a+1 ∈ leafOf
divExp` via `FoldProduced`'s provenance (bookkeeping; Object D's cCodim bridge). Evidence: `exists_
atlasRealizesExponents`'s own docstring folds the coupled difficulty into L5 (L3/L4); L7's docstring states
"Nothing about L7 blocks the wall (L4), L3, L5's proof-content, L6, or L8." Paper-first: Aoyagi's coupling is
in the RESOLUTION (Cases 1&2, the regular Q,P, the b-ledger) — the atlas is generic resolution-of-
singularities packaging (charts cover; exponents read off the jacobians; Lemma 4-5 pole-order = read-off).

**THE ONE non-bookkeeping piece: L7 `leafPath_compactCover` (the cover-tiling)** — a combinatorial coverage
computation over the canonical block assignment (`canonCenterOf`/`canonPivotOf` slots), riding
`FoldProduced`/`FoldRealizes` (the built tree), INDEPENDENT of L4/L3/L5. It is DETAIL-AT-SCALE (patient,
decomposable; pnp-fan's fanned-cover cert #11-14 is the mechanism), NOT a coupled monument (no single deep
insight). Coupled just means a BIGGER (fanned) tiling, same kind of argument. Residual: the general-`d` fan
tiling is sorried (pnp-fan has the (2,2,2) instance + mechanism); generalizing is detail-at-scale. So
"#73 lands → the summit is wiring (L1/L6/L8) + the L7 cover-tiling seat" — nearly done, with L7 the one
buildable long-pole, NOT an un-owned coupled frontier.

**b-leaf7 / the L7 cover architecture (CORRECTED by seat-L7cover's (2,2,2) escape — the deferred L7 SPECIFY).**
My earlier "L7 is over the col-pinned row-fan" was WRONG — it conflated the LEDGER-fan (diagonal leaves,
col-pin, carries the leaf-invariant) with the COVER-fan (ALL coordinate charts). The escape: over the LITERAL
col-pinned atlas, `leafPath_compactCover` is FALSE — target `x = ε·e_{(0,0,1)}` (col=1) is uncovered (every
col-pinned chart forces its pivot-slot=0; blow-up is outermost, no repair), and x is ε from 0 so no ρ works.
The FULL-fan `(0,0,1)`-pivot chart (col=1, DROPPED by the col-pin) covers it — the #86(B) COLUMN-ORBIT.
RULING (fork A): L7 = the ABSTRACT full-fan cover (pnp-fan mechanism, pivots over all of S), and the
col-pinned→full-fan BRIDGE = the #86(B) column-orbit σ-transport (the column charts are σ-IMAGES of the
diagonal leaves under the DLN coordinate-permutation gauge — verified a coordinate permutation:
`EndpointNormalization:129`, `FibreChartConjugation.pivotGauge`/`gaugeEquiv`; σ permutes chart domains
cleanly + commutes with the blow-up per #86(B)'s clear-equivariance). So the cover-bridge is DETAIL-AT-SCALE
(a permutation-covers-permuted-directions argument on established gauge machinery), NOT a frontier / NOT a
#87 re-open (the col-pin stays for the LEDGER, never the cover — as #87 flagged). (B) [literal col-pinned
atlas covers] is FALSE-as-stated (the escape); its "column-orbit as real added charts" IS (A)'s σ-transport.
FAN-COMPLETENESS (the 2nd gap): `FoldRealizes` gives only leaf-SURJECTIVITY, but the cover needs every
admissible-pivot branch continue — DERIVABLE from L5's `buildTree` (which enumerates all admissible-pivot
branches by construction), NOT a frontier; expose it (a `FoldRealizes` def-edit, controller single-writer,
or an L5 lemma), don't leave it a bare threaded hypothesis. So L7-cover = full-fan tiling + σ-cover-bridge +
completeness — ALL detail-at-scale; (a)-pricing HOLDS on the cover side (refined: full fan via σ, NOT
col-pinned-leaves). The row-repeat phantoms (§9.11) are a LEDGER-side exclusion, orthogonal to the cover.

**Terminology (pin — two collisions):** (1) "the wall" splits into **the case-1 wall** (L4, #38/#73's
leaf-invariant boost-split — the coupled monument) vs **the atlas monument** (L6/L7/L8, the geometric
assembly — bookkeeping + the L7 tiling). (2) "L5-layer transport" splits into **the INV step-transport**
(P5's `sourceClearedInv_holds` induction step, #73) vs **the σ-chart transport** (#81's canonical→fan
chart-permutation, the genuine-L5 provenance). Use these; do not say "the wall" or "L5 transport" unqualified.

## THE PIVOTAL FORK — RESOLVED: RE-ARCHITECT to the matrix-ideal Schur-clearing (elder Q3, 2026-07-24)

**Ruling: RE-ARCHITECT (the construction swap), CONFIRMED — against the encoding I served for ~29 catches.**
Three decorrelated inputs CONVERGE: (Codex xhigh) LOCAL-MIN 85% — per-step substitution + support-tracking is
NOT forced; A→C→D is a direct composition. (pnp-ideal + controller cross-check, 3 scripts exit 0) the
matrix-ideal Schur-clearing is GENUINELY LIGHTER — the pivot normalizes to a CONSTANT unit ≡1, so Q,P are
unipotent with POLYNOMIAL inverses, ⟨QAP⟩=⟨A⟩ with polynomial cofactors (NO unit inversion, NO degeneration
on the nbhd, corank-2 included), the coupling lives in the RESIDUAL matrix never a support predicate → the
#95 row-repeat bug class HAS NO REPRESENTATIVE. (Elder Q1) the matrix-ideal route was ADOPTED at F1/F2 and
the fold DRIFTED from it; the refuted `SupportedOn` was the post-substitution form, a different object.

**SCOPE (localized, NOT throw-out-the-atlas):** SWAP = L3/L4/L5's `FoldStepInvAt` coordinate-substitution
proof of the per-chart ideal-identity certificate (`hideal_fwd`/`hideal_bwd` = `GermRepresents` both ways)
→ the paper's unimodular Schur-clearing proof (Q,P unipotent, cross-term F₃F₂ ∈ ⟨F₂,F₃⟩ drops in one line,
worked.tex:443-458/:466). KEPT = the `Chart`/`Resolution` framework + the value engine A→(Object B CoV)→C→D
(ideal-level via `wrlctAt`, the Jacobian weight — LANDED, no foundation gap; Object A IS the Chart interface)
+ `buildTree`/provenance + L6 + L7 (the cover, my prior ruling stands — framework) + L8 + L1. RETIRES: the
WALL, the KILL, #95, #98, `couplingClear`, degree-1 exactness — ALL artifacts of the divide-by-pivot
substitution. corank≥2 plausibly DISSOLVES (clear J pivots one at a time, each an identical ideal-preserving
step; the coupling accumulates; no special corank≥2 object, no `2u₀u₂` shear-rescue — that was a symptom of
divide-by-pivot). FIDELITY WIN: the Schur-clearing IS Aoyagi's own route (Cases 1&2, Lemma 2); the fold was
OUR invention — the ~29 catches were the accrued cost of the drift (charter §3 source-fidelity, deepest form).

**CAVEAT DISCHARGED + the remaining gate:** the one risk (clean `RegionRepresents` — cofactors continuous,
unit nonvanishing — on the chart nbhd at the RLCT-relevant points, corank≥2) is what pnp's cofactor-cleanliness
verified. Elder condition on the COMMIT: the controller's gate-2 Lean prototype (a corank-2 minimiser step)
must measure the Lean tax as manageable — the paper's one-line ideal argument + polynomial-cofactor Q,P must
render without a hidden Mathlib ideal-membership tax. Green-enough prototype → commit the swap. This is the
rising-sea move: fill the layer with the RIGHT (her) construction, not grind a local-min on sunk cost.
UPDATE (2026-07-24 checkpoint): rev-render LANDED (4+ rounds) — the SPINE is verified sound+general; the
gate-2 Lean prototype (corank-2 dom-wide `hideal` via L-A/L-B) + the corank≥2 `hcover` probe remain the
pre-commit gate (elder). The Lean tax is un-measured; render-bounded ≠ built.

## THE COUPLED-B BUILD PHASE — PHASE CHECKPOINT (2026-07-24: rev-render landed + scope-correction)
**V-MIRAGE RETRACTED; the committed route is coupled-B, the matrix-ideal Schur-clearing** = Aoyagi's own
Cases-1/2 (S,J) recursion (charter §1-B, §3). Nothing in the fold was REFUTED — the encoding drifted;
SUPERSEDED, kept as history.

**THE RENDER + 4 REV-RENDER ROUNDS: the SPINE is verified, the RENDER IS NOT COMPLETE.** The ideal SPINE
(L-A block-elim ideal identity any corank / L-B (S,J)-maintenance via the b-chain / Thm-4) is VERIFIED
sound+general (rev-render #3 + Codex) — the coupled-corank≥2 MAINTENANCE wall was a substitution-encoding
artifact, DISSOLVED at the math level. The combinatorial value half (hlb+hattain) is PROVED sorry-free
clean-three (controller #print-axioms-verified: `o5_core_realized`/`tStar_realized`/
`clearable_of_minimizer`/`hlb_hattain_of_atlasRealizesExponents`). **The earlier "the only remaining
content is bounded combinatorial reproduce-and-verify" was OVER-CLAIMED (rev-render #1, the 2nd
optimism-on-scope error) — the per-chart ideal identity is NECESSARY-NOT-SUFFICIENT.**

**THE SCOPE-CORRECTION (geo-atlas-wire, controller-verified against the Lean).** `exists_coreResolution:311`
needs `∃ res : Resolution (coreGen d e) 0`; the `Chart` record (`ProductResolution.lean:112-116`) mandates
`hideal_fwd`/`hideal_bwd` — the DOM-WIDE ideal identity. The render's FINAL scope-calibration
(ideal-route-full-render.md) listed the residual as `hg_analytic`/`hg_inj`/`hjac`/`hcover` and OMITTED
`hideal` — conflating "hideal math-verified" with "hideal Lean-inhabited." CORRECTION: the coupled `hideal`
is the DEEP monument, UNBUILT in Lean (still the sorried fold `foldResid_case11`). The box-geometry (L6
Jacobian, L7 cover — MECHANISMS built clean-three only for a SIMPLER single-term-shear object, three seams
to faithful) is NECESSARY-NOT-SUFFICIENT — it does NOT touch the `hideal`. The coupled hardness MIGRATED
from the (dissolved) maintenance wall to L7's coupled `hcover` at corank≥2 — UN-PROBED, the highest residual
risk. So the residual to :311 = coupled `hideal` build (L-A/L-B Schur-clearing, RENDERED, UNBUILT) + the
box-geometry seams + the coupled-`hcover` probe. render-bounded ≠ review-landed ≠ built.

**OPTION (b) — operator-chosen 2026-07-24: build the coupled `hideal` via L-A/L-B, retiring the fold.**
The ELDER GATE before the full build fires: (i) a corank-2 chart's dom-wide `hideal_fwd`/`hideal_bwd` BUILT
in Lean via L-A/L-B (the gate-2 prototype; `Corank2Proto` §4 `Q1_C1_Q2_eq_diag` on
`expedition/aoyagi-engine-PROTO` is a starting brick; cast-tax measured); (ii) a decorrelated corank≥2
`hcover` probe. Green-BOTH → commit the full reproduction; green-one → re-scope. The germ→dom-wide bridge
(pivot≡1 ⟹ unipotent-polynomial `Q`, no rational inverse; L6 render) makes the Lean build a REPRODUCTION
of the (S,J) recursion over `buildTree`, not a port of L-A — "bounded in principle" but LARGE, the
under-priced axis of this expedition.

**THE NEW 3-LEVEL OPERATING MODE (operator, 2026-07-24).** (1) controller owns PROCESS + MATH (the render);
(2) decorrelated ADVISORY math-level seats — a review-only pen-and-paper (rev-render) auditing the render, a
code-frontiers scout, a long-range code-projection scout — propose-never-act; (3) Lean OUTSOURCED to builders
via detailed briefs. PREP phase now (operational center + house-cleaning); the Lean BUILD fires ONLY on the
operator's explicit go. Elder role in the new mode: gate the render/SPEC against the charter (objects A-E;
the bar); author the charter/compass; the stern voice on overclaim (hold "render-bounded" ≠ "review-landed"
≠ "built"). Plan artifact: `execution-plan-coupledB.md` (controller).

## Standing counsel (rising-sea)
- **THE PER-FIELD + BOUNDARY AUDIT (refined 2026-07-21, the layer-axis event):** audit each free
  field AND each field's range boundaries — a field constrained everywhere but at its range's
  endpoint is severed at the endpoint. Axes to date (8): content, size, path, coordinate,
  layer-boundary, plus the three frame/indexing axes closed at the `supportAt` bake — support
  (computed window, not a free ∀-branch), C′ (PINNED = supportAt(child), not ∃), coefficient-clause
  (re-factored, not free). ⚠ COORDINATE is RE-OPENED (L7 `leafPath_compactCover` false-as-stated;
  the `canonCenter` "bridge-free" closure was premature — see overlay/severance-witnesses.md). The
  witness bank (overlay/severance-witnesses.md; register §6) holds one exemplar per axis; every
  fold-sourced ∀-statement re-checks against all eight before its render freezes.
- **BUILD THE RIGHT OBJECT — DO NOT MINIMUM-VIABLE IT (operator, 2026-07-20; the elder's own
  recalibration).** The whole α-chart programme tried to reach the lower bound WITHOUT building the
  ideal machinery Mathlib lacks; the category error is the PROOF a chart cannot dodge it. The elder ALSO
  drifted — characterising the follow-up as "just Lemma 1, toric-trivial, elementary ≥," an unverified
  clean headline of exactly the falsified shape. DURABLE: build the RLCT-ideal-and-resolution library as
  a proper STANDALONE GENERAL library (rlct as ideal/germ invariant; Lemma 1 both directions +
  ideal-inclusion monotonicity; monomial-ideal RLCT / Newton in full generality; the resolution CoV; the
  analytic/zeta foundation for ρ) — to full generality from the START, not a patch to unblock a headline.
  DLN-specific simplifications (toric-triviality, the explicit tree) FALL OUT downstream; scoping the
  object BY them is the error. NEITHER avoid the hard part NOR avoid the large build.
- **KILL-SET ADEQUACY.** Every pre-committed kill set must exercise each KNOWN failure mechanism
  (interior-bottleneck width-drop; L≥4 non-monotone depth). A green pre-committed battery is NEVER
  sufficient for a universal claim — the gate reads a DECORRELATED hunt. Provenance: "clean telescopes"
  ⇏ "coupled tractable" is the shallow-instance confound that has bitten this expedition repeatedly (an
  "== Adm at all 4" kill sat green while false at 84/351 — all 4 instances bottleneck-free).
- **MATHEMATICAL SENSE OVER CASE ANALYSIS (operator).** Understand the mechanism at conceptual altitude
  (iterated blow-ups monomialising the ideal, ONE uniform idea whose "cases" are charts) THEN transcribe;
  build the uniform object and DERIVE the cases. When a case-grind feels authoritative but shapeless, stop.
- **MATHEMATICAL NECESSITY IS THE BAR, not Lean-build progress (operator).** Judge a shape by whether the
  MATH necessitates it; Lean cost is a secondary tiebreaker. When a ruling leads with "zero ripple /
  unblocks the build," STOP and re-derive from the math.
- **DECORRELATED GATES.** In-house nice-instance witnesses MASKED gaps repeatedly (resRank fold; srcBox
  boundedness; the realization gap — caught by pnp's independent scan, not the battery). The GATE reads an
  independent seat, never the builder. An in-file witness is necessary, never sufficient.
- **Survey banked state before commissioning anything** (3 redundant commissions on a prior run). Reuse
  dev's determinantal RESULTS for D; keep the RLCT-ideal work on the DLN side (the cite lives there).

## Landmarks (A–E frame; ≤9 — why these)
*The map's landmark set MIRRORS this section; divergence is a drift item, not a rendering choice.
(Reconciled 2026-07-21 late evening — both prior sets were stale; demotions with surviving homes:
F1 → settled-forks; (2,2,2,2)-clean-telescoping → fork F3; the (3,3,4) anchor → the L4 brief +
traversal table + witness bank; b-leaf2-blowup-atlas → absorbed into the Core-leaves node.)*
- **aoyagi-summit / kill-cite** — the destination as one node: `aoyagi_learning_coefficient`
  cite-free; the summit IS the kill (merged — they were never two things).
- **Object A** (landed) — the ideal-invariance workhorse every transport rides.
- **Object B** (LIVE — the coupled `hideal` monument via L-A/L-B Schur-clearing; the box-geometry is
  necessary-not-sufficient; L7 coupled `hcover` UN-PROBED) — where the expedition is.
- **Object C** (landed) — the guarded boxed rule the wall's output feeds.
- **Object D** (banked) — the divisorMin → qipMin → cCodim bridge.
- **b-value-cov** (landed) — the atlas min-over-charts CoV equality: the engine's analytic heart, O1 closed.
- **corollary-reduction** (landed) — flatten + deepest-point + carrier bridge: the summit's wiring stands ready.
- **Core-leaves banked node** (landed) — terminal_bezout + L1 + the blow-up atoms (absorbs
  b-leaf2-blowup-atlas): the spine's PROVEN end — the wall's output already has its consumer.
- **Object E** (OPEN, scoped) — P6.1 banked; P6.2 = the max-chain identity in statement-shaping.
- **category-no-go (F1)** — why the ideal route; the retired chart Engine's tombstone (RETIRED.md).
- **(2,2,2,2)-clean-telescoping** — the verified clean landing (peel identity + structure_v2).
- **(3,3,4) / (3,3,2,2)** — the coupled frontier probe (minAdm=8 coupled-only).

## History — retired chart Engine (POINTERS ONLY; not truth)
The chart Engine's internal design is JOURNAL/GIT HISTORY — do NOT rebuild against it. Retired as
DEAD-ROUTE ARTIFACTS (chart-atlas constructions with no ideal-frame analogue; their frame-independent
CONTENT lives in A–E, above): `ChartBridge` / `region_glue` (the chart→integral
interface → replaced by A + C + the resolution CoV); `IsFullMonomialization` the PREDICATE
(EngineDefs:268) is ledger-COMBINATORIAL (divExp = Mval of admissible profiles) and is SALVAGED into
the Object-B adapter (mon-rec, elder-ratified, conditions C1/C2) — only its bundle-role inside
`CanonicalResolution`/`ChartBridge` is retired; `terminalExponents` / `divExp` / `divProfile` /
`genDivExp` / `divTilde` (per-node exponent-ledger fields → the `b_i` exponents / min = minAdm, Objects
C/D); the resolution-tree carrier + edge-labelled sharing + `StepRel` / `stepUpdate`; the Q5
banked-RLCT-transport route; the full-mechanism R1–R7 rungs; the coverage theorem + theorem4-localization
+ region-glue division-of-labor; the concrete monomialization oracle; diagonal-normalization; the α-atlas
`LeafPullback` / `geoAtlasNorm`; the two-lane / hbox / mint-PR endgame. See journal ticks ≤340, RETIRED.md.
SALVAGE correct kernel-checked det/tree pieces into Object B by re-importing the specific module, never by
resurrecting a chart hole (charter §3).
