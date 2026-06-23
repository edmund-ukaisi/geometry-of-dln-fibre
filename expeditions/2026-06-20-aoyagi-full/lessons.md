# lessons.md — Aoyagi-Full (append-only methodological learnings)

Seeded from the diagnostic of `expedition/aoyagi-rlct` (the prior, assumed-bad attempt) and the
pen-and-paper rounds that preceded this expedition. Directed-suspicion fuel for `priorities.md`.

## 2026-06-20 — seed lessons (from the diagnostic)

- **Treadmill failure mode (the thing to not repeat).** The prior expedition put ~55% of recent commits
  and +8.7K lines into reconciling a *printed Case-2 typo* with no stated target theorem, so accretion
  had no stop condition; open sub-items grew 7→25+ in a day. Guardrail: the goal skeleton with named
  `sorry`s is the contract; every unit closes a named sorry; sorry-count trends down.

- **The "awkward middle" — where to draw the Cited line.** Proving the blow-up *combinatorics* while
  citing the *extraction* strands the resolution *geometry* in between (neither proved nor cited), and
  that gap is what the bookkeeping was silently assuming. Cite the **extraction** (S2); **prove the
  construction** (R1, real charts). Never an abstract exponent-bookkeeping engine disconnected from the
  geometry.

- **Aoyagi's printed Case-2 vector is λ-safe; the "prefix-minimum correction" is NOT.** The printed
  `t^{(i)}=M^{(i+1)}` telescopes to `M^{(S)}M^{(S+1)}` (a two-width product ≥ 2λ) — always safe. The
  prefix-minimum "fix" the prior expedition built can violate admissibility and produce sub-2λ (even
  negative) values. So: do not reproduce the corrected-vector machinery; the Case-2 vectors never bind
  (proven). If we ever touch the printed vector, the printed reading is the geometrically valid one.

- **Definition 3 (relevant-set selection) may be ill-defined on unbalanced widths.** A finder returned
  no set for `[4,2,1,3]`. Mitigation: define `aoyagiλ` via the always-well-defined minimisation; prove
  the printed Theorem-2 expression equal where Def 3 applies; pin the exact Def-3 regime.

- **Clean closed form beats the printed one for formalisation.** `2λ_core = ½(Σqᵢ²−Σmₖ²)` (q = balanced
  ℓ-split of P) keeps terms small and sidesteps Def 3 in the core. Internal target; prove printed = clean.

- **Page images are necessary when a step depends on `M^{(s)}` vs `M(S)`** — plaintext PDF extraction
  collapses these notations. Record the source-imaged formula before accepting any transition data.
  (Carried from the prior expedition's own lessons; verified relevant.)

- **Build-time anti-pattern: one giant file.** A 13.7K-line module recompiles wholesale on any edit.
  Many small modules + a build-once Foundations layer + background builds.

## 2026-06-20 — statement-fidelity audits must be per-rung and adversarial

The Rung-0c audit (broad: defs, S2-minimality, θ-seam, hygiene) PASSED but MISSED two statement bugs in
the skeleton rungs — caught only by a later controller precision-read of the full `Skeleton.lean`:
- `block_elimination` (L1) was **vacuous**: `∃ invertible P,Q, (P·B·Q).rank = r` is trivially true
  (rank invariant under invertible mult). A non-X=X statement can still be vacuous — "rank preserved"
  reads like content but is a triviality. **Audit test:** for each rung, ask "could this be discharged by
  identity witnesses / an invariant that holds for ALL inputs?".
- `product_reduction` (L2) **over-claimed**: `rlctAt = aoyagiLambda` `∀ wstar ∈ optimalSet` — but the local
  RLCT varies over the fibre (min at the deepest point; that's why D1 exists), so it's false at milder
  points. **Audit test:** for each `∀`-over-a-set conclusion, ask "true on ALL admitted inputs, or only at
  special points?". Tell-tale: if the rung makes a sibling rung (D1) redundant, it's over-claiming.
Takeaway: a green build + a broad audit is necessary, not sufficient; statement-fidelity needs a sharp,
per-rung, adversarial pass (vacuity + over/under-claim + name=content) — now standard for skeleton audits.

## 2026-06-20 — the "deepest point" of a fibre: prefer a CONSTRUCTED point over a ∀-predicate

For the DLN fibre {∏A = B} (rank B = r), the local RLCT is minimized at the "deepest" point. Pinning the
identification (pp + decorrelated Codex, exact-algebra):
- **per-partial-product rank-r is WRONG** (too weak): a layer can be high-rank while the partial products
  stay rank r, giving a milder singularity. Counterexamples both r=0 ((2,2,2): (A¹=0,A² inv)→rlct 2≠3/2)
  and r>0 ((3,3,3) r=1: A¹=diag(1,0,0),A²=diag(1,Q)→9/2≠4).
- **per-layer rank-exactly-r is SUFFICIENT** (⟹ all-partial-rank-r by submultiplicativity; rlct constant
  over it = a single GL gauge orbit) **but NOT EXHAUSTIVE** — the full set attaining λ is larger (residual
  core in the closure of an Aoyagi-minimizing nested-rank stratum; multiple orbits attain λ).
- ⇒ **a ∀-predicate form (even per-layer) under-describes the attaining set.** Use a SINGLE CONSTRUCTED
  `deepestPoint` (block-normal rank-r chain, residual core = 0): D1 `⨅ = rlctAt(deepestPoint)` (Thm-2
  monotonicity), L2 `rlctAt(deepestPoint) = aoyagiLambda`. Lowest proof surface, zero over-claim, no
  gauge/orbit lemma needed. General lesson: when a "the special point(s)" set is subtle/non-unique, key the
  statement to ONE constructed witness, not a ∀-over-the-set predicate.

## 2026-06-20 — R1: don't conflate the codim-minimisation stratification with the chart atlas

The prefix-rank stratification `{rank(∏_{≤j}C)=tⱼ}` computes the RLCT VALUE (codim S(t)=Mval, min over t),
but it is NOT the chart atlas: a determinantal center `{rank≤t}` is singular along `{rank≤t−1}`, so a smooth
log-resolution refines the strata by the FULL interval rank-pattern `r_{ab}=rank(C^a···C^b)` — each
minimizing chart does NOT correspond to a single prefix stratum (charts are strictly finer). So:
- VALUE (`½ min_t Mval`) and ATLAS (explicit normal-crossing charts) are SEPARATE deliverables: pin the
  value via codim (chart-free), build the atlas only to witness the statement's `∃`.
- "each minimizing chart ↔ one prefix stratum" / "R1↔Adm is a chart bijection" are OVER-STRONG; the R1↔Adm
  match is VALUE-level (min-chart-ratio = ½ min Mval). (Caught by decorrelated Codex BEFORE any formalisation
  built on it — corrects design-spec §9.3 + thread-03.)
- Anti-treadmill corollary: Aoyagi's recursive affine blow-ups ARE the tractable Lean atlas, BUT the value
  must come from the codim stratification, not the blow-up bookkeeping — never make the bookkeeping the
  content (that was the prior expedition's treadmill).
- Dead ends recorded: toric/Newton-polytope route (nondegeneracy fails — Codex torus-zero counterexample);
  flag/quiver determinantal resolution (correct but far heavier to formalise than Aoyagi's recursion).
- **Citation discipline reaffirmed:** citing `rlct = codim/2` (R3a, Lehalleur–Rimányi arXiv:2411.19920) was
  rejected — it would cite away THE new content (codim) and breach the Aoyagi-independence constraint. The
  geometric codim must be PROVEN (R3b). A tempting one-line shortcut that violates scope is still out.

## 2026-06-20 — the proof attempt is the ultimate audit (the 7th bug); audit hypothesis-satisfiability

The contract passed a sharp, per-rung, adversarial "bedrock" audit (non-vacuity + over/under-claim +
name=content) AND a re-audit — yet `deepestPoint_exists` (`Nonempty {w // IsDeepLayers H r B w}` under
`hB : B.rank = r` alone) was FALSE, and with it the headline (⨅ over an empty fibre = ⊤ ≠ finite). It was
caught only when fm tried to PROVE it: counterexample H=(3,1,3), r=2, B=diag(1,1,0) — the middle width H 1=1
bottlenecks the product to rank ≤1<2, so the fibre is empty. The audit (and the controller note) had reasoned
"rank B=r ⟹ r≤H s", true only for the OUTER widths (B : Fin(H 0)×Fin(H last)); middle widths are
unconstrained.
- **Audit-discipline addition (now standard):** beyond non-vacuity/over-claim/name=content, check
  hypothesis SATISFIABILITY + conclusion-reachability. For an existence/`Nonempty S` rung, CONSTRUCT or
  REFUTE a witness under the stated hyps — a `Nonempty S` where S can be empty is FALSE, not vacuous.
- **Build-to-bedrock corollary:** a green build defeats technical slop and a sharp audit defeats much
  conceptual slop, but the PROOF ATTEMPT is the ultimate audit — it surfaces false statements review misses.
  Statement-fidelity audits are necessary, not sufficient; do not over-trust "bedrock" before the proof runs.
- **Heed the decorrelated flag (the sharpest part of this post-mortem).** Decorrelated Codex had FLAGGED this
  exact gap in the bedrock consult (its Q3: "under-hypothesized unless r≤H s for all layers") — and rv-2
  OVERRODE it with the wrong bottleneck argument. The decorrelation WORKED; the failure was dismissing it.
  STANDING RULE: when a decorrelated check (Codex or a teammate) flags a hypothesis/soundness gap, CONSTRUCT
  or REFUTE the witness before dismissing — never override a flag with an unverified argument. (Binds the
  controller too — neither rv-2 nor I caught it independently; only fm's proof attempt forced it.)
- **Fix:** `hr : ∀ s, r ≤ H s` is the right WHOLE-theorem hypothesis (also the well-definedness domain of
  `aoyagiLambda`, since M⁽ˢ⁾=H⁽ˢ⁾−r). Threaded through the headline + deepestPoint chain.

## 2026-06-20 — calibrate "verified compiles": full-body vs type-level/partial

pp self-corrected (unprompted) an earlier "the ~30-50 line assembly compiles" — it had verified the
type-level chain + the individual MP lemmas applying, but the composed MP body was still `sorry`'d; fm-2's
"reindex friction" was the real, under-stated gap. pp then actually compiled the full body (EXIT=0).
- **Lesson:** "verified it compiles" can mean type-checks / individual-lemmas / full-body-green — confirm
  WHICH. A measure-/proof-body that is `sorry`'d type-checks but is not done. Discount remembered "compiles"
  to the artifact actually built.
- The unprompted self-correction is the disposition working — reward it; it keeps the design honest.

## 2026-06-20 — weak existential statements: provable by free choice ≠ the intended result

A1 `lambdaCore_eq_clean` was `∃ ℓ m, lambdaCore M = cleanCore ℓ m`. fm closed it by FREE CHOICE (ℓ=1,
m=![1,(min Mval).toNat], needing only min≥0). It type-checks green but proves almost nothing: the existential
does not bind (ℓ,m) to M, so it does NOT capture Aoyagi Lemma 3 (`lambdaCore` = the clean closed form at the
Def-3 widths). "Fully full" demands the genuine result, so the STATEMENT must be strengthened to bind the
witnesses to the data (m to M's Def-3 selection), turning it into the real minimisation proof.
- **Audit test (extends the satisfiability check):** for any `∃ x, P(M, x)` rung, ask "can x be chosen
  FREELY of M?" If yes, the statement is weak/vacuous — it must bind x to M to carry content. A green proof
  of a free-choice existential is the visible-progress trap (a checkmark proving nothing).
- Dual of the deepestPoint bug: there the existential was FALSE (unsatisfiable); here TRUE-but-vacuous
  (over-satisfiable). Both are statement-fidelity holes a green build hides.
- Pattern across this contract: L1 (vacuous rank), L2 (over-claim), deepestPoint (false), lambdaCore (weak
  existential), A2 (weak existential, known seam). **Statement design is where the bedrock work is** — the
  proofs, once the statement is right, are labour.

## 2026-06-20 — domain under-specification: check the DEGENERATE CORNERS

Two contract statements were FALSE not from vacuity but from MISSING DOMAIN HYPOTHESES, found one-at-a-time by
proof attempts:
- **7th:** deepestPoint_exists/headline false when r > a MIDDLE width (`rank B = r` bounds only the OUTER
  widths) → needs `hr : ∀ s, r ≤ H s`.
- **9th:** deepestPoint_exists/headline false for **L=0** (empty product = identity ⟹ fibre needs B=I;
  `L=0, H=![2], r=0` has hr ✓ but empty fibre) → needs `hL : 1 ≤ L` (L=0 = no network = out-of-model).
Both are DEGENERATE CORNERS (empty index type `Fin 0`; rank-vs-width extremes) the `∀`/headline silently
admitted. **Audit-discipline addition:** for every quantified statement, enumerate the degenerate corners —
empty index types (L=0, `Fin 0`), zero/extremal ranks, single/zero widths — and check it is TRUE or EXCLUDED
by a hypothesis there. Domain hypotheses are easy to under-specify; degenerate corners are where
false-on-the-boundary hides. Commissioned a systematic domain-corner SWEEP (rv-2) to catch the class
wholesale, mirroring the weak-existential sweep. Healthy, not alarming: STATEMENT-domain holes caught before
proofs build on them — again, statement design is where the bedrock work is.
- **The discriminator (rv-2, reusable):** `∃ x, LHS(data) = f(x)` is WEAK iff `f`'s range free-covers the
  LHS via a witness `x` choosable FREE of the data — i.e. the LHS is a CONCRETE value the witness reads off
  (A1: `lambdaCore M` is a computable ℚ, so pick `n = 2·lambdaCore M`). GENUINE iff the LHS is PINNED/OPAQUE
  so the witness must ENCODE the data (R1: `rlctAt(dlnLoss)` is an opaque `sSup` with no statement-level
  value — same `∃ d k h` shape as A1 but you CAN'T pick the exponents without the resolution lemma, so it's
  genuine). Opaque-vs-concrete LHS is the whole difference. Sweep run on the full contract: only A1 + A2 weak.

## 2026-06-20 — full-trunk build catches what module builds hide (orphans + FQN collisions)

`lake build DLNFibre.DLN.RLCT.<M>` builds only M's closure; the default `lake build DLNFibre` builds only the
root `DLNFibre.lean` import closure. A NEW Foundations proof-module not yet imported anywhere (e.g.
`S1Transport`, in the proof-module pattern) is ORPHANED — BOTH builds skip it, so a regression/sorry there
passes CI silently; only `scripts/sorries` (globs all files) sees it (hence a sorry-count higher than the
root build actually compiles). And a proof-module lemma sharing the contract decl's FULLY-QUALIFIED name is a
latent duplicate-declaration landmine that bites at wire-in (when both come into scope). FIX (proof-module
pattern refinements): (a) proof-module lemmas get DISTINCT names (`_aux`/`_impl`); wire = `Skeleton.<rung> :=
<rung>_aux …`. (b) wire the module into the root closure (Skeleton imports it) to be CI-covered; gate WIP via
explicit module-builds until then. (c) run the FULL-trunk `lake build DLNFibre` (not module-scoped) at
integration — it's the gate that surfaces orphans + collisions a module build can't. (Caught by rv-2's
full-trunk green-gate during an idle window — the right use of idle reviewer time.)

## 2026-06-20 — analytic-IMPLICATION gaps: the hyps don't imply the conclusion (10th issue, S1.1)

S1.1 `weightedThreshold_transport` had been statement-audited AND measure-pinned (IsAddHaarMeasure, from the
original bedrock pass) AND domain-corner-swept — yet the bare equality was still FALSE: the stated hypotheses
(proper π, inj/diff OFF a null E) do NOT IMPLY the conclusion. Two gaps, surfaced only when fm-2 tried to
PROVE the reverse `≥`: (1) surjectivity (w*∉range π ⟹ RHS=⊤); (2) Luzin-N (off-E differentiability doesn't
make π(E) null — a Cantor-staircase π is the counterexample; needs `volume (π''E)=0` stated). The Skeleton
DOCSTRING had ASSUMED "π(E) null via Luzin-N" — but a docstring assumption is NOT a stated hypothesis, and the
hyps didn't encode it.
- **New gap-class (distinct from vacuity + domain-corner):** the statement's HYPOTHESES are too weak to IMPLY
  its conclusion (a soundness gap), even when non-vacuous, domain-complete, and measure-pinned. Neither the
  weak-existential sweep nor the domain-corner sweep targets this — **only the proof attempt surfaces it.**
  Reinforces (yet again): the proof attempt is the ultimate audit; a green-statement build + every
  statement-level sweep is necessary, not sufficient.
- **Docstring assumptions ≠ stated hypotheses.** If a proof leg relies on "X holds here" (e.g. Luzin-N), X
  must be a HYPOTHESIS, not a docstring aside — else the statement is false and the proof can't close.
- **Right handling (fm-2, exemplary):** ESCALATE the contract finding (don't silently strengthen hyps);
  deliver the honest UNCONDITIONAL direction (`≤`) + the full result under the SUFFICIENT added hyps; let the
  controller adjudicate the statement change (decorrelated-confirmed, 7th/9th protocol). The added hyps were
  LOCALIZED (S1.1 only; consumers supply them at use-sites where they hold), so the contract change was small.
- **RECURRING across the analytic rungs** (confirmed): S1.1 needed hsurj+hImE (surjectivity + Luzin-N);
  S1.3 `rlct_unit_invariant` (11th issue) needs `Measurable u` (non-measurable u → u·F non-measurable → not
  Integrable → rlctAt=sSup∅=0). The bare statements of analytic rungs SYSTEMATICALLY omit the
  measurability/properness/surjectivity side-conditions the proof needs — EXPECT a hyp-gap in every analytic
  rung; the formaliser checks hypothesis-sufficiency + escalates (don't silently strengthen). S1.4
  `rlct_germ_local` was the exception (bare statement sound). The fixes are always LOCALIZED + use-site-
  satisfiable (the resolution data is proper/surjective/analytic/measurable) — small contract changes, big
  fidelity gain.
- **WHY it recurs — the universal lever (rv-2):** the RLCT is defined as `sSup` over the *integrable*
  exponents, so EVERY transport/additivity lemma silently requires (i) the transformed integrand be
  (a.e.-)MEASURABLE — `Integrable ⟹ AEStronglyMeasurable`, so a non-measurable transform ⟹ admissible set
  `{0}` ⟹ `rlctAt=0`; and (ii) the integrand be NON-TRIVIAL near the point — `≡0 ⟹ rlctAt=⊤` (the 0^neg=0
  convention). Those two facts are the levers behind the 10th (Luzin-N/surjectivity), 11th (Measurable u),
  and 12th (Measurable G + G≢0) findings. PREDICTION (use it): every future analytic rung (R1's per-chart
  transport, L2's Fubini lemma, D1's monotonicity) will need measurability + non-triviality of its
  transformed integrand stated — check it at statement-design time, not just at proof time.
- **12th resolution (S1.5, pp+Codex):** when the bare additivity is false AND heavy (Laplace) AND uncitable,
  the fix can be a STATEMENT PIVOT, not a hyp-add: restate to the smooth-block FUBINI lemma (`rlctAt(Σxᵢ² +
  monomial-core) = n/2 + min ratio`), proven by the explicit radial integral `∫(|x|²+s)^{-c}=C·s^{n/2-c}` +
  Fubini — light, one-citation-clean, and the chart-form (core=monomial, nonzero-a.e.+measurable) dodges both
  levers by construction. Lesson: pick the statement the proof can actually reach cheaply, matched to the
  use-site (per-chart in R1), rather than the most general abstract form.

## 2026-06-20 — RLCT lower bound needs MULTIPLICITY control, not codimension (R1, pre-execution catch)

The RLCT-from-resolution UPPER bound (`rlctAt ≤ ½ min codim`) comes from one chart (the binding divisor on
the min stratum) — cheap. The LOWER bound (`≥`) is where the work concentrates, and the tempting "every
divisor ratio = ½·codim" shortcut is FALSE: the divisor ratio is `(h_E+1)/(2k_E)` and depends on F's VANISHING
ORDER k_E, NOT the center's codim. Two decorrelated counterexamples: `rlctAt(x^{2k}) = 1/(2k) < ½·codim=1/2`;
`(x²+y²)²` (sum of squares, Z={0} codim 2) has `rlctAt=1/2 ≠ ½·codim=1` (squaring doubles the order). So the
real lower-bound obligation is **multiplicity control** — prove `h_E+1 ≥ k_E·(min codim)` for EVERY divisor of
a COMPLETE resolution. For a regular-sequence center (multiplicity 1 ⟹ k_E=1) it reduces to `½·codim`, but
that must be PROVEN per-divisor, not shortcut. Plus the cover/exhaustiveness (the resolution must be complete —
an incomplete chart family overestimates the RLCT by missing a worse divisor). Lesson: for any "RLCT =
½·codim"-style claim, the codim gives the UPPER bound cheaply; the LOWER bound needs vanishing-order
(multiplicity) control over a complete resolution — never shortcut the lower bound from codim. (Caught by pp +
Codex BEFORE R1 execution — the same "surface it early" discipline as the additivity finding.)

## 2026-06-21 — a combinatorial RULE survives many wrong guesses; only EXHAUSTIVE check certifies it (#19 route)

The #19 lower-bound minimiser characterisation went through THREE successive "obvious" rules, each refuted by a
small explicit witness, before the correct one: (1) the per-c / `min_c` reading (cleanCore monotone in widths)
— FALSE (`[1,2,4]` vs `[1,2,7]`: 2 vs −2); (2) route-B's "per-c lower bound" restatement — FALSE (`M=[1,1,4]`);
(3) Codex's "single-c achiever rule `aᵢ ≤ ⌈Sᵢ/i⌉`" — FALSE (278/3900 fail). The CORRECT rule is the CUMULATIVE
predicate: `c* = largest c with ∀1≤i≤c, aᵢ ≤ ⌈Sᵢ/i⌉` on sorted M (0 failures, exhaustive widths 0..3 L≤4 +
3900/3900 widths 1..5). LESSON: for a combinatorial selection rule feeding a Lean lower bound, neither a clean
derivation sketch nor a decorrelated-Codex proposal is evidence — only an EXHAUSTIVE small-case sweep is. Run
the sweep BEFORE committing the route to a formalisation thread; a plausible-but-false rule costs a whole
bounded thread. (The discriminator that finally held was found by brute enumeration, not by argument.)

## 2026-06-21 — call "dedicated multi-session lift" honestly; don't shave a keystone into bounded threads forever

#19's keystone proper (~250-350 lines: per-T lower bound via descent-set DEPENDENT-Fin reparametrisation +
achiever construction + Adm-membership) resisted being landed in any bounded sub-thread — three threads each
banked a reusable engine (`balancedSplit_min`, `cleanCore_perm`, the corrected route) but correctly STOPPED
short of the reparametrisation bulk rather than thrash. The genuine hard core is the dependent-Fin descent
reindexing (the minimiser's breakpoint widths coincide with `sortedSmallest` only AT `c*`, so the
"perm-invariance wall" persists at the min level). DECISION: when an OFF-critical-path result is genuinely a
dedicated multi-session lift, ROADMAP it (statement + engines + corrected route all banked = well-set-up for a
later dedicated tide) and PIVOT the formaliser to the critical path — do NOT keep peeling bounded sub-threads
off an off-path keystone while the headline path has open rungs. The bedrock "Just Do It if within reach, else
roadmap it" applies at the THREAD-budget granularity: "within reach" means a bounded thread, not an unbounded
sequence of them.

## 2026-06-21 — when a sub-fact turns out heavy AND it's the cited axiom's domain, RELOCATE it via an abstract hypothesis (Fubini shift)

The S1.5 Fubini lemma needed the core's divergence-above-threshold for its ≤ direction. First plan: prove the
monomial divergence `∫_box ∏|y_j|^{a_j} = ⊤` standalone (~30 LoC, "elementary"). Building it, fm-2 found it is
NOT elementary — Mathlib's pi-product factorization (`integral_fintype_prod_volume_eq_prod`) covers only the
FINITE/integrable case, not a lintegral=⊤ divergence; the divergent case needs a custom pi-Tonelli (heavy). The
two obvious exits were both bad: build it (heavy, and it re-proves what S2 already gives) or import S2 into the
otherwise-axiom-clean analytic module (pollutes the axiom audit). THE FIX: state the lemma ABSTRACTLY as the
general shift theorem `rlctAt(Σxᵢ² + core) = n/2 + rlctAt(core)`, taking the core's threshold/divergence as
EXPLICIT hypotheses, and DISCHARGE those at the use-site (R1) where the core is a resolved monomial and its RLCT
is exactly S2's domain. This (a) keeps the analytic module axiom-clean + monomial-machinery-free, (b) lands the
one cited axiom (S2) precisely where it belongs, (c) yields a MORE GENERAL, reusable theorem. LESSON: when a
required sub-fact is both heavier than expected AND squarely inside the one thing you're allowed to cite, don't
re-prove it and don't import the axiom into the clean module — abstract the general statement, take the sub-fact
as a hypothesis, and discharge it at the use-site from the citation. The hygiene must stay EXPLICIT (hypotheses,
not implicit assumptions) to avoid the measurability/non-triviality levers — but explicit hyps discharged
downstream are honest, not hand-waving. (Symmetry check: the ≥ direction already took core-integrability as a
hypothesis, so the abstract ≤ form is the dual — a sign the abstraction is the natural one.)

## 2026-06-21 — a "known-false placeholder with a docstring caveat" is still a landmine: restate the SIGNATURE (13th finding)

The 12th finding established that the bare disjoint-block additivity is FALSE and must be restated to the Fubini
shift lemma. That was DOCUMENTED — but the Skeleton statement `rlct_additive_smooth_block` was left with the
bare (false) signature and a docstring saying "the bare-measurable general form is FALSE." fm-2, building the
proof, hit the contradiction: the SIGNATURE is the false form the docstring disavows. The bare statement is
Lean-provable-FALSE from an existing substrate lemma (`rlctAtOn_zero_eq_top`): instantiate G≡0 ⟹ RHS=n/2+⊤=⊤,
LHS=n/2. LESSON: a caveat that CONTRADICTS the signature it annotates is worse than no caveat — it signals the
fix was deferred, and a `sorry` on a false statement is a landmine (anyone who later proves it has proven
nonsense, or more likely wastes a thread discovering it can't be proven). When a finding says "restate X,"
restate the SIGNATURE in the same pass, not just the docstring; if the proof isn't ready, the corrected signature
+ sorry is the honest interim, never the false signature + caveat. (CLAUDE.md "caveats live next to claims" has a
corollary: a caveat may NARROW or CONDITION a claim, never CONTRADICT it — if it contradicts, the claim is wrong,
fix the claim.)

## 2026-06-21 — don't assume two hygiene conditions are equivalent; find the separating witness (hGfin vs hHne)

Pinning the 13th-finding fix, fm-2 proposed `hGfin : rlctAtOn(G²) y0 < ⊤` and asserted it "≡ G²≠0 a.e. near y0"
(= hHne, what the proof engine carries). They are NOT equivalent: G²≡1 (nonvanishing constant) has rlctAtOn=⊤
(everything integrable on a bounded nbhd) yet is ≠0 a.e. — so hHne holds but hGfin fails. Consequences: (a)
hGfin OVER-excludes — it drops the true `rlctAt(G²)=⊤` cases where the equality holds vacuously (⊤=⊤); (b) hGfin
isn't even what the cusp/integrability proofs use (they need a.e.-nonvanishing for the H=0 corner, not
finiteness). LESSON: before adopting a hypothesis "equivalent to" the one your proof needs, find the separating
witness in BOTH directions — a one-line example (G²=1) settles it. The right contract hypothesis is the WEAKEST
that (i) makes the statement true, (ii) the proof literally uses, (iii) the use-site supplies — here hHne, which
R1's monomial core (≠0 a.e.) supplies, and under which even the ⊤-cases stay true.

UPDATE (sharper): hGfin is not merely over-strict — it is UNSOUND as the contract hypothesis. Witness
G(y)=y·[y>0], G²=y²·[y>0], y0=0, n=1: rlctAtOn(G²)(0)=1/2<⊤ (hGfin HOLDS) but the shift equality is FALSE —
LHS rlctAtOn(x²+G²)(0,0)=1/2 (the y≤0 slice is pure x², and ∫(x²)^{-c} diverges for c≥1/2, CAPPING the joint
admissible set), while RHS = 1/2+1/2 = 1. So hGfin admits a false instance; only hHne (which kills the
positive-measure zero-set that drives the cap) is sound. META-LESSON: the proof author proposed the plausible
hypothesis and asserted equivalence; the decorrelated controller check (construct the witness, both directions)
caught that it was unsound. This is the "heed the decorrelated flag — build the witness before dismissing"
discipline applied to a HYPOTHESIS proposal, not just a claim: a hypothesis is a claim too (it claims "this
suffices / is necessary"), and gets the same witness-or-it-isn't-true treatment.

## 2026-06-21 — an ORPHANED rung can harbor a false statement; the validate-small case must EXERCISE the feature (14th finding)

Designing R1.1, pp found `resolution_charts` was both (a) ORPHANED — `product_reduction` (the rung that needs the
resolution) never calls it, so nothing forced its statement to be right — and (b) FALSE for r>0: it stated the
full-loss RLCT = ⨅ monomialThreshold (a MIN), but the full-loss RLCT at the deepest point = n/2 + ½·min Mval (a
SUM — the regular n/2 directions ADD to the RLCT via the Fubini shift, they are NOT a min-direction). Two
compounding lessons:
1. **An orphaned rung (consumed by nothing) is unchecked by construction** — the build is green and no downstream
   proof forces it to be true, so a false statement hides indefinitely. Grep every rung for its CONSUMERS; a rung
   the headline never reaches is either dead or a landmine. (Here it would have been catastrophic: R1, the
   mountain, was about to be built proving a statement the headline doesn't use — proven-but-unplugged.)
2. **The validate-small case must EXERCISE the feature under test.** The (1,1,1) end-to-end gate passed because it
   has r=0 ⟹ n=0 ⟹ the regular block is EMPTY ⟹ the SUM degenerates to the MIN, so the min-vs-sum error is
   invisible there. A degenerate small case gives false confidence. Pick the smallest case where the feature is
   NON-degenerate (here, r>0 / n>0, e.g. (2,1,2)) — or know explicitly which features your small case does NOT
   exercise.
3. **Structural corollary (reusable architecture):** the regular (smooth-quadratic) directions ADD to the RLCT
   (the Fubini shift theorem: rlctAt(Σx²+core) = n/2 + rlctAt(core)); they never participate in the min-over-charts.
   So any "RLCT = ⨅ over charts" statement must be about the CORE (singular part) alone; the regular n/2 lives in a
   separate additive step. Keep resolution (min over charts) and the regular block (additive Fubini) in separate
   rungs — conflating them produces a min=sum type error.

## 2026-06-21 — route-before-lines paid off: the product-structure concern KILLED the cheap route; and a fork can have a third answer (R1.2 verdict)

The controller flagged a concern in the cheap R1 route (B: "iterated-L1 exposes the core as a regular sequence of
coordinates") — that the core ‖∏C‖² is a PRODUCT, so naively not linear coordinates — and gated the build on pp
validating it (decorrelated, witness-or-refute). The verdict (pp + Codex, independently identical, with witnesses):
route B is FALSE. THE DECIDER: a residual product of length q≥2 has ordinary vanishing order 2q, and regular
coordinate changes PRESERVE ordinary order, so L1-alone can never reach the order-2 of a smooth coordinate-square
block. Witnesses: (1,2,1) F=(a₁b₁+a₂b₂)² (singular quadratic cone), (2,2,2) F=‖AB‖² (ord 4, Hessian zero, needs a
genuine blow-up). Lessons:
1. **The route-before-lines gate is worth the round-trip.** Had fm built the (B) general path, it would have hit
   the order-2q wall after sinking ~150-250 lines. The concern → decorrelated validation → refutation cost two
   messages and zero Lean. ALWAYS validate the load-bearing route claim (with a witness, decorrelated) before the
   formaliser commits lines — especially when a cheap route seems "too good" (here: "R1 is trivially light").
2. **A route fork is not necessarily binary.** The controller framed it as (B) L1-light vs (A) abstract-blow-up-infra
   mountain. The validated answer was a THIRD option: (A)-CONCRETE — explicit polynomial blow-up charts (vanishing
   Jacobian on the exceptional locus), carried by the existing S1.1 change-of-variables (whose hsurj+hImE hyps, added
   for the 10th finding, are EXACTLY for a blow-up's non-injectivity + null exceptional image). Neither cheap-but-false
   nor needs-new-infra. When validating a fork, ask "is there a middle route?" — don't accept the binary.
3. **The controller's own reconciliation can be wrong — let the decorrelated check correct it.** The controller had
   written "if (B) holds, multiplicity-control is vacuous + R1 is light." (B) was refuted, so that's dead; the bank
   was corrected. Bank conclusions as provisional until the validation lands; don't let an elegant-but-unverified
   reconciliation harden into a planning assumption.

## 2026-06-21 — a tractability win on one piece is not a win on the whole; pressure-test the residual (R1.6)

Designing the general R1 atlas, pp found R1.3 (the codimension piece, feared as the heavy "determinantal-codim,
Mathlib-lacking" mountain) is actually a LIGHT ℕ count identity (∑ residual block sizes = Mval) — a real win, the
Mathlib gap dissolved. Then pp started writing "R1 is medium" — and CAUGHT ITSELF, pressure-tested R1.6 (the
cover), and corrected: R1.6 (general-M cover) is the genuine mountain, because the headline EQUALITY needs the
LOWER bound, the lower bound needs a COMPLETE resolution (no missed worse divisor), the codim-shortcut for the
lower bound is FALSE (the route-B witnesses x^{2k}/(x²+y²)²), and D1 (inf over the fibre) does not give the
per-point lower bound. LESSON: when one feared sub-piece turns out easy, that's exactly the moment the
"visible-progress / confident-headline" instinct fires ("R1 is medium now!") — resist it by pressure-testing the
OTHER pieces before re-headlining the whole. A win on the piece you feared most does not relocate the difficulty to
zero; it relocates it to wherever you weren't looking. (pp did this unprompted — the self-correction IS the
standard; the controller reinforces it.) Naming corollary: "R1 is medium" was the over-claim; "R1.3 light, R1.6 the
mountain" is the accurate map — name the difficulty where it actually is.

## 2026-06-21 — a shortcut whose ANSWER matches is a cross-check, not a proof path (the Q4-lct trap)

Settling R1's lower bound, decorrelated Codex offered a shortcut: `rlct(F) = ½·lct(I)` with `lct(I) = min_Adm Mval`
via quiver multiplier ideals — sidestepping the whole flag-resolution. Its ANSWER matched the target. pp rejected
it as a proof path, for three reasons, and kept it only as a cross-check: (1) it rests on an UNPROVEN coincidence
(real rlct = ½·complex lct — not generally true; needs proving for this family); (2) it introduces a SECOND
citation beyond S2 AND breaks the Aoyagi-independence constraint (it's the Lehalleur–Rimányi/determinantal-
multiplier-ideal literature); (3) it BLACK-BOXES the very content the rung exists to prove. LESSON: when a tool
hands you a shortcut whose output equals what you're trying to prove, that is evidence the TARGET is right
(valuable — take the confidence), not evidence the shortcut is a valid PROOF. Before adopting it, check: does it
rely on an unproven bridge? does it import a citation/dependency you've committed to avoid? does it assume the
thing you're trying to establish? If any — it's a cross-check, not a path. (This is the dual of "build the witness
before dismissing": here, don't ADOPT a confirmation just because the number matches.)

## 2026-06-21 — ℝ≥0∞ gotcha: "product finite ⟺ both factors finite" is FALSE (0·∞=0) — record the positivity (2,1,2)

Designing the (2,1,2) product-MIN lemma (`rlctAt(G·H) = min(rlctAt G, rlctAt H)` for G,H≥0 on disjoint vars, via
Tonelli split of `∫⁻(GH)^{-c}`), pp caught a silent hole: in ℝ≥0∞, `a·b < ⊤ ⟺ a<⊤ ∧ b<⊤` is FALSE — if one
factor is 0 and the other ⊤, the product is 0·∞ = 0 < ⊤. So "the joint integral is finite iff both block
integrals are finite" needs the extra fact that neither block integral is 0. It doesn't bite here (each
`∫⁻_U G^{-c} ≥ μ(U ∩ {G≤1}) > 0`, strictly positive because G≥0 vanishes only at 0), but the lemma's hypothesis
must RECORD that positivity rather than rely on the false equivalence. LESSON: any ℝ≥0∞ argument that factors a
finiteness/admissibility condition through a PRODUCT must rule out the 0·∞ corner explicitly — the convention
makes `0·∞=0`, so a "both-finite" inference silently assumes both factors are nonzero. (Surfaced on the concrete
(2,1,2) case before it could hide in the general product-MIN lemma — validate-small-first again.)

## 2026-06-21 — residual-smooth-block entanglement is real but lands on UNIT termini (harmless) — the A-vs-B call

Adjudicating how to handle residual smooth blocks in the resolution (Option A: monomialize the block, extra
blow-up layer, uniform monomial leaves, RHS stays `⨅ monomialThreshold`; Option B: handle the leaf
`monomial × Σy²` directly via `smoothBlockND_rlct` + Fubini-product-MIN, no extra layer, heterogeneous leaves).
Decorrelated Codex flagged (FACT) that the Fubini split `rlct(monomial × Σy²) = min(monomial-ratios, n/2)` CAN
fail in general — later blow-ups can make an exceptional coord divide a combination defining the block (verified:
a 2-pivot residual carries `q²` on a sub-block). pp REFINED this into the usable form: the entanglement lands at
**T1 (unit) termini** — where the residual is `monomial × (unit with constant term)`, so it's a clean
monomial×unit leaf either way and the split is IRRELEVANT — and NOT at **T2 (smooth-block) termini**, the only
place the split matters, where the block coords are fresh ratio/residual coords with the exceptional pulled OUT
front (disjoint). So Codex's CAN-ENTANGLE is correct but does not threaten Option B. VERDICT: A for fixed-M
(contract-fidelity, cheap at small M); B/HYBRID for general-M (lighter, reuses existing lemmas, no extra layer;
the hybrid applies the cone blow-up only where entanglement actually occurs, needing no global disjointness
guarantee). The block layer adds NO new G3 geometry (the block is a standard coordinate-cone) — it compounds only
G5 under A, which B avoids. So the residual-block handling does NOT compound the genuine wall (G3); the wall stays
G3 alone. LESSON (general): when a decorrelated model flags a failure mode as FACT, the value is often not
"abandon the approach" but "locate WHERE the failure lands" — a real failure mode confined to the cases where it
doesn't matter is a refinement, not a refutation. (Pair with the Q4-trap lesson: there, a matching answer wasn't
a proof; here, a real obstruction wasn't a blocker. Both: interrogate the SCOPE of the model's claim.)

## 2026-06-21 — state the hypothesis for what it ACTUALLY needs (product-MIN: positivity-guard, not "vanishes only at 0")

The (2,1,2) `product_min_rlct` lemma (`rlctAtOn(G·H) = min(rlctAtOn G, rlctAtOn H)`, disjoint vars) was
first stated with hyp "G,H ≥ 0 each vanishing only at 0." Re-examining shapes (prompted by rv-2's
S1.5-PASS — checking whether S1.5 was the (2,2,2) δ-leaf tool; it is NOT, S1.5 is a SUM-shift, the δ-leaf
is a PRODUCT) surfaced that "vanishes only at 0" is SUFFICIENT-BUT-OVER-STRONG: it excludes MONOMIAL
factors (`x²s²` vanishes on hyperplanes, not only at 0), so the lemma as stated would WRONGLY fail to
cover the δ-leaf (`monomial × block`). The hypothesis the proof actually USES is only the POSITIVITY
GUARD (both block integrals `∫⁻ > 0`, ruling out the ℝ≥0∞ `0·∞=0` corner) + disjoint vars + measurable.
Restating with the positivity guard UNIFIES three cases under one lemma: block×block (2,1,2),
monomial×block (the δ-leaf), monomial×monomial. LESSON: when a hypothesis is "obviously true for the case
in front of you" (the smooth block does vanish only at 0), check whether it's what the PROOF needs or
just what's CONVENIENT — an over-strong hyp silently narrows the lemma's reach and blocks reuse on a
sibling case (here the monomial factor). State the hypothesis at the altitude the proof actually requires.
(Dual of "name the result for what it is" — name the HYPOTHESIS for what it is: the minimal guard, not a
convenient sufficient condition.)

## 2026-06-21 — per-chart cover value is the JACOBIAN-WEIGHTED threshold, NOT bare rlctAtOn(F∘φ)

Pairing with fm-2 on the (2,2,2) cover measure pieces, fm-2 asked for the exact δ-leaf RHS "to dodge
another bare-false trap." Pinning it caught one: the per-leaf contribution to the cover rlct is
`weightedThreshold (F∘φ) |Jac φ| {0}` (weight ρ = the Jacobian), NOT `rlctAtOn (F∘φ)` (which is
`weightedThreshold F 1 {w*}` — TRIVIAL weight ρ=1, `Rlct.lean:168`). For the δ-block leaf
`x²s²u²·unit`: bare `rlctAtOn = min(½,½,2,…) = ½` (WRONG), but the Jacobian `x³s²u³` shifts the
exponents to `min((3+1)/2,(2+1)/2,(3+1)/2) = 3/2` (correct, matches the cover). The Jacobian weight IS
the content of the resolution — it's what makes the divisor ratios `(h+1)/(2k)` come out right.
Mechanically safe: the change-of-variables lemma `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
PRODUCES the `|det fderiv|·g∘φ` integrand, so the Jacobian lands in the `weightedThreshold` ρ slot
automatically — but ONLY if the per-chart lemma is STATED as a weighted threshold. State it as bare
`rlctAtOn(F∘φ)` and you've dropped the Jacobian and get the wrong value. LESSON: in a resolution-RLCT,
the per-chart value is the Jacobian-WEIGHTED threshold; the bare rlct of the pulled-back function omits
the divisor weights and is wrong. (Reusable for the general G3 tide — every per-chart lemma there is a
weighted threshold too.) The DLNFibre `weightedThreshold (G ρ K)` def has the ρ slot precisely for this;
`rlctAtOn`/`rlctAt` are the ρ=1 specialisation and must NOT be used for a chart that carries a Jacobian.

## 2026-06-21 — single-writer on the contract file; don't spawn parallel sessions re-proving closed rungs

A parallel session re-derived `deepestPoint_exists` ("prove r=0, narrowed r>0 sorry") while fm's branch ALREADY had
the fully-proven r>0 case (sorry-free, #21) — a merge divergence fm had to resolve (keep the complete proof,
salvage the parallel side's helpers). Wasted effort + reconciliation cost on an already-closed rung. LESSON: the
Skeleton (contract file) has ONE single-writer (fm); other sessions must not edit it or re-prove its rungs.
Delegate sub-tides to a DISTINCT file/lemma (proof-module pattern: _aux in Foundations, never the Skeleton), and
check a rung's status before assigning (sorry-free on trunk / done = closed; don't re-open). Controller corollary:
when two agents reach for the same lemma (the rlctAt_mono collision), resolve the lane + delete the duplicate task
immediately — overlapping assignment is the upstream cause of duplicated/divergent work.

## 2026-06-21 — a PROVEN, TRUE, hypothesis-sharpened result can STILL be an orphan (S1.1 mis-scoped for its use-site)

fm's SPECIFY phase found a single explicit blow-up chart does NOT satisfy S1.1 `weightedThreshold_transport`'s
GLOBAL `IsProperMap` + `Surjective` hypotheses (a blow-up chart is non-injective on the exceptional, not globally
proper/surjective). pp traced the full reverse-dependency: `weightedThreshold_le_transport` (no external consumer),
`weightedThreshold_transport_aux` (used only by its wrapper), `weightedThreshold_transport` (no rung consumer) —
and D1 (`rlctAt_mono`), L1/L2 (`block_elimination`/`product_reduction`), R1 (`g5_flat_cover`) all independent of it.
So S1.1 is an ORPHAN. This is a DISTINCT pattern from the resolution_charts orphan above (which was orphaned AND
FALSE — an unchecked landmine): S1.1 is orphaned AND TRUE — it was even SHARPENED to a true statement by the
10th-finding (`hsurj`+`hImE` added so the bare equality holds). The trap here is subtler: a result can be proven,
true, AND have its hypotheses carefully sharpened, and STILL be mis-scoped — because the true statement's
hypothesis SHAPE (global proper+surjective) doesn't fit the use-site that motivated it (per-chart blow-up transport,
which is non-injective-off-a-null-set; carried by g5_flat_cover instead). LESSON: "proven + true + sharpened" is NOT
"plugged in." Sharpening a statement's hypotheses to make it TRUE (the 10th-finding) is necessary but does not
verify the hypotheses MATCH the intended consumer's shape. Track a rung by its actual CONSUMER (grep the call-site),
not by "it's proven and true." When the use-site's shape (per-chart, non-injective) differs from the lemma's
hypothesis shape (global, proper+surjective), the lemma orphans even though both are individually correct.
Name it honestly: ORPHAN-pending-reuse (S1.1 is still bedrock — axiom-clean, true general transport; the global
proper+surj form is a candidate for the G3 tide's GLOBAL Lemma-2 unit-Jac reparam, distinct from the blow-up charts
g5 carries). The earlier pp claim "S1.1 carries the blow-up CoV" was imprecise — g5_flat_cover does. Name the
consumer, not the theorem.

**THE ACTIONABLE EDGE (controller self-noted — applies to controller AND pp):** VERIFY THE USE-SITE ACTUALLY
CONSUMES THE LEMMA BEFORE SHARPENING ITS HYPOTHESES TO FIT IT. The 10th-finding sharpening of S1.1 (adding
hsurj+hImE) was driven on the ASSUMPTION that S1.1 was R1's transport — an unverified-consumer assumption. Effort
went into making S1.1's hypotheses fit a use-site that, on inspection, doesn't consume S1.1 at all (R1's blow-up
charts are per-chart non-injective, the wrong shape for S1.1's global proper+surjective; g5_flat_cover is the real
transport). The cheap check — "grep the call-site: does the rung that motivates this lemma actually invoke it, with
THESE hypotheses?" — comes BEFORE the expensive sharpening, not after. Had it been run first, S1.1 would have been
scoped to its true consumer (a global reparam) from the start, or recognized as not-yet-needed. Order of operations:
(1) name the intended consumer, (2) verify the consumer's use-site shape matches the lemma's hypothesis shape,
(3) THEN sharpen. Skipping (2) produces a proven-true-but-orphaned lemma — wasted sharpening effort + a misleading
"S1.1 is the transport linchpin" in the contract until the trace corrects it.

## Green-gate gap: `lake build <lib>` only covers the aggregator's transitive closure (2026-06-21)

`lake build DLNFibre` builds only what the aggregator `DLNFibre.lean` imports (its transitive
closure). Engine modules built AHEAD of their consumers — S1ProductMin (#56), S1G5 (#52),
ParamsFlat — are imported by nothing wired into the headline, so they were **never compiled by the
standard green-gate**. A broken or unsound orphan engine would pass `lake build DLNFibre` silently.

**Caught by:** an `#print axioms` run failing with `'S1ProductMin.olean does not exist'` — the module
had never been built. Building all Foundations modules explicitly (`lake build DLNFibre.DLN.RLCT.Foundations.*`)
closed the gate; all green, #56 axiom-clean.

**Lesson:** a green `lake build <lib>` is *necessary but not sufficient* — it covers only what the
aggregator reaches. Gate orphan engines explicitly until they are consumed, and keep them permanently
covered by (a) importing stable engines into the aggregator and (b) a restored `AxCheck.lean` that
`#print axioms` the key results on every build. "Green build" ≠ "every module compiles."

## Decorrelation tool intermittent: the codex CLI hangs in down-windows (2026-06-22, down ~22:00+)

The local `codex` CLI is non-functional in this environment. `~/.local/bin/codex` is an AISI wrapper that
runs `uvx --with git+ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools aisitools override-key`
(the sanctioned AISI key-governance step) on EVERY invocation, and that git-ssh fetch HANGS before codex
ever starts — even `codex --version` times out; `~/.codex/auth.json` is absent.

**INTERMITTENT, not all-day-down (corrected ~22:00 from a teammate's data):** a fresh consult (g165)
LANDED successfully at 21:50 today — real 63-line output, a completed run (it confirmed PIN 0's Route A,
a valid decorrelated opinion). The controller's tests + a teammate's re-test hung only from ~21:56/22:00+.
So codex cycles up/down; the wrapper's uvx git-ssh fetch is the DOWN-window failure mode. The controller's
earlier "down environment-wide" over-generalized from down-window samples — timestamp any "codex down"
observation (a later window may work; it is timing out as of ~22:00+). Standing discipline unchanged: don't
DEPEND on codex (substitute subagents + handback-on-thrash); treat an up-window consult as a bonus.

## Skeleton-first trap: a pinned signature can be vacuously satisfiable (2026-06-22)

The L2 gauge-chart assembly was built skeleton-first: `deepest_gauge_construction` "proven from 4 obligations",
3 PINs sorried, "signatures pinned by the assembly typechecking." An independent formaliser on PIN 1
(`deepest_regAbsorb_exists`) found its pinned signature is VACUOUSLY satisfiable: `regAbsorb := id` satisfies
all 4 conjuncts by `rfl` (id 0=0; fixes the core/spec slots; `rlctAtOn(F∘id)=rlctAtOn(F)`). So "the assembly
typechecks with PIN 1 sorried" did NOT guarantee PIN 1 is meaningful — id closes it, and then PIN 2
(`loss_squeeze`) receives `regAbsorb=id` and is FALSE (raw-reg loss_squeeze is false, g161). The PINs were
coupled through the shared `regAbsorb`, but PIN 1's signature didn't capture the coupling.

LESSON: skeleton-first pins signatures by typechecking, but TYPECHECKS ≠ NON-VACUOUS. Before trusting that
filling a sorried obligation is meaningful, run the INHABITANT-TEST: can a trivial inhabitant (id, a constant,
0) satisfy the signature? If yes, it's underspecified — the real constraint lives elsewhere (here, the
`regAbsorb = E-straightening` coupling that only PIN 2 sees), and a "green" fill would be hollow. Capture
cross-obligation couplings IN the signatures, or "proven from N obligations" is hollow at the vacuous ones.
Same class as the #70 all-interior=r confound and the `rlct_…`-named-but-only-codim trap: a green/satisfiable
thing that's actually special-case/vacuous. Green is necessary, never sufficient — and here an INDEPENDENT
formaliser's inhabitant-test was the instrument that caught what the skeleton author's typecheck missed.

## "Build completed successfully" ≠ exit-0 + no-error-grep (2026-06-22)

A formaliser committed @b96fd7f as "green" after checking only `lake build` exit-0 + a no-"error"-grep — but
the build had 4 real errors (a SIGABRT mid-build + name-resolution failures). exit-0 can mask a crash; a grep
for "error" can miss Lean's actual failure phrasing. The pushed branch was briefly build-broken; caught +
corrected @c15ef75 by checking the explicit `Build completed successfully` line (lake prints it only on a
genuinely complete build).

LESSON: verify a Lean build by the `Build completed successfully` line (or full job-count completion), NEVER by
exit-code + error-grep alone — a SIGABRT / elaborator crash can exit non-cleanly-but-not-1 and skip the error
phrasing the grep expects. This compounds the skeleton-first + vacuity traps: "green" must mean the build
genuinely COMPLETED, just as "the obligation is filled" must mean it's NON-VACUOUSLY filled. The controller
re-verifies `Build completed successfully` + `#print axioms` at integration (#28) as the backstop — agent
green-claims are necessary, not sufficient.

## A homeo field's `Continuous shift` requirement blocks a poles-shift; cutoff to satisfy it (2026-06-22)

The DeepestGaugeChart absorptions are `≃ₜ` FIELDS (global homeos), but the honest maps are local-only: the
Schur shift −Z(I+X)⁻¹Y has poles where I+X is singular (I+X=0 at X=−I; X unconstrained over `Matrix r r`), and
the E-straightening is a nonlinear, non-globally-invertible diffeo. A homeo (`≃ₜ`) needs GLOBAL continuity,
which the poles-shift lacks.

THE SAFEGUARD (verified by crux2 — correcting an earlier over-statement that the masking *occurred*): the masking
does NOT actually occur. coreShearHomeo (and measurePreserving_coreShear) REQUIRE `Continuous shift` as a
hypothesis, so a poles-shift −Z(I+X)⁻¹Y is UNPROVABLE (you cannot prove `Continuous` of a pole-y function) —
build-time blocked, NOT silently-green. The peel goes through the homeo (rlctAtOn_comp_homeomorph takes a
`Homeomorph`), so it is Continuous-gated. So the cutoff is needed to SATISFY the `Continuous` requirement, not to
dissolve a green-masking. The general caution survives as a *conditional*: an a.e.-MP peel consumed UNGATED by a
homeo's `Continuous` hyp (i.e. via bare `Measurable`) WOULD ride green through a null singular locus — so verify
your peel is homeo-gated (Continuous), not MP-ungated (Measurable). This one is gated. Surfaced by a controller
consistency-flag + cobuild-sub34 verifying I+X is unconstrained (X=−I ⟹ I+X=0).

THE FIX (cutoff-inhabitation): inhabit the `≃ₜ` field with a global homeo whose GERM at 0 = the real (local)
map, via a globally-continuous CUTOFF (bump × correction, = the real map on a nbhd of 0, tame far away). rlctAt
is a germ + the peel (#72) is local, so the far-field is free; the local identity is all the downstream
consumes. Match the cutoff difficulty to the map: a TRANSLATION (coreAbsorb: core ↦ core + shift) is a global
`≃ₜ` for ANY globally-continuous shift (free); a NONLINEAR map (regAbsorb, Φ'(0) ≠ id) needs conjugate-by-Φ'(0)
+ cutoff-to-a-contraction + a global-homeo/Hadamard proof — if that walls, relax that field to a LOCAL
`OpenPartialHomeomorph` (what #72 consumes natively).

LESSON: a measure-theory / MP lemma that holds a.e. can MASK that an underlying homeo isn't globally continuous
— "green MP peel" ≠ "sound homeo." When a homeo field is inhabited by a map with a singular locus, verify
global continuity (or cutoff-inhabit the germ). Same class as the vacuity + #70 confounds: green is necessary,
never sufficient; the controller's consistency-flag was the instrument.

**Surfaced by:** pp2's #70 decorrelated consult "didn't land (CLI flaky — nested background launch)." The
nested-launch hypothesis was a RED HERRING: a top-level `codex doctor` / `codex --version` hangs identically.
It is an environment-wide outage, not a nested-launch artifact.

**Discipline held (the load-bearing part):** (1) did NOT bypass the wrapper with a raw `npx @openai/codex` —
that routes around the AISI key path (an org boundary); making a tool work is never a reason to breach the
sanctioned path. (2) did NOT substitute Claude's own answer for the missing Codex opinion (per the
`local-codex-consult` skill + `codex-consultation.md`). A failed consult is surfaced, not faked.

**Substitute while codex is down:** the harness's OTHER decorrelation channel — independent subagents
(reviewer red-team seats, pen-and-paper witness/obstruction seats, adversarial self-guards like pp2's g201).
Decorrelation degrades (same model family, no cross-vendor check) but is not lost. For a headline-load-bearing
design cert, run an independent reviewer subagent on the NAMED load-bearing claim before its build.

**Operator action (non-blocking):** restoring codex needs the `uvx` git-ssh fetch to `aisi-inspect-tools` to
succeed (network / ssh / key) — infra the agent cannot fix. Flagged; the expedition continues on subagent
decorrelation.

## Decorrelation earns its keep: the all-interior-width-=-r confound in #70 (2026-06-22)

The #70 degenerate-boundary cert (g202/g203) was validated by pp2 on 6 configs + an adversarial self-guard
(g201), and the controller endorsed the g203 sharpening ("flat = pure gauge r²(L−1)") as "clean and right."
A decorrelated adversarial subagent (substitute for the down codex, opposite-seat, its own exact algebra over
ℚ) then BROKE part of it:
- The VALUE (rlctAt(deepest, degenerate) = nReg/2) is SOUND — confirmed on 19 configs, and given a more robust
  reason than single-orbit: J's image surjects onto the determinantal-variety {rank≤r} tangent at B (dim nReg),
  capped by the variety, regardless of factorization or B.
- But deliverable (ii) "flat dim = r²(L−1), pure gauge" is FALSE whenever an interior width exceeds r:
  flat = ambient − nReg = ΣH_sH_{s+1} − r(H₀+H_L−r) (the fibre tangent dim) depends on interior widths;
  r²(L−1) (the gauge dim) does not. They coincide IFF every interior width = r — exactly the regime ALL 6
  validation configs sat in. Witness: (4,2,3,2,4) r2 → flat 16 vs r²(L−1)=12.
- And the "genuinely flat Morse-Bott" justification is wrong: along the LINEAR nullspace the loss is t⁴, not 0
  (flat only along the CURVED gauge orbit). The value survives via "smooth codim-nReg fibre cut transversally",
  not "linear Morse-Bott".

TWO lessons:
1. A validation set that all shares an unstated special property (here: every interior width = r) validates the
   SPECIAL case, not the general claim. The controller read 6 configs as general when they were collinear in the
   confound. When you reach for "clean and right," look for what every example quietly has in common. (Controller
   owned the endorsement error; Bayesian update.)
2. With codex down, a decorrelated SUBAGENT (opposite-seat adversary, own exact algebra) caught a real confound
   the author's self-check + the controller's endorsement missed — fired BEFORE the build (gated on L2), so it
   prevented a wrong-route build. Substitute decorrelation works; run it on the design before the compute.

BUILD-ROUTE CORRECTION (carry into #70's formalisation): build rlctAt_deepest_degenerate via the smooth
codim-nReg fibre cut transversally (rank dΦ = nReg) → L2's smooth-block primitive on the ADAPTED (fibre-normal)
coordinates → rlctAt = nReg/2. NOT via a genuinely-flat linear Morse-Bott complement (the raw nullspace carries
t⁴). The headline value nReg/2 = aoyagiLambda is unchanged; only the cert's reasoning + the flat-dim formula are
corrected. Seat's scripts: expeditions/2026-06-20-aoyagi-full/threads/adv-degen-boundary-witness/.

## Divergent file copies across branches → phantom disagreement; declare canonical early (2026-06-23)

A 6-pass coordination stall: cobuild-sub34 asserted "your coreAbsorb is the UNIT, fix it to Schur" while crux2
(correctly) insisted "it's already the additive Schur." Both were right about THEIR OWN branch — DeepestGaugeChart.lean
had forked into two copies on origin: fm2/split-reindex (517L, the (e)-fix structure, 34 regAbsorb mentions, docstring
corrected to additive Schur) and fm2/deepest-gauge-chart (467L, pre-(e)-fix, ZERO regAbsorb, the STALE multiplicative
gloss "T·(I−VY)⁻¹" at line 250). cobuild-sub34 read the stale line-250 gloss on the older branch; crux2 read the
corrected one on the newer. The "bug" was phantom — the coreAbsorb FIELD is abstract+Schur on both.

LESSON: when two agents persistently disagree about what a file SAYS (not about the math/design), suspect BRANCH
DIVERGENCE before re-litigating the content — a key file forked into divergent copies makes each "I verified it"
true-but-incommensurable. Resolution (controller): git-verify the divergence (line counts, key-decl presence e.g.
`grep -c regAbsorb`, the disputed line) → DECLARE ONE canonical copy → direct everyone to build against it. Do it
EARLY: divergent copies of a load-bearing structure must collapse to one BEFORE consumers build against the wrong
version (here the L2 PINs). The diagnostic (grep both branches for the disputed token) is cheap — reach for it the
2nd time a "what does the file say" disagreement repeats, not the 6th. (crux2 found the root cause; controller
git-verified + declared fm2/split-reindex canonical.)

ADDENDUM — divergence also makes the CONTROLLER nearly re-derive proven work (2026-06-23). Resuming post-compaction,
I scoped D1's ≥-leg, concluded "r=0 homogeneous deepest=min has an open analytic crux (lsc-at-origin)", and SPAWNED a
decorrelated pen-and-paper to adjudicate it. Then TaskGet #42 revealed the crux was ALREADY PROVEN sorry-free on
fm2/d1-deepest-min @8d0fd21 (DeepestMinRlct.lean: rlctAtOn_lsc_at_origin + deepest_le_of_homogeneous_core) — the proof
lived on a branch my working tree (expedition/aoyagi-full) doesn't show, so it was invisible to file-reads + greps
scoped to the checkout. Stood the pp down (1 wasted spawn). LESSON: D1 work is scattered across ≥3 branches
(fm2/d1-deepest-min = canonical proof; d1-scope = roadmap docstring; expedition/aoyagi-full = headline+sorry); the
TASK DESCRIPTIONS are the only divergence-aware record (#42 already said "PROVEN @8d0fd21"). Before commissioning ANY
new work on a leg: (1) TaskGet the leg's task FIRST and read its full description, (2) `git grep <target-decl>` across
ALL branches, not just the checkout. A clean working-tree file-read is NOT evidence the result is unproven — it may be
proven one branch over. (Reinforces: collapse divergence EARLY — the #28 consolidation deferral is now actively
costing controller cycles, not just risking future merge pain.)

## Classical.choice discards the witness's structure — only the PREDICATE survives (2026-06-23)

I told cobuild "(iii) confirmed, proceed" — that the deepest point's interior frames are trivial (G_s=I, clean
telescoping ∏A = P_0⁻¹·∏C·Q_{L-1}⁻¹), citing #77's docstring ("interior deepest layers are already block-normal").
crux2's decl-first verification caught it WRONG before a build: `deepestPoint := (Classical.choice (deepestPoint_exists
…)).1` is CHOICE-OPAQUE, and `IsDeepLayers` (the only thing `deepestPoint_isDeep` exposes) pins ONLY per-layer
`rank = r` — NOT the block-normal/corM structure. #77 therefore uses the GENERIC `rank_normal_form_exists` → per-layer-
NONTRIVIAL frames, not interior-identity. The docstring's "interior block-normal" is true of the wLayers WITNESS that
`deepestPoint_exists` constructs — but `Classical.choice` DISCARDS that witness; the surviving handle on the extracted
`deepestPoint` is exactly `IsDeepLayers`, nothing more.

LESSON: a property holds for a `Classical.choice`-extracted term ONLY IF it is in the PREDICATE the existence
quantifies over — never because the existence PROOF (or a docstring describing the construction) happens to build a
witness with that property. To make a construction-property usable downstream, it must be CARRIED IN THE PREDICATE
(here: strengthen `IsDeepLayers` to add the corM-interior conjunct + have `deepestPoint_exists` establish it — controller
ruling (a), task #95). Controller discipline: do NOT confirm a geometric "proceed" off a docstring's description of the
witness; demand the decl-first check that the property is in the predicate the choice-term satisfies. This nearly put
both L2 PINs' framed-product telescoping on frames the choice-opaque `deepestPoint` provably does not have. (crux2
decl-first-caught; controller ruled the spine-strengthen (a) over the heavier per-layer-nontrivial twisted-product (b).)

## Long-lived RESUMED background agents drift on stale transcripts — spawn FRESH for a new grind (2026-06-23)

fm3's spawned background formaliser (a8c41813) handed back THREE times on STALE blockers: each resume reads its own
prior transcript SNAPSHOT, not the current branch HEAD, so it re-surfaces obligations resolved AFTER its snapshot
(asked for a PivotWitness (A)/(B) anchoring ruling already committed @4802af4; offered to build `continuous_dlnLoss`
already banked @3b05766 — its OWN prior commit). fm3 re-unblocked it each time (pull HEAD, verify against the committed
decl), but the drift recurred on the next resume.

LESSON: a long-lived RESUMED agent accumulates transcript-vs-branch drift — its context is frozen at spawn/last-resume
while the branches move under it. For a NEW unit of work (e.g. when the pp-r1realize §4 verdict lands and the routeStep
grind is dispatched), spawn a FRESH agent with a clean read of current HEAD, OR hand a self-contained brief with the
current decls inlined — cheaper than re-syncing a drifted one. Resume only for genuinely continuous work where the
agent's accumulated context outweighs the drift. (fm3 g213 @10b6f92; controller will spawn fresh for the §4 dispatch.)

## A passing review can certify a REVERSED claim by auditing an orthogonal-true sub-statement (2026-06-23)

rs-grind's #108 leaf-classifier statement card (@801ecdb) PASSED review — reviewer survived, decorrelated-Codex
CONCURRED — yet its ⊤-trap caveat asserted the REVERSED leaf-value: "the leaf VALUE must route through the #70 Morse
handler (rlctAt = nReg/2), not the additive ½·minAdm fold." That is the g233 INTERMEDIATE that pp2's g237 trace + the
controller's pinning had already reversed (leaf = ⊤ non-binding terminator; value rides the accumulated BRANCH-divisors
→ ½·minAdm; #70 = degenerate-ROOT-only, NOT per-leaf). The card was written mid-flip-flop and froze a reversed
intermediate.

THE FAILURE MODE: the caveat's premise "dlnLoss M 0 ≡ 0 at a leaf ⟹ RLCT = ⊤" is TRUE — but that is the NODE's
GEOMETRIC RLCT, an object ORTHOGONAL to the leaf's FOLD-contribution. The reviewer + Codex audited the true-but-orthogonal
sub-statement (node-RLCT = ⊤) and concurred, which MASKED the wrong INFERENCE ("⟹ leaf VALUE = #70"). A green review
(reviewer-survived + decorrelated-Codex-concurred) certified a conceptually-reversed caveat because the audit landed on
an adjacent true fact, not the exact claim.

LESSON: a passing review — even decorrelated-Codex-concurred — is NECESSARY, not SUFFICIENT; it can certify a REVERSED
inference when the reviewer audits an orthogonal-but-true neighbour instead of the exact claim (the same "green ≠ The
Way" gap as the sorry-gate, now at the review layer). Two compounding hazards: (1) artifacts (cards / docstrings / certs /
notes) written DURING a flip-flop freeze reversed intermediates; (2) a review can "pass" them by auditing the adjacent
truth. Controller discipline: (a) when a claim has flip-flopped, RE-AUDIT every artifact written in the flip-flop window
against the FINAL semantics — do not trust a mid-flip-flop "reviewed" stamp; (b) a review must target the EXACT inference,
not an orthogonal-true neighbour (here: "leaf FOLD-contribution = ⊤ non-binding", NOT "node-RLCT = ⊤"). ACTION for #28:
the re-audit sweeps ALL flip-flop-era artifacts (cards, docstrings, certs, notes) for reversed-intermediate captures and
verifies each against the g237-final semantics. (fm3 fidelity-caught the card AFTER reviewer + Codex had passed it;
controller banked the lesson + elevated the #28 sweep. The leaf-value's ~5x flip-flop is what made a reversed card
plausible enough to pass — reinforces: collapse a flip-flopping claim to a PROVEN anchor fast, then re-audit its trail.)
