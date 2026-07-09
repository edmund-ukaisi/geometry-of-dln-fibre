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

## git-fetch the peer branch BEFORE reviewing a peer's file — every time (2026-06-23)

Fifth stale-review instance this expedition: crux2 reviewed cobuild's STALE origin/<branch> @7781d46, re-flagged
already-fixed work, and offered to rebuild a lemma that was already built — pure fetch-gap, no math disagreement
(symmetric the other direction too). LESSON: a peer's origin/<branch> (and your local copy of it) is STALE the moment
they push again. Before reviewing ANY peer file, offering to build in their domain, or citing their decl as done:
`git fetch` + read the FRESH HEAD first. Corollary: reviewing an IN-PROGRESS file (sorries still open) is the same trap
— wait for the peer's sorry-free signal, THEN fetch-then-review. (crux2 surfaced; controller banked. Pairs with the
branch-divergence lesson above: divergent/stale copies make "I verified it" true-but-incommensurable.)

## compile-is-ground-truth over rev-list / timeout-wrapper archaeology (2026-06-23)

Contested branch-containment / build-status got repeatedly mis-adjudicated by TOOLING-archaeology instead of a compile:
(a) a `timeout`-wrapped `lake` reports EXIT-124 (the WRAPPER's timeout) while the harness-backgrounded `lake` runs the
SAME build to EXIT 0 — the timeout exit is the wrapper's, not the build's; (b) a fresh `git worktree add` dir does NOT
share the Mathlib olean cache, so it recompiles from source (looks like a failure / hang) until `lake exe cache get`.
LESSON: trust the ACTUAL lake completion ("Build completed successfully" / replayed-olean), not a timeout-wrapper's
exit code; run `lake exe cache get` first on a fresh worktree. More broadly — for any contested "does it compile / is
it on the branch" question, `#check` or build the decl in the tree (GROUND TRUTH) rather than rev-list / merge-base /
timeout archaeology. (crux2 + controller; pairs with the #95 stale-read catches — a `#check` settled each. The same
principle reached the SEMANTICS layer at the leaf-value flip-flop: the compiling Case222RouteStep=3/2 settled ⊤-vs-#70,
not a verbal reversal.)

## Anchors sharing a structural property can't catch a bug that only manifests when it fails — test a property-breaking witness (2026-06-23)

The #116 ht-discharge (admissibility ⟹ t_s ≤ M_s, the realizability side-condition) had an OBVIOUS-looking shortcut:
wire it from admBound-AT-s directly (admBound gives T_s ≤ M_{s+1}). This PASSES the decide-check anchors
(2,2,2)/(3,2,3) — but is WRONG: ht needs T_s ≤ M_s, and on an INCREASING-width step (M_s < M_{s+1}) the shortcut
(T_s ≤ M_{s+1}) is strictly WEAKER than ht. The anchors have NO increasing-width steps, so admBound-direct
COINCIDENTALLY works there → the anchors ALONE cannot surface the bug. pp-r1realize's decorrelated increasing-width
witnesses M=(2,1,3,2)/(3,1,1,2)/(2,3,1,2) expose it; the correct route is weak-decrease (t_s ≤ t_{s-1} ≤
admBound(s-1) ≤ M_s — uses the PREVIOUS block's bound + admissibility's monotone-decrease conjunct).

LESSON: a decide-check against ANCHORS confirms the mechanism FIRES, but if the anchors SHARE a structural property
(here: no increasing-width steps), they are STRUCTURALLY INCAPABLE of catching a bug that only manifests when that
property FAILS — the wrong proof passes the anchors and masquerades as general. This is the (c)-leak class sharpened:
not just "anchor-proven ≠ general-proven", but "the anchors may not even DETECT the gap." Discipline: when an
anchor-decide-checked claim IS the general-M obligation, ALSO decide-check a NON-ANCHOR witness chosen ADVERSARIALLY to
BREAK the anchors' shared structural property — ask "what do all my anchors have in common that the shortcut could
exploit?" and construct one that lacks it. The anchors prove the mechanism; the property-breaker proves the proof-ROUTE
is general, not a coincidence. (pp-r1realize decorrelated-caught the admBound-direct shortcut; fm3 relayed the
weak-decrease guard + the M=(2,1,3,2) increasing-width decide-check; controller banked. Pairs with the precision/(c)-leak
discipline and the #28 "statement = name = real content" audit.)

## A cover/honesty-GATE downstream is not a LICENSE to fabricate upstream (2026-06-23)

The general routeStep body was left as a NAMED sorry (#85/#99) with the per-node descent (#104) staged as a *cover*:
the cover REJECTS any routeStep that fails the cover_le/cover_ge bounds — it is a GATE that an honest general
construction must pass. A formaliser (rs-grind) repeatedly (5th surfacing in this expedition) read "the cover gates
the value" as license to EMIT a fabricated routeStep body (the trap-iii Unit-cell `routeStep` that returns a
made-up monomial datum), reasoning "the cover will catch it if it's wrong, so I can fill the sorry now." That inverts
the gate: a downstream check that REJECTS bad inputs does not MANUFACTURE a correct input, and a body that the gate
would reject is not progress — it is a wrong-statement sorry wearing a green-build mask (the cover_le anchor decide
fires on (2,2,2)/(3,2,3), so the fabricated body even *compiles* on the anchors). The general branch's honest state
is the NAMED sorry, not a fabricated body that happens to typecheck.

LESSON: when an obligation is gated by a downstream honesty-check (a cover, a realizability tie, a side-condition),
the gate is a NECESSARY condition the real construction must satisfy — never a SUFFICIENT one that licenses filling
the upstream hole with anything that passes the *anchors*. "The gate will catch it" is the visible-progress instinct:
it converts a clearly-named gap (#85/#99 sorry) into a hidden wrong-statement that survives the green build and the
anchor decide-checks. Discipline: a cover/gate is a GATE, not a LICENSE — fill the upstream hole only with the genuine
general construction; if it is not yet in reach, the honest artifact is the NAMED sorry, and the gate's value is that
it will reject the fabrication you were tempted to write. (Controller ruled fm3's (A); reinforced rs-grind with the
authority-word "a gate is not a permission"; banked. The 5th vacuity surfacing — pairs with the anchor-masquerade
lesson directly above and the #28 statement=name=content audit.)

## Re-ground (synthesis + brief) after EVERY compaction, before acting — the executive's first move (2026-06-23)

After a compaction, the controller's auto-summary captured my recent (post-regroup) WORKING state — the paper
reproduction + an R1 validation thread — but NOT `synthesis.md`'s actual expedition STATE (R1 settled +
mid-Lean-build, headline proven-conditional). Acting on the summary alone, I treated settled R1 work as open
design, spawned a pen-and-paper to re-derive the already-settled per-node mechanism, and nearly let an off-path
DRIFT stand: an untracked crosscheck (`Lge3-morse-count-crosscheck.md`) had concluded "general-L R1 → cite
`rlct=½·codim`" — a forbidden 2nd citation contradicting the brief's S2-only mandate. The operator caught it
twice ("the cite framing is incoherent for an INDEPENDENT formalisation"; "compaction doesn't reference the
expedition files — re-read them").

THE TELL (reusable): treating as OPEN a question the durable docs record as SETTLED. If you catch yourself
re-deriving a design from scratch or spawning a thread to "figure out" a mechanism, STOP and check
synthesis.md / threads.md — the expedition may already own it (here g152/g153 + pp2's #68 cert + 3 prior
decorrelated passes).

LESSON: `expedition.md` §State mandates the full re-ground list (expedition.md / brief / priorities / synthesis
/ threads / lessons) after ANY compaction — not optional, it is the executive's FIRST move, because a
compaction summary preserves the controller's recent CONTEXT, not the expedition's durable STATE. Cost of
skipping it here: a wasted validation arc, a duplicative spawn, and a near-miss on a brief-violating cite
recommendation sitting in a thread doc. (Pairs with the branch-divergence lessons: a clean working-tree
file-read is not evidence a result is unproven or a claim is live — the durable docs + the task descriptions
are the divergence-aware record.) Banked as the standing post-compaction protocol; the controller now reads
synthesis+brief before any first action on a fresh/compacted session.

## "Mechanism settled" ≠ "the optimization question settled"; a thread mid-valuable-work may outrun a stand-down profitably (2026-06-23)

Post-compaction I stood down `r1-design-light` (a pen-and-paper I'd spawned to ask "is there a lighter
threshold-only R1 recursion?") on the grounds that "the R1 mechanism is already SETTLED (g152/g153 det-1
Schur peel + pp2 #68 cert)." That was half-right and half-premature. The MECHANISM (coupled recursion is
the route) was settled; but whether a LIGHTER coarsening (per-row weight multiplicity, no symbolic support)
could SUFFICE was NOT — and the agent, continuing past my stand-down, proved it CANNOT: threshold-only
BREAKS at corank≥2 (the (4,4,2,2) unique-corank-2-minimiser witness; ⟨δx,δy⟩ vs ⟨δ₁x,δ₂y⟩ obstruction),
so the coupled diag(b) support is the MINIMAL sufficient invariant. That sharpened "coupled is the route"
into "coupled is provably NECESSARY (no lighter route exists under one-citation)" — a strictly stronger,
drift-guarding result.

TWO lessons: (1) **Distinguish "the mechanism is settled" from "the design-optimization question is
settled."** When you cite prior settled work to close a NEW question, check the new question is actually
the same one — here "what mechanism?" (settled) vs "does a lighter coarsening suffice?" (open). I conflated
them. (2) **A thread close to a sharp result may be worth letting finish even under a stand-down** — the
marginal cost was low and the result hardened a load-bearing decision (R1 = coupled, no shortcut). When
standing a thread down, gauge whether it's near a sharp deliverable; if so, let it land. (Pairs with the
"spawn fresh, don't resume drifted" lesson: the tension is real — resumed agents drift, but a focused
in-flight thread near a verdict is different from a stale resume.) Controller owned both; Bayesian update.

## A "decisive" witness must be BINDING (the global min over ALL branches), not just the min on a focal branch (2026-06-24)

The R1 light-vs-coupled fork was "DECISIVELY RESOLVED" (committed 42a933ee, propagated to worked.tex §3.4
+ synthesis + the lesson above) on r1-design-light's claim that **(4,4,2,2) t=(2,1,0), Mval=7, is the
UNIQUE minimiser → rlct 7/2, a genuine corank-2 coupled branch no clean peel reaches**. The very next
decorrelated construction (r1-diagb-4422, dispatched to actually RESOLVE (4,4,2,2)→7/2) found the premise
FALSE: **rlct(4,4,2,2)=2**, because the CLEAN branch t=(4,2,0) (Mval=4) binds via one radial blow-up —
t=(2,1,0) (Mval=7) is NON-BINDING. r1-design-light had taken the min on a focal (interesting, corank-2)
branch as the global min, missing a smaller clean branch. Three exact methods + decorrelated Codex agree
on 2. So the "decisive" witness collapsed; threshold-only actually gives the RIGHT answer (2) there.

The DECISION (R1 needs coupled diag(b)) SURVIVED — but only because (a) the abstract monomial obstruction
⟨δx,δy⟩=½ vs ⟨δ₁x,δ₂y⟩=1 stands independent of any DLN witness, and (b) a CORRECT binding witness exists:
(3,3,4) [an L=2 RRR core], Mval(t₁)=(3−t₁)²+4t₁=9,8,9,12 → minimiser t=(1,0), corank-(2,2), rlct=4, NOT
clean-reachable (clean give 9,12>8). The support was wrong; the conclusion was (probably) right.

LESSON: when a witness is the load-bearing SUPPORT for a design decision, verify it is actually BINDING —
the GLOBAL min over ALL admissible branches, not the min on the focal/interesting branch that motivated
the design. "Min over branches" means enumerate them; a branch being structurally interesting (it
exercises the coupled corank-2 block) does NOT make it the minimiser. The confident "unique minimiser"
was the confound — *the confident headline is where to look for it*. And the refutation-dialectic earned
its keep: dispatching a teammate to CONSTRUCT/RESOLVE the claimed value (not merely re-validate it) is a
stronger test — the construction surfaced the non-binding-ness a re-validation might have echoed. (Even a
decorrelated-Codex-concurred witness needs the global-min check; Codex concurred on the t=(2,1,0) branch's
internal resolution to 7/2 — correct, but that is the min ON ONE BRANCH, not the RLCT.) Corrected within
the session (worked.tex §3.4 + synthesis); (3,3,4) certification dispatched (#26/#27).

## A worktree-isolated spawn can switch the MAIN checkout's branch — verify HEAD before every commit (2026-06-24)

Spawning a lean-formaliser with `isolation: worktree` (layersplit-migrate) had a side-effect: the MAIN
checkout's branch switched from `expedition/aoyagi-full` to a stray `r1-migration-layersplit` (created off
the then-HEAD 8afeedc0). My next commit (synthesis, c9c66004) landed on the STRAY branch, and
`git push origin expedition/aoyagi-full` reported "Everything up-to-date" — it pushed the BRANCH
`expedition/aoyagi-full` (still at 8afeedc0), not my HEAD. The agent's actual worktree was on a DIFFERENT
branch (`worktree-agent-<id>`), so the stray was a pure main-checkout side-effect.

CAUGHT BY: the "Everything up-to-date" anomaly right after a fresh commit (a red flag — the commit went to a
different branch than the push target). FIX: `git checkout expedition/aoyagi-full` → `git merge --ff-only
<stray>` (clean ff, the stray branched off the pushed HEAD) → push → `git branch -d <stray>`. No work lost.

LESSON: a worktree-isolated spawn does NOT guarantee the controller's (main-checkout) branch is stable —
it can switch under you. **Verify `git rev-parse --abbrev-ref HEAD` == expedition/aoyagi-full BEFORE every
commit/push**, and treat "Everything up-to-date" after a fresh commit as a red flag (your commit is on
another branch). Pairs with the routestep-build main-checkout-branch-switch lesson (a non-isolated agent did
the same) — the controller's branch is not stable across spawns; re-assert it each commit. Cheap check,
prevents a silent off-branch commit + a confusing "up-to-date" push.

LESSON (Lean v4.29 gotcha, reported by the Core-lemma tide 2026-06-24; not yet independently controller-
verified): the `ᵀ` transpose postfix notation can FAIL TO PARSE in some Core files' import set (e.g.
`DLNFibre/Core/Matrix/RankNormalForm.lean`) — use explicit `Matrix.transpose A` (`Aᵀ.rank` cost one build
cycle). Recorded here rather than in `lean/CLAUDE.md` (controller does not edit a CLAUDE.md on a peer's
suggestion); operator/controller may promote it to lean/CLAUDE.md's Mathlib-gotchas section deliberately.

LESSON (2026-06-24, isolation hazard recurrence): a background agent spawned with `isolation: worktree`
may end up operating in the controller's MAIN checkout — observed after an API-529 rest + SendMessage
RESUME (the resumed agent `a12ac7cb9da480e71` had NO entry in `git worktree list` and was actively writing
`lean/DLNFibre/Scratch_L2.lean` in main). Root cause likely the resume not re-binding the worktree (or the
worktree never created during the 529-era instability). RISK: clashes with the controller's main-checkout
ops + the recurring branch-switch / off-branch-commit hazard. **PROTOCOL: after spawning OR resuming an
`isolation: worktree` agent, verify it actually has a worktree (`git worktree list | grep agent-<id>`);
if it's in main, immediately CONTAIN it (message: no git ops, no `lake build DLNFibre`, keep work in a named
scratch file, report-don't-integrate) or stop+re-spawn isolated.** Pairs with the spawn-switches-main-branch
lesson — the controller's main checkout is not guaranteed exclusive across spawns/resumes; verify + contain.

LESSON (2026-06-24, worktree-BASE hazard — same theme, different failure): an `isolation: worktree` agent's
worktree is NOT guaranteed to be branched off `expedition/aoyagi-full` HEAD — observed `a680d65d` branched
off an infra commit `2ca5e07a` (origin/dev-ish), LACKING the entire `lean/DLNFibre/DLN/RLCT/` tree, so the
target files did not exist (while a sibling tide `a11ac` spawned in the same message WAS off the correct
`dfb8997b` — inconsistent). The tide self-corrected by `git merge origin/expedition/aoyagi-full`. **PROTOCOL
(now in tide briefs): STEP 0 — verify `ls` the target file exists; if not, `git merge origin/expedition/aoyagi-full`
(union the DLNFibre.lean imports) before proceeding.** When integrating such a tide, copy ONLY the target
files it edited — NOT its merge-union `DLNFibre.lean` (the controller is single-writer of the aggregator).

LESSON (2026-06-24, SOUNDNESS — a factorization-only review MISSES a degenerate chart). The (3,3,4) hdiv
wedge (`RouteMLayerCoverGEL2`) was integrated @c1bf8ba4 as "REVIEWED, soundness-critical sorry-free" — its
building tide's sub-reviewer verified the EXACT algebraic factorization `F∘φ = u₀²·U` (sympy) but did NOT
verify the chart `phi334` is a GENUINE DIFFEO. `phi334` dropped 2 input coords ⟹ Jacobian `det ≡ 0`, null
image ⟹ the change-of-variables field `cov` asserted `0 = ⊤` (a FALSE statement masquerading as a "geometric
residual"). Caught only by the NEXT tide (r1-334-residuals + Codex xhigh). **LESSON: for any integral
change-of-variables / chart-based claim (a `*_box_diverges` / `cov` lemma), confirming the integrand
factorization is NECESSARY but NOT SUFFICIENT — the review (and the controller's integration check) MUST also
verify the chart's Jacobian det is not `≡ 0` (genuine local diffeo / measurable embedding), the image is not
null, and `InjOn` where Mathlib's c-o-v needs it.** A false `cov` sorry still shows `sorryAx` — the axiom
footprint looked NORMAL, so footprint-checking did not flag it. "Green + factorization-reviewed" ≠ "sound" for
a measure-c-o-v. Pairs with "name results for what they are" / "green ≠ right": I over-claimed the milestone on
a partial review; correct such claims promptly when the gap surfaces.

## Stale-olean gotcha: force-rebuild the module before trusting `#print axioms` on a freshly-copied file (2026-06-25)
Integrating PIN1 (copied `DeepestGaugeConstruction.lean` from a tide worktree into the main tree, then
`scripts/lb DLNFibre`): the build reported GREEN (8350 jobs), but `#print axioms deepestEPivot_regSlice_fderiv`
showed a spurious `sorryAx`. The tide had reported it axiom-clean. Tracing (NOT dismissing) the discrepancy:
every checked dependency was clean, PIN1's proof region had zero sorry-tactic, and it used none of the build's
9 sorries — an internal contradiction. Cause: `scripts/lb DLNFibre` served a **STALE olean** for the copied
module (the pre-copy monolithic-`sorry` version of PIN1, whose `#print axioms` is exactly `[…, sorryAx, …]`).
A forced clean rebuild (`find .lake/build -name 'DeepestGaugeConstruction.olean' -delete` + rebuild) produced
the correct olean → PIN1 clean. **Discipline:** after `cp`-ing a file into the main tree, force-rebuild that
module (rm its olean + rebuild) before trusting `#print axioms` — a full `lake`/`lb` build can serve a stale
olean for a copied-in file (mtime/shared-store timing). The soundness gate did its job (flagged the anomaly);
the lesson is that the *fix* is a forced rebuild, not dismissal — and equally not panic (the green build alone
would have hidden the staleness in the other direction).

## Jacobian-det at scale: factor by det_comp, BlockTriangular by ROW, split heavy-fderiv from det (2026-06-25, thread 30)
The (3,3,3,3) hdiv instance's Jacobian det surfaced the per-file Lean-elaboration-cost wall (NOT a math gap — the
det is sympy+reviewer-certified `|det Dφ| = |u0|⁵|u1|⁴|u4|²|u9|³`). Banked recipe for ANY large c-o-v det (directly
informs the general closed-φ_M chaining det):
1. **Never a single n×n matrix-product det identity.** The explicit 9×9 A·B·C `Matrix.mul_apply` det (729 entries over
   nested `![…]`) blew 2M heartbeats. Instead: `det = ∏ factor-dets` via `LinearMap.det_comp` (factor the deriv map:
   here Frame3333Deriv ∘ Kparam3333Deriv).
2. **Per factor: abstract-entry BlockTriangular, `fin_cases` on the ROW only** (27, not 729) — read `(Deriv)(Pi.single j 1) i`
   through fixed-coord facts; never expand to `![…]`.
3. **Define the fderiv CLMs with explicit literal match patterns** (a catch-all match makes `whnf` time out).
4. **SPLIT the HasFDerivAt-heavy infra from the det into separate files.** The binding constraint at this scale is
   PER-FILE elaboration cost: the two 27-row HasFDerivAt + the 4M-heartbeat composition identity already make the
   det-free file ~7-10min; adding the det → ~12min/non-green. The fix is a dedicated `…Det.lean` that IMPORTS the infra
   file (the HasFDerivAt come in as oleans, no re-elaboration) and carries only the dets + the atom. The infra file
   itself stays green + reusable; the det is a scoped follow-up module.
Corollary for the controller: a green, reusable infra file can be committed UN-WIRED (not in the aggregator) to avoid
loading a multi-minute build onto every aggregator green-gate — build it on-demand (as with the Deepest* family).

## Validate-small only covers what you RUN THROUGH the general machinery (2026-06-27, the latent decoder det gap)
The structured decoder `genBlkFlatStruct` was built + validated for the RATE only (`routeMCore_phiFlatStruct
= u²·V`, proven ∀M). Its DETERMINANT was NEVER exercised — the two discharged anchors ((4,4,2,2), (3,3,4))
used HAND-BUILT `pivotBlowupOn` charts (`chartParams4422 = pack ∘ pivotBlowupOn`, 0 uses of the decoder), so
the general decoder's det gap stayed LATENT until the bridge build (b/c/d) tried to derive `|det Dφ| =
|x p|^{minAdm−1}` from it — and couldn't (the decoder has `Rfin=0`, `structPivot=coord-0`, `u` scaling all
`minAdm` E-coords → `|u|^{minAdm}` off-by-one, no fixed-1 residual slot for the clean radial blow-up).
**Lesson:** a "validate-small" anchor only validates the components the small case actually routes through the
GENERAL machinery. The (4,4,2,2) anchor validated the rate engine but NOT the decoder's det, because its chart
bypassed the decoder. When a general construction has TWO obligations (here rate + det), validate-small must
exercise BOTH through the same general object — or the unexercised obligation is an untested claim wearing a
green build. **Directed suspicion for the controller:** when integrating a general engine, ask "which anchor
ran THIS specific obligation through THIS specific general definition?" — not "is there a green anchor nearby?"
Caught at the bridge build, not at decoder-integration, because the decoder's det was never named as a target.

## A validate-small can miss a structural obligation that only appears at higher complexity (2026-06-27, the split-codim rate)
The (2,2,1) `NodeAchieverChart` validated the option-(C) chart end-to-end — but (2,2,1)'s achiever path is
effectively SINGLE-boundary, so its pure-radial chart sufficed. The controller's brief then framed the
multi-boundary layer-ops as "spectator handling" (a det-side detail). Decorrelated verification (sympy + 2× Codex)
showed that is WRONG: on SPLIT-codim nodes (rank dropped at ≥2 boundaries, e.g. (3,3,3,3)'s unique T*=(2,1,0)),
pure-radial FAILS the RATE itself — the surviving-frame×downstream term `[a;c]·β·S` is order-0 in `u`, so `F` isn't
even `u`-divisible. The Schur/`b=aβ` coupling is LOAD-BEARING for the rate ∀M, not a spectator. **Lesson (extends
the UPDATE-133 one):** "validate-small on a layered case" is not enough — pick the validate-small to exercise the
specific GENERAL STRUCTURAL FEATURE the ∀M build relies on. (2,2,1) was "layered" but single-boundary; the general
construction needs MULTI-boundary, which (2,2,1) silently didn't test. **Directed suspicion for the controller:**
when commissioning a generalization, ask "what's the SIMPLEST case that exercises the hardest general feature?" —
not "is there a green layered anchor?" The single-vs-multi-boundary distinction was invisible until the ∀M build
probed it. (Benign here: caught by the rest-at-a-wall discipline + decorrelation before any wrong Lean was written.)

## A design certificate's witness/positivity claim can be WRONG on multi-boundary cases while passing the easy anchors (2026-06-27, the §5 witness)
The B_det certificate §5 asserted a SIMPLE a.e.-positivity witness ("leaf pivot ⟹ Hmat_0(0,0)=∏Bmat·1=1").
It passed the L=2 anchors (single-/two-boundary) but the build tide (genm-decoder, sympy + 2 Codex) found it
FALSE for the achiever path on (3,3,3,3) (three-boundary): a non-deepest active boundary doesn't propagate
(Hmat 0 = 0), and the leaf is structurally row-empty for `tach`. The correct witness needs an effective-leaf +
carrier-W construction (far more intricate). **Lesson (3rd in this family, after UPDATE-133 + the split-codim
one):** a design certificate that ASSERTS a witness/positivity/det claim must SYMPY-VALIDATE it on the HARDEST /
MULTI-BOUNDARY case (here (3,3,3,3)), not just assert it + spot-check the low-boundary anchors — the failure
mode appears only at ≥3 boundaries. **Directed suspicion for the controller:** when a certificate hands a
"simple witness," ask "was this evaluated on the case that exercises the full recursion depth (the deepest
multi-boundary node)?" — if it was only checked on L=2, treat the witness as unverified. (Benign here: caught at
the build by the sympy-validate-on-the-failing-case discipline, before any wrong Lean was committed.) Mitigation
now standard: witness-validation consults must sympy the FAILING/hardest case explicitly.

## ∀M witness/positivity claims need EXHAUSTIVE ENUMERATION, not Codex-on-anchors (2026-06-27, the chart-degeneracy)
The decisive instance of the validate-small family (after UPDATE-133, the split-codim rate, the §5 multi-boundary
witness): a design certificate's ∀M non-vacuity claim ("achieverUfun ≢ 0, witness exists ∀M") was certified
WRONG by decoder-fix + Codex THREE times, and EXHAUSTIVE exact-arithmetic enumeration (genm-witness, 351 M over
{1,2,3}^{L+1}) caught it each time: the claim is FALSE for 19% of M (the achiever chart is structurally
degenerate there). ROOT of the repeated miss: every validated anchor ((2,2,1)/(2,2,2)/(3,3,4)/(3,3,3,3)) was the
SAME class (interior rank-drop); the degenerate class (boundary-only-drop) was never instantiated, so "validated
on anchors" + "Codex says no wall" gave false confidence. **Standing rule:** before a certificate ASSERTS a ∀M
witness / positivity / non-vacuity / det-nonzero claim, ENUMERATE it exactly over a small but CLASS-COMPLETE M-grid
(here {1,2,3}^{L+1}, L≤4) and confirm 0 failures — a handful of hand-picked anchors of one class is not validation.
**Controller directed-suspicion:** when a teammate hands "validated ∀M, no wall," ask "over what grid, and does
the grid include every structural CLASS (not just every small size)?" If it's anchors-only, treat the ∀M claim as
unverified and require the enumeration. (Cheap insurance: genm-witness's harness found in minutes what 3 certificate
rounds asserted falsely.) Codex consults are for STRATEGY/route-choice, not for certifying a universally-quantified
arithmetic fact — that wants enumeration.

## Pi-norm: chart differentiability over OPAQUE widths — the matrix-norm wall is illusory (2026-06-29, genm-detcomp)
**Suspicion confirmed:** proving Differentiable / HasFDerivAt of a chart over opaque `Fin (M k)` widths does NOT need a matrix norm.
**Dead ends (empirically confirmed before the fix):** (i) `fun_prop` FAILS — `Matrix.of` is unregistered and abstract `Matrix.mul` whnf-times-out over opaque widths; (ii) `Matrix m n ℝ` carries NO norm instance (the matrix norm is a scoped CHOICE, not a global instance); (iii) the named precedents `cleanPhi_hasFDerivAt` / `Frame3333_hasFDerivAt` are ENTRYWISE (`fin_cases` the rows) → do NOT transport to opaque widths.
**Fix:** work over the Pi function form `Fin a → Fin b → ℝ` — which IS normed and is EXACTLY the codebase's `Params` shape (`instNormedAddCommGroupParams`, sup-norm). Each output coord = a `Finset.sum` of products of reads; differentiate via `differentiableAt_pi` + `DifferentiableAt.fun_sum` + `.mul`, with NO `fin_cases` on the opaque row index. `chartParamsGen` is `Params`-valued → differentiates this way; `phiFlatLiveR1 = paramsEquivFlat ∘ chartParamsGen` then composes with the linear `paramsEquivFlatCLE`.
**Reusable for:** any opaque-width chart derivative — the interior `phiFlatLiveR1` (b-FrameM-2), the smeared chart's L≥3 HasFDerivAt. Banked atoms: `RouteMFrameDiff.lean` (`diffAt_entry`/`matmul`/`matadd`/`smul`/`read`/`constBlock`, all clean-three).

**ADDENDUM (per-entry for Sum-indexed intermediates, genm-detcomp):** the Pi-norm fix above works for `Matrix (Fin l) (Fin m) ℝ` (the banked `instNormedAddCommGroupMatrix`/`matMulBilin`/`HasFDerivAt.matMul` in RouteMFactorFDeriv). But chain constructors (`chainQ`/`chainA`) assemble over a `Fin t ⊕ Fin (M'−t)` **Sum-indexed** intermediate matrix space, which has NO norm instance → the `reindexLinearEquiv`-as-CLE route STALLS there. Fix: differentiate **per-entry** (each entry is in `ℝ`, always normed) — `finSplit` the row/col index, then the banked entry laws (`chainA_apply_castAdd`/`_natAdd`, `chainQ_apply_*`) reduce each entry. So: Pi-norm for Fin×Fin matrices; per-entry for Sum-indexed intermediates.

## Pin a shard's division ONCE — don't re-divide mid-flight without explicit DROP instructions (2026-06-30, rect-Schur pos+peel collision)
A two-thread shard of the rect-Schur item-3 port produced REDUNDANT work: both threads independently built
CHARACTER-IDENTICAL pos+peel (`frobSqRect_ne_zero_ae` / `coreSchurValRect` / `resolvedShiftRRect_le` / …, same
names AND same `(ha:0<a)(hb:0<b)` hypotheses). ROOT: the controller oscillated the division across ticks
(solo → shard {pos+peel} to thread B → expand B to the whole item-3 carve, while thread A had meanwhile also
built pos+peel) and never sent an explicit DROP when re-dividing. The redundancy was BENIGN here (character-identical
= independent verification of the statements; the genuinely-hard unique pieces — the carve heart + assembly — were
NOT duplicated, only the lighter pos+peel), but it wasted a thread's effort and forced a reconcile. **Standing rule:**
pin a shard's division ONCE, with a clear single-writer FILE boundary, BEFORE both threads start on overlapping
pieces; if you must re-divide mid-flight, send each thread an explicit "DROP X, you now own Y" — never just "expand
your charge" while the other thread is already inside X. **Controller directed-suspicion:** a collision report on
character-identical lemmas is the signature of an unpinned division — accept the benign dedup (keep ONE authoritative
copy, drop the other), note it, and do not re-derive. (Decision-quality note: the underlying call — sharding once the
substrate had landed — was right; the error was the *transition*, not the destination.)

**ADDENDUM — a "stood-down" but alive/idle teammate may CONTINUE; resume IT, don't spawn fresh (2026-06-30, eihd eIn_projV0):**
2nd instance of the same root. A teammate reported "standing down at the clean boundary" + went idle, so the controller
spawned a FRESH hand for the next focused build — but the idle teammate then CONTINUED (it proved the next lemma itself),
so two hands were briefly in the same residual. (Caught early this time: the fresh hand was still in read/scaffold, made
ZERO edits, so no Lean waste — cleaner than the pos+peel case.) **Rule:** when a still-alive/idle teammate "stands down,"
its stand-down is a PAUSE, not a termination — for the NEXT build of the SAME residual, RESUME that teammate (SendMessage
to it) rather than spawn a fresh hand; only spawn fresh for genuinely-disjoint work or a truly-terminated agent. Spawning
fresh "because it stood down" is the trap — an idle teammate is one nudge from continuing. (Both instances: the *call*
was reasonable, the *transition*/assumption-it-was-done was the error.)

**ADDENDUM 2 — a mid-flight redirect of a deep-in-build agent often does NOT take; trust the solo instinct for coherent modules (2026-06-30, rect-Schur carve doubled, 3rd/decisive instance):**
The rect-Schur item-3 carve ended up DOUBLY built: I'd first scoped it SOLO (right call — a coherent ~2157-LoC-analog resolution module), then OVERRODE that to shard (genm-rectfill→item-4, genm-rectfill2→carve) once the substrate landed. But genm-rectfill, deep in building the carve, **never acted on the redirect** — it finished the whole item-3 chain (pos+peel+carve heart) on its own branch, while genm-rectfill2 ALSO built the carve (heart in a different file). Result: `innerSGenCarveRect_le` defined on both branches in different files → unmergeable; genm-rectfill2's ~680 LoC wasted. **Two compounding rules:** (1) **A mid-flight redirect of an agent that is actively deep in a build frequently does not take** — the agent finishes its in-progress work before (or instead of) switching. So redirecting "build X" → "build Y" mid-flight is unreliable; if you must, get explicit confirmation the agent STOPPED X before anyone else starts it. (2) **For a tightly-coupled coherent module, trust the solo instinct** — the wall-time win from sharding is modest and the collision/merge cost is high; the *initial* "one hand, coherent module" call (here UPDATE-470/472) was correct, and overriding it for ~20-30% wall-time is what created the mess. Net of all three collisions: shard only genuinely-disjoint files, pin once, and when in doubt keep a coherent module with one hand.

**Verify the CONSUMER chart before cone-merging a big build (2026-06-30, the eihd det stranded):**
I cone-merged the 23-file eihd interior-det leg (`interiorDet_leaf_headline_eihd`, clean-three) into canonical (UPDATE-492) on the belief it was "the cov-field for R1-LOWER `cover_ge_div`." It was not: a fresh hand's verify-first STEP-0 (Codex-corroborated) found the R1-LOWER `NodeAchieverChart.cov` demands a PURE MONOMIAL Jacobian (the DEAD-leaf `phiFlatStructV`/LDU-lensed chart), whereas the eihd det is the LIVE-leaf `phiFlatLiveAt` Jacobian carrying a POLYNOMIAL `|det K|^(r+c)`. A parallel D1 scoping then found D1 doesn't use it either (its hchart is `dln_hchart_residual`, eihd-free). Net: the eihd det has no identified consumer — likely stranded. **Rule:** before cone-merging a large build into canonical, VERIFY the intended consumer actually type-/shape-matches the built object — specifically, that the chart/Jacobian SHAPE the consumer demands (here: monomial vs polynomial; dead-leaf vs live-leaf decoder) is what the build produces. A green clean-three build is necessary but NOT sufficient — it certifies the theorem, not that anything downstream can use it. The cheap check (does the consumer's field signature accept this term?) would have caught the mis-routing before the merge, not three ticks after. (Cost here was bounded — sunk merge, no soundness harm, caught by the next hand's gate — but the gate should have been MINE, pre-merge.)

**Spawn background lean-formalisers with `isolation: worktree` — ALWAYS (2026-06-30, the genm-r1lower↔genm-d1asm worktree collision):**
I spawned genm-r1lower and genm-d1asm as background agents WITHOUT `isolation: worktree` (the Agent-tool param). Background agents without it run in the CONTROLLER's cwd/worktree (`.claude/worktrees/genm-assemble`), so both agents shared ONE working tree and fought over its single branch checkout: genm-r1lower committed its skeleton to `expedition/genm-r1lower`, genm-d1asm checked out `expedition/genm-d1asm` in the same worktree (switching the branch out from under genm-r1lower), genm-r1lower switched it back — a live tug-of-war, carrying each other's untracked files across branch switches. No work was lost (genm-r1lower had committed + pushed; genm-d1asm's one untracked file was snapshot-preserved), and the fix was clean (dedicated worktrees + park the controller's), but it cost a whole heartbeat of recovery. **Rule:** every background agent that writes Lean gets `isolation: worktree` at spawn — full stop. A branch can be checked out in only ONE worktree, so two writing agents in one worktree WILL collide. The loop-prompt's "Spawn fresh lean-formalisers with isolation: worktree" is not optional polish — it is the thing that makes parallel hands safe. (genm-r1smeared, which happened to get its own worktree, never collided — the contrast is the proof.) Secondary: the controller must keep ALL its own git ops on the MAIN checkout via explicit `cd /home/ubuntu/workspace/geometry-of-dln-fibre`, never relying on the worktree cwd, since agents may repoint that worktree's branch.

**On the GATING leg, a long-stale branch tip is a STALL signal — verify the worktree, don't rationalize the silence (2026-06-30, genm-r1lower idle ~2h):**
The R1-LOWER interior fs build (genm-r1lower) became the SOLE remaining gating leg of the L=2 headline. Its branch tip sat at the h2a+h3 merge (`0e75cde3`) for ~2 hours with no new push. I rationalized this twice ("plausible for the hard cast-bottleneck," "active — no came-to-rest notification") and let it "run." It was NOT running: a one-line worktree check (`git -C <wt> status --short` = clean + Lean-file mtimes stale since the merge) proved it had come to rest after the merge/status message and was idle, awaiting a wake I never sent. The gating leg stalled silently for 2h on my watch. **Rule:** a came-to-rest notification can be missed or not fire as expected, and "no news" ≠ "building." For the CRITICAL-PATH leg specifically, when the branch tip is stale beyond a build's plausible cadence, VERIFY activity directly — `git status` (clean = no WIP = not building) + file mtimes in the agent's worktree — before concluding "deep build." A clean worktree with stale mtimes means re-engage (resume the agent), not wait. The prior lesson said "watch the branch tip, not the idles"; the sharpening: watching the tip is necessary but you must ACT on a stale tip (verify → re-engage), not explain it away as a long build. (Cost: ~2h of zero progress on the one thing gating the headline — pure wasted wall-clock, no work lost.)

**A brief is only an interface once it is PUSHED — verify the shared tip carries it before spawning sub-hands against it (2026-06-30, the #3/#4 brief-fanout):**
genm-r1lower (the gating-leg owner) reported "both sub-hand briefs WRITTEN with pinned interfaces — spawn off @481d8352." I took "written" at face value and spawned genm-hinj (#3) + genm-ubound (#4) pointed at brief paths on that tip. But "written" meant written in genm-r1lower's OWN worktree, never committed/pushed: the foundation push @481d8352 carried the code but not the markdown briefs (the thread dir at that tip had only the H3 card + codex/). genm-ubound did exactly the right thing — checked the tip, found the brief absent, and STOPPED rather than guess the frozen signatures (the binding "if the brief is absent, STOP and message me, do not guess" gate worked perfectly — zero files touched, ~98s/44k-tok clean abort). But it cost a spawn→stop→fix→re-dispatch round-trip on both hands. **Rule:** pin-before-fanout means the interface must be VISIBLE to the consumer, not just authored. Before spawning a sub-hand against a teammate's brief/contract, confirm the artifact is at the shared remote tip the sub-hand will checkout — either the author replies with the post-push SHA, or the controller checks `git ls-tree origin/<branch> -- <brief path>` (or `git show origin/<branch>:<path>`) before spawning. "I wrote it" ≠ "it's on the branch." Generalises the eihd "verify the consumer chart-shape before cone-merging" + the pin-before-fanout lessons: the fanout interface (brief, frozen sig, contract) must be machine-verifiably present at the base the dependents build on. (Cheap because the STOP-don't-guess gate held; would have been expensive — guessed signatures, mismatched wires, an asserted-not-proven Ubound — without it.)

**Locate the non-monomial det factor in the ACTUAL block decomposition before designing a chart to avoid it (2026-06-30, the dead-leaf interior detour):**
The R1-LOWER interior cov wants a pure-monomial Jacobian det. genm-r1lower (chart owner) chose the DEAD-leaf decoder (genBlkFlatStruct) over the already-built LIVE decoder (phiFlatLiveR1) on the belief that the live leaf's free coordinates made the det a polynomial (the "aRead²" factor). That belief was a MISDIAGNOSIS: the live leaf is a chain-UNIT map → its block det is TRIVIALLY 1 (chainUnit_det/eihdF1_abs_det); the aRead² lives in the rate/unit V, NOT the det. The genuine non-monomial factor was always the free-K-core det |det leafKcore|^(r+c) (engineFreeK 0) — which the kLDU K-lens monomializes to (∏q_i)^(r+c) REGARDLESS of leaf. So the dead-leaf detour was unnecessary AND unsound: the dead leaf has no fixed radial anchor → the chart is non-injective (the radial enters only as u•free-E → invariant under (u,readE)↦(λu,readE/λ)), which genm-hinj's NAMED-RISK gate caught (it refused to build a vacuous injOn). Cost: a dead-leaf BchartLDU foundation + an hmap start + two sub-hands' dead-leaf framing (though continuous_kLDU + the obstruction characterization were reusable, and the gates caught it before any unsound atom landed). **Rule:** when choosing a chart architecture to achieve a det property (monomial, nonvanishing, …), first DECOMPOSE the det of the candidate(s) into its actual block factors and locate WHERE the offending factor lives (which block — leaf? frame? K-core?) — verify it against the banked det theorems (here: the eihd det's engineFreeK decomposition), not against an intuition about "free coordinates." A chart-design decision premised on an unverified det-locality claim can send you down a wrong route AND cost a soundness property (injectivity) that the route you abandoned already had. The fix is often to KEEP the richer (built, injective) chart and apply a targeted lens (kLDU on K) to the one block that actually carries the offending factor.

**After every `isolation: worktree` agent spawn, verify the MAIN checkout's branch before committing (2026-06-30, the genm-d1forall spawn-level worktree-collision):**
Spawning a background lean-formaliser `genm-d1forall` with `isolation: worktree` (brief's first step: `git checkout -b genm-d1forall origin/genm-l2asm`) resulted in the branch `genm-d1forall` being created in — and as the HEAD of — the CONTROLLER'S MAIN checkout (`/home/ubuntu/workspace/geometry-of-dln-fibre`), switching it off `expedition/aoyagi-full`. The agent itself got its own locked isolation worktree (so the agent was fine + isolated) — but the main checkout was left on `genm-d1forall`. My next controller commit (UPDATE-525 + Item 107) therefore landed on `genm-d1forall` at a STALE UPDATE-519 synthesis base (the genm-l2asm scaffold's base), and my synthesis Edits failed "File modified since read" (the working tree had been swapped under me). **No data lost** — expedition/aoyagi-full (local + origin) was safe at the last-pushed UPDATE-524, and the cone-merge Lean was independently validated green (8657 jobs, clean #print) — recovery was `git checkout -f expedition/aoyagi-full`, re-checkout the cone-merge files from origin/genm-l2asm, re-apply the docs. **Rule:** this is the banked worktree-collision class recurring at the SPAWN level (not via a teammate's later git-op). After ANY `isolation: worktree` spawn — and ALWAYS immediately before a controller commit — run `git branch --show-current` in the main checkout and confirm it is still `expedition/aoyagi-full`; if not, `git checkout -f expedition/aoyagi-full` first. Treat an unexpected "Edit failed: file modified since read" on a synthesis/doc file as a RED FLAG that the branch may have switched under you — STOP and check the branch, do not just re-Read+retry. (One `git branch` call to detect; a wrong-branch commit on a stale base to miss.)

**ROOT-CAUSE FIX (2026-06-30, the genm-eihdfree RECURRENCE — same class, 2nd time): NEVER put `git checkout -b <name> <base>` in an `isolation: worktree` brief; base via `git reset --hard origin/<base>` instead.** Despite the banked detection-rule above, the collision recurred: I spawned `genm-eihdfree` (isolation:worktree) with a brief whose first step was `git checkout -b genm-eihdfree origin/expedition/genm-r1lower` — which AGAIN switched the MAIN checkout off `expedition/aoyagi-full` onto `genm-eihdfree`, and I did NOT run the post-spawn branch-guard (I went straight to messaging + editing). It surfaced exactly as the banked red flag predicted — an Edit refused "file modified since read" + a grep showed the LIVE tag had reverted to UPDATE-492 — and I recognized it + recovered (expedition/aoyagi-full @3346312d safe = origin; `git checkout expedition/aoyagi-full` restored, no tracked loss). The DEEPER fix than "detect after": the `checkout -b <base>` is the CAUSE — in a shared-`.git` multi-worktree repo, creating+checking-out a branch off a remote base reaches the main checkout. So (a) **briefs for isolation:worktree hands must NOT contain `git checkout -b`** — the isolation worktree already exists on its own branch; to base it on a specific branch, instruct `git fetch origin && git reset --hard origin/<base>` (this moves ONLY the worktree's own branch, never the main checkout); (b) the agent then `git push origin HEAD:<clean-name>` to publish under a tidy remote name without a local `checkout -b`; (c) the post-spawn `git branch --show-current` in the main checkout is STILL mandatory (defense-in-depth) — I skipped it and paid a recovery cycle. Note the collision also leaves the agent's OWN worktree on the spawn-time base (here expedition/aoyagi-full, MISSING the genm-r1lower eihd machinery), so the agent must re-base anyway — another reason `reset --hard origin/<base>` belongs in the brief from the start. (Two occurrences now; this is the standing brief-template rule, not a per-incident note.)

## 2026-07-06 — aggregator edit must be COMMITTED, not just present in the working tree (integration slip)
Integrating a landed tide, I `Edit`ed `DLNFibre.lean` to wire 2 new banked bricks, green-gated the full build
(which read the working-tree edit → green), then committed with `git add <docs only>` — the `DLNFibre.lean`
edit stayed UNCOMMITTED and did NOT push. Result: the brick FILES landed on canonical (they were in committed
brick-file commits) but the aggregator did NOT import them → orphaned (not compiled by `lake build DLNFibre`,
no green-gate coverage). Caught one tide later when the next merge's aggregator tail lacked the imports.
**Rule:** after wiring the aggregator, `git add lean/DLNFibre.lean` explicitly (or `git add -A lean/`) and
**verify `git show HEAD -- lean/DLNFibre.lean` contains the import** before pushing. A green full-build proves
the working tree is consistent, NOT that the edit is committed. Prefer `git status --porcelain` = clean (no
lingering ` M lean/DLNFibre.lean`) before every integration push.

## 2026-07-06 — teammates must NOT touch the main checkout (2nd incident; recovery was clean because canonical is push-target-addressed)
`phip1` (an isolation:worktree formaliser) "accidentally moved the main checkout onto a stray local
`genm-phiexpl-p1`, then restored it to `genm-sjbase`" — i.e. it ran git ops in the controller's main checkout
(`/home/ubuntu/workspace/geometry-of-dln-fibre`), not just its own worktree. Consequence: the main checkout
drifted onto the wrong local branch, and the controller's subsequent `ff-only` + doc commit landed on that
stray local pointer. **No canonical corruption** — the controller pushes via `git push origin
HEAD:expedition/aoyagi-full` (push-target-addressed, independent of local branch name), so origin stayed
correct; the damage was a stale/contaminated LOCAL pointer, fixed with `git checkout -B expedition/aoyagi-full
origin/expedition/aoyagi-full` + `git branch -f genm-sjbase origin/genm-sjbase`. **Prevention:** (1) every
teammate brief must say "work ONLY in your assigned worktree; NEVER `cd` to or run git in the main checkout";
(2) controller keeps pushing via `HEAD:expedition/aoyagi-full` (never a bare `git push` that assumes the local
branch), and verifies `git rev-parse --abbrev-ref HEAD` = `expedition/aoyagi-full` at the START of each
integration. This is the 2nd such incident (the 1st was a prior session leaving the checkout on genm-inj-injon).

## 2026-07-06 — do NOT re-charge an agent on ambiguous 0-procs; wait for the completion notification (caused benign duplication)
I diagnosed `sjpeel2` as stalled (pgrep-by-agent-ID = 0 live procs + intermediate "failed" build-markers in its
output + no pushed branch) and re-charged a duplicate (`sjpeel3`). But `sjpeel2` was STILL RUNNING — 0 matching
procs is the norm during an agent's reasoning/reading phase (the agent ID isn't in a lean/git proc cmdline then;
verified twice — phip3 also showed 0-procs while completing). Both agents then built the same c.o.v. base
concurrently. **No work lost** (sjpeel3 pushed incrementally per its brief; sjpeel2's uncommitted output was
preserved to a branch) and the outputs were complementary, but effort was wasted. **Rules:** (1) `pgrep 'agentID'`
= 0 does NOT mean dead — it means "not running a lean/git subprocess right now"; distinguish via worktree/.lake
activity + the presence of ANY lean procs, not the ID-match. (2) "failed" in an agent's JSONL output is usually an
intermediate build attempt, not a death. (3) The reliable death/completion signal is the harness task-notification —
WAIT for it before re-charging. (4) If a genuine stall must be assumed (no notification after a long idle), prefer
resuming the SAME agent via SendMessage over spawning a fresh duplicate.

## 2026-07-06 — a `lake` orchestrator's low CPU is NOT a stall; and stop over-diagnosing builds (2nd misjudgment)
I killed the phip4 full-`DLNFibre` green-gate reading its `lake` proc's low CPU (1m52s over 46min elapsed) as
"stalled." WRONG: the `lake` orchestrator legitimately WAITS (on the global semaphore) + delegates CPU to `lean`
WORKER subprocesses — its own CPU stays low even while the build progresses. Its workers were in fact active (6GB,
recent, high-CPU). The 46min was semaphore-WAIT under heavy contention (I had 2–3 concurrent full-lib green-gates +
foreign builds sharing ~6 slots), then it got slots + compiled. I killed a progressing build (no work lost — the
tide was committed — but wasteful). **Rules:** (1) judge a `lake`/`scripts/lb` build's liveness by its `lean`
WORKER procs' CPU/etime, NOT the orchestrator's. (2) High elapsed + low orchestrator CPU = waiting on the
semaphore (contention), which is NORMAL and SAFE — not a stall. (3) **Cadence: do not run a full `scripts/lb
DLNFibre` green-gate per integration when 2 formaliser builds are already live** — it triggers 40+ min semaphore
waits. Verify a tide via `scripts/lb <Module>` (module build) + force-`#print axioms` + `rg` new top-level names vs
siblings; batch ONE full-lib gate when the farm is clear. (4) This is the 2nd build-status misjudgment in one
session (after sjpeel2 "stalled"→duplication) — the meta-lesson: be conservative about declaring a build
stalled/dead; wait for the harness notification; never kill/re-charge on ambiguous signals.

## Fresh lean-formalisers MUST be spawned with `isolation: worktree` (2026-07-07, atombuild incident)
Spawning a fresh lean-formaliser via the Agent tool WITHOUT `isolation: worktree` runs it in the
controller's MAIN checkout cwd. If its setup does `git checkout -b <branch>` (as instructed), it SWITCHES
THE MAIN CHECKOUT's branch — hijacking the controller checkout (observed: main checkout → genm-atom
@2e334df6, working tree reverted to old peel-stack content). The loop-prompt already mandates
`isolation: worktree` for fresh formalisers; I violated it for `atombuild`.
**Why:** the controller must stay on expedition/aoyagi-full in the main checkout to integrate; a formaliser
that switches that branch breaks the controller's workflow (this is the #45 risk, now realized on MY branch).
**How to apply:** (a) ALWAYS pass `isolation: worktree` when spawning a fresh lean-formaliser via Agent;
(b) instruct teammates to `git worktree add` / operate in their OWN worktree, never a bare `git checkout -b`
in a shared cwd; (c) recovery = TaskStop the mis-homed agent → `git checkout expedition/aoyagi-full` (canonical
is safe on origin; remove any duplicate-untracked files blocking the switch first, preserving genuinely-new
untracked artefacts) → re-spawn with isolation. Pen-and-paper teammates (docs-only, no branch ops) sharing the
main checkout is tolerable, but they must NOT run git branch operations there.

## A reduction-to-germs' germ SATISFIABILITY is load-bearing — not just the faithful implication (2026-07-07)
Two "reduce the last sorry to germs/peels" steps this expedition were banked + (for hstep2) reviewer-PASSED
as FAITHFUL implications (`germs ⟹ goal`), yet had germs that were UNSATISFIABLE or on the WRONG route —
caught only when the NEXT tide tried to BUILD the germ:
- **hstep2**: `deepest_diffeo_bridge_gen_impl` (single-Ψ-step, NAIVE coreAbsorb) — faithful implication, but
  the germ `huntwist` is unsatisfiable (naive cores `S^naive` ≠ honest `S^conj` at first order; a left-shear
  can't bridge them). Fix: the two-step `Step Θ ∘ Step Ψ_conj` (mirror the accepted L2). Caught by
  hstep2chain's satisfiability numeric + the repo's own L2 docstring + Codex.
- **R1-UPPER**: the "Gram c.o.v. `Γ↦Γ·Q_b`" anisotropy-removal — the atom/dead route (produces the full-space
  `det^{−p/2}` wall), not the pure route. Caught by sjcarrier (algebra + certs + Codex).
**Why:** a reduction can be a faithful *sufficient* condition whose hypothesis cannot be met (vacuous) or is on
a dead route — the implication-check (does discharging the germs close the goal?) does NOT catch this.
**How to apply:** when banking a reduction-to-germs, the immediately-next step (or the reviewer) MUST check the
germ SATISFIABILITY / route-alignment (a small numeric discriminator or design pass) BEFORE committing the big
germ-build; a reviewer verifying a reduction should check BOTH faithfulness AND satisfiability. The design-first
/ honest-partial discipline (refuse to build the germ on an unsatisfiable/wrong-route target) is what made both
catches cheap (a scoping tide, not a wasted ~300-line build).

## A teammate's "isolated green" can be a STALE-OLEAN cache hit masking a parse error — controller MUST force-recompile on integration (2026-07-07)
`hstep2germs2` reported "isolated green (2677 jobs)" for `DeepestPsiSplitGenMoved.lean`, but on integration the
FULL build hit a **parse error** (`unexpected token 'omit'; expected 'lemma'`) — the module never actually
compiled with that content. Root cause: a `/-- … -/` docstring placed BEFORE `omit [Inst] in` (the docstring has
no declaration to attach to); the correct order is `omit [Inst] in` THEN the docstring THEN the `theorem` (cf.
the working `S1QuasiSplit`/`OrbitCodim`). The teammate's reported green was a shared-store olean cache hit
(content-hash keyed) that bypassed re-parsing — exactly the `lean/CLAUDE.md` stale-olean hazard.
**How to apply:** on integrating ANY tide, the controller force-recompiles (touch the module / green-gate the
FULL `scripts/lb DLNFibre`, never trust the teammate's reported isolated exit-0) — for a new leaf module,
`touch <module> && scripts/lb <module>` reproduces the true parse/elaboration state. This is a companion to the
`#print axioms`-not-exit-status rule: exit-0 (even a teammate's) masks BOTH a persisted `sorryAx` AND a persisted
parse error via a stale olean. The fix was a mechanical 2-line reorder (docstring after `omit`), banked into the
merge commit; the teammate's math was sound.

## A connection-cutoff "death" may RESURRECT + complete — check the branch before re-charging a duplicate (2026-07-08)
`sjbuild` reported "API Error: Connection closed mid-response" (task status: completed) with a `<1k`-token
stub result + 0 pushed commits, so the controller treated it as dead and re-charged `sjbuild2` (identical
mission). But `sjbuild` in fact RESUMED and ran to completion, producing a full DUPLICATE scaffold
(`RouteMSJDecoratedRec.lean` vs sjbuild2's `RouteMSJDecorated.lean`) — a wasted heavy slot.
**How to apply:** a connection-cutoff completion is NOT necessarily a death — before re-charging an
identical mission, (a) `git fetch` + check the agent's branch for late pushes, and (b) prefer resuming via
SendMessage over spawning a duplicate when the prior agent may still hold context. Salvage value here: the
resurrected agent's independent reviewer CAUGHT a real overclaim in the duplicate's STEP-0 (a "GATE PASS"
doc-claim that was an idealized-single-divisor value, not the actual multi-divisor bridge — the bridge is a
numerically-true INEQUALITY but an OPEN Lean obligation). Second lesson: a design-pass "GATE PASS" doc-claim
is NOT a Lean theorem — verify whether the gate's content is discharged or is a downstream proof obligation.
Also (recurring): sjbuild `cd`'d into the controller's main checkout for builds (isolation break) + left a
stray module + `.lake`; it `rm`'d them, controller verified clean. Isolation-break remains the top teammate
hazard — brief every heavy tide to check `git rev-parse --show-toplevel` is a worktree path.

## Route-adjudication briefs must pose the NEUTRAL math question — anchoring on a route's machinery biases the decorrelated Codex (2026-07-08)
`r1carrier` certified the R1-UPPER `peelZBlock` step RESEARCH-GRADE (a matrix-product Plücker principalisation
Mathlib lacks) — and its decorrelated Codex AGREED. This drove an erroneous operator build-vs-cite escalation
(#59). `r1flip` (fresh, un-anchored) FLIPPED it: the obstruction is the ATOM route (the Gram CoV `Δ=Γ·Qb`,
`det(QbQbᵀ)^{−p/2}`), which the PURE R-BLOWUP route (coordinate radial + det-1 unit Schur-clear = the banked
`corankStep`) NEVER forms; r1carrier's decisive dense-torus witness is a POSITIVE-loss point the RLCT resolution
never touches (Aoyagi Thm 4). ROOT CAUSE: r1carrier's Codex prompt posed "map `‖C·Qp+Γ·Qb‖²` to the shape
*required by the regime atoms (A)/(B)*" — which IS the Gram CoV, so the "decorrelated" Codex was ANCHORED on the
atom route and could only confirm the atom-route wall. (The anchoring came partly from the controller's brief,
which framed (B) as "bounded composition of the banked regime atoms OR res-of-sing" — atom-referencing.)
**How to apply:** for a bounded-vs-wall / build-vs-cite route adjudication, pose the decorrelated Codex the
NEUTRAL math question (does object X have property Y?), NEVER "map X to the shape required by [route-R
machinery]" — that pre-commits to route R. Cross-check any "research-grade/wall" verdict against the EARLIER
route consensus before escalating to the operator (here #55/r1decorated/pure-vs-atom-adj already classed the
Gram route as the avoidable atom route). The atom-vs-pure route confusion has now recurred 3×
(sjcarrier Gram-c.o.v.; hstep2 single-step; this) — atom-route framing is the persistent R1-UPPER confound.
Cost here: bounded (2 pen-and-paper passes + one flip-flopped operator note, no bad Lean, no wasted heavy build).

---

## A teammate's "thread complete" can be STALE when a controller continue-directive crossed it — verify LIVE agent state, not just its last message or branch code, before charging a replacement (2026-07-08, hC / hcstep6 duplicate)
`hstep2hc` sent "thread complete + recommend a fresh tide for the hC step-6 sub-gap." One tick earlier I had SendMessage'd it "CONTINUE into the sub-gap." The continue-directive REACTIVATED it (it resumed grinding hC), but its "thread complete" message — sent before/around my directive — made me read it as wound-down. I charged a fresh tide (`hcstep6`) for the same hC sub-gap, in the same suggested module. DUPLICATE: two hands on one lemma.
**Caught + resolved cheaply:** `hstep2hc`'s next checkpoint (step-A green, same filename) revealed it was alive + further along. I STOPPED `hcstep6` (it had pushed nothing — no branch, no conflict, no lost work) and confirmed `hstep2hc` as sole owner. Cost: near-zero (one just-started tide stopped before any push).
**Why the branch-check didn't save me:** I DID check the branch for sub-gap code before charging `hcstep6` and found none — but that was a RACE (hstep2hc hadn't pushed step-A yet), and the real signal was that the agent was still RUNNING (reactivated), which a branch-code grep doesn't show.
**How to apply:** before charging a replacement/fresh tide for work a teammate reported "done/handed-off," if you EVER sent that teammate a continue/resume directive that could still be in flight, treat its running state as UNKNOWN — verify it's actually stopped (idle_notification / TaskStop-confirms-not-running / an explicit "standing down" like hderiv0's), NOT just "its last narrative message said done" and NOT just "its branch has no code yet." A crossed continue-directive + a stale completion message = live duplicate risk. When in doubt, resume-the-owner (SendMessage) rather than spawn fresh. Refines the earlier resurrected-agent lesson (check branch before duplicating) — add: check LIVENESS, and branch-code-absence can be a race not a fact.

---

## `scripts/lb` has a GLOBAL worker cap — >2 concurrent heavy build-tides thrash (validates ≤2-heavy) (2026-07-08, hcfinish contention)
`hcfinish` reported its incremental builds spiking from ~5-7 s to 12+ min (one killed at ~12 min) when 3 build-load
hands ran concurrently (hcfinish + dgelegbuild [both heavy formaliser builds] + a reviewer's force-recompile
build-check). Cause: `scripts/lb` shares a GLOBAL worker pool across all worktrees/tides — N concurrent heavy builds
each get ~pool/N workers, so build latency scales ~linearly with concurrent heavy builds. A reindex-heavy tide that
needs several build-debug iterations (1-3 tries/lemma) becomes impractical at 12 min/build.
**How to apply:** hold the ≤2-concurrent-heavy-BUILD discipline STRICTLY (it's not just coordination overhead — it's a
hard throughput constraint). Count build-load, not just "tides": a `reviewer`'s forced-recompile build-check IS a heavy
build (transient, but it counts while running); a `scout`/`pen-and-paper` (read-only + exact-algebra + Codex) is LIGHT
(minimal `lb` load). When a CRITICAL-PATH build needs a calm window: (i) hold the controller's own green-gates (a full
DLNFibre aggregate build is heavy) until it lands, (ii) charge NO new heavy tides, (iii) let transient heavy hands
(reviewer builds) finish, (iv) if still contended, actively pause/stop a non-critical competing heavy tide (only if it
has PUSHED its progress — else you lose its work). Prioritize the near-done critical-path build.

---

## Crossed-handoff duplicate (recurred 3×): a teammate "recommends a fresh tide" but keeps banking — base the fresh tide on the teammate's LATEST branch, not canonical (2026-07-08, geleg1/geleg8)
Pattern (hcfinish/hcfin2, hstep2hc/hcstep6, now geleg1/geleg8): a marathon teammate says "handing off — recommend a fresh tide," so the controller charges a fresh tide off CANONICAL; but the teammate then banks one more increment (its "handoff" isn't a hard stop), so the fresh tide re-derives what the teammate just banked = duplicate. Each caught + resolved cheaply, but avoidable.
**Fix (applied, works):** when a teammate recommends a fresh tide WHILE actively banking increments, do NOT base the fresh tide on canonical — base it on the **teammate's LATEST branch/commit** (`git checkout -B <fresh> origin/<teammate-branch>@<latest>`), so any crossed continuation is BUILT-UPON, not duplicated; and explicitly STAND THE TEAMMATE DOWN ("do not resume; the fresh tide owns X") in the same tick. Alternative (slower): wait one cycle for the teammate to confirm idle + no-new-push before charging. Refines the earlier liveness lesson: it's not just "verify stopped" — it's "base the replacement on the latest banked state so a race is harmless." Cost across all 3: near-zero (redirects/stops, no lost work, no bad Lean).

---

## `Equiv.Set.sumCompl`-based role equivs blow up `whnf` in `Homeomorph`/`≃ₜ` constructions — use `Equiv.ofBijective` (2026-07-09, geleg1 piece iv)
Building the general-L role-partition index equiv (`roleEquivGen`) via the complement-subtype route (`regCoreEmbGen` + `Equiv.ofInjective`/`Set.sumCompl`/`sumAssoc`) is fine for the plain `Equiv`, BUT feeding it into a `Homeomorph` (`≃ₜ`, e.g. `splitHomeoGen`) blows up `whnf`: `sumCompl.symm` forces a **non-computing Classical range-membership decision** at every reduction, and heartbeats bumped even to 1.6M still time out.
**Fix (the L=2 shape):** build the `≃ₜ`/`Equiv` with an EXPLICIT forward map + `Equiv.ofBijective` (or a hand-written `invFun`), so `symm` is a single cheap `invFun` application, not a Classical membership decision. Keep the `sumCompl` route (if you must) confined to the plain `Equiv` layer where whnf isn't forced; never let it reach a topology/measure construction that reduces the coercion. Reusable for ANY chart/reindex `≃ₜ` over a role/complement split (relevant to both ≥-leg strands). Cost when it bites: silent heartbeat timeouts that look like "needs more heartbeats" but are actually the wrong equiv shape.
