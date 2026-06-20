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
