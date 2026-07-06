# Brief — `rlct-foundation` expedition

## Central question

> Replace the thin **cited scalar** in the DLN payoff (`rlct = ½·codim`, today carried by an opaque
> interface) with a **real RLCT foundation** — the zeta-pole invariant `RLCTPair = (λ, m)` defined in
> honest mathematical terms — behind a **machine-enforced citation cordon** that makes "what is fully
> formalised vs cited" a *checkable, forget-proof* invariant of the repo. Connect the already-formalised
> fibre geometry (codim, components) to the RLCT result across that clean proved/cited boundary, so the
> payoff reads mathematically with the genuinely-analytic monuments isolated. Fold in the one open geometry
> edge (non-monotone fibre `θ`, Gap 1).

This is the last thin cited interface in the project's ultimate payoff (the SLT "DLNs are mildly singular"
result), so it's the highest-leverage correctness gain left. It is also the most **monument-adjacent** work
we've done — real-analysis (zeta, Mellin, meromorphic continuation, resolution) — so the discipline is
paramount: **name = content**, Proved/Cited separated, and (rung 1) the cordon that enforces it.

Grounding: ROADMAP § *Bundle 4b* (the planned RLCT programme, with the build/cite split + module layout) and
§ *Open edges* (Gap 1). Base off `dev` @ `10edbdc3` (after #20/#21/#22). Recon-first (the domain is new).

---

## Rung 1 — the citation cordon (do FIRST, battle-test, then graduate to policy)

**This rung is a software / UX problem, not a math one — and the users are AI agents (formalisers,
controller) as much as humans (operator, reviewers).** Design it as such: robust, forget-proof, discoverable,
with actionable output and adversarial tests. It gates every later rung.

### The mechanism (the "accounted-axioms" cordon)

Cited external results are Lean `axiom`s (so the kernel *auto-tracks* every dependency — nothing to forget),
tagged and quarantined; a filtered report over Lean's own `collectAxioms` (the `#print axioms` engine) is the
gate.

- **`@[cited "<source>"]`** attribute — a parametric tag carrying the citation source string as *structured
  data* (not a docstring convention), so the manifest is auto-derived. Applied to each cited `axiom`.
- **Core analysis** (one reusable module; DRY): for a declaration, `collectAxioms` its transitive axiom set,
  then subtract (i) the **foundational allowlist** `{propext, Classical.choice, Quot.sound}` (explicit +
  extensible) and (ii) all `@[cited]`-tagged axioms. The remainder is the **UNACCOUNTED** set. Empty ⟺ the
  declaration is *proved, modulo only declared citations*.
- **Two frontends over the one core:**
  - `#audit_cited foo` — an in-file command (mirrors `#print axioms`, familiar) showing `foo`'s unaccounted
    axioms + its cited dependencies, right where you're proving. The formaliser's inner loop.
  - `scripts/cited` / `lake exe cited-audit` — the repo gate. **Enforcing (nonzero exit on violation)**,
    unlike the informational `scripts/sorries`. Runs three independent checks:
    1. **Unaccounted = ∅** over *all* public declarations (any theorem resting on an untagged axiom fails).
    2. **Location + tagging:** every `axiom` in `DLNFibre/**` is `@[cited]` *and* lives in an allowlisted
       `*/Cited.lean` file (a stray or untagged axiom anywhere fails).
    3. **Manifest** (`--manifest`): derive, per headline, which `@[cited]` axioms it uses (→ the README
       status 🔵 column + each `Cited.lean` header), from the same `collectAxioms` output.
- **Why forget-proof:** forgetting the tag does not *hide* a cite — the raw `collectAxioms` still sees the
  axiom, so it lands in UNACCOUNTED → the gate goes red → you are forced to tag+locate it (or prove it).
  Completeness is the kernel's; the tag only *accounts*.

### SWE / UX requirements (bake these in)

- **Fail loud + actionable:** each violation states the fix verbatim ("axiom `X` is unaccounted — prove it,
  or `@[cited \"…\"]` it and move to `…/Cited.lean`").
- **Machine-parseable + human-readable:** a one-line structured summary (`UNACCOUNTED=0 CITED=3
  LOCATION_VIOLATIONS=0`) for AI users to grep, plus a detailed colored listing (like `scripts/sorries`).
- **Deterministic** output (stable ordering) for CI + agents. **Discoverable:** documented in `lean/CLAUDE.md`
  next to `scripts/sorries`, and (deliverable) a policy doc.
- **Separation of concerns:** unaccounted / location+tag / manifest are distinct modes.
- **Battle-test (the crux — a cordon unproven to catch violations is worthless):** adversarial fixtures with
  known-expected verdicts —
  (a) a fully-proved decl → FORMALISED;
  (b) a decl using a tagged+located cite → CITED[source];
  (c) a decl using an **untagged** axiom → UNACCOUNTED, gate **fails**;
  (d) an axiom **outside** `Cited.lean` (or untagged) → LOCATION violation, gate **fails**;
  (e) a *transitive* cite (A depends on B which is cited) → still CITED (kernel transitivity).
  These fixtures + their expected outputs are part of rung 1, run in the gate.

### Deliverables (rung 1)
The `@[cited]` attribute + the `collectAxioms`-based core + both frontends + the adversarial test suite +
gate-wiring alongside `scripts/sorries`; **and** `docs/policies/citation-cordon.md` (the mechanism, the
declare-a-cite workflow, the invariants, the rationale — forget-proofness). Retrofit the existing
`RlctRealInterface` cite onto the cordon as the first real user.

---

## The RLCT build ladder (recon-gated; BUILD the foothills, CITE the mountains)

**Recon first** (domain is new — real analysis): size Mathlib's depth for Mellin (`MellinTransform` present),
`MeromorphicAt`/`MeromorphicOn` (present), integration + change-of-variables, `AnalyticAt`. Kill-questions:
how far does the buildable middle reach before the resolution cite? is coord-change invariance buildable or
does it need heavy analytic CoV? does the pole-order `m` connect to anything we have, or is it purely Aoyagi?

- **Zeta + definition:** `ζ_x(z) = ∫_U K^z φ` on its convergence region (Mathlib integration); `RLCTPair K x =
  (λ, m)` = the largest pole on the negative real axis and its order. **The definition** (per the ROADMAP
  decision — zeta-pole, which gives the honest multiplicity `m`).
- **BUILD (detail-at-scale — don't flinch at "looks analytic"; it's established maths, decomposable):** the
  1-D Mellin continuation `∫ t^{az+b} φ(t) dt` (elementary, gamma-type poles); the product **normal-crossing
  pole formula** `λ = min_{aᵢ>0}(bᵢ+1)/aᵢ`, `m = #minimisers` (denominator `2aᵢ` for squared losses); germ +
  unit invariance; the smooth **quadratic block** `λ_0(x₁²+…+x_c²) = c/2`; coord-change invariance (recon-gated).
- **CITE (monuments — via the rung-1 cordon, in `Cited.lean`):** meromorphic continuation of `ζ` for an
  *arbitrary* real-analytic germ; resolution / principalization existence; pole-order-from-resolution;
  zeta-pole ↔ integrability-threshold ↔ volume-asymptotic equivalence. **DLN cites:** Aoyagi's `λ`
  computation; Watanabe's universal upper bound.
- **DLN germ link:** `K_B(A) = ‖mult(A) − B‖_F²`; prove `K_B⁻¹(0) = mult⁻¹(B)`; connect to the codimension
  (reuse the already-Proved algebraic `λ = ½·codim` matching `two_lambda_eq_codimFormula` +
  `codimRepCanonical_fibre_eq_two_aoyagiLambda`, and the real↔complex transfer — rewired onto the new object).
- **Rewire the payoff** to read: `rlct(K_B) = ½·codim mult⁻¹(B)`, via [built] Aoyagi's algebraic matching +
  [cited] Watanabe-upper + [cited] Aoyagi/singular-locus-lower, the cited bounds named as analytic theorems
  **about the real DLN germ** — none of it a bare scalar in the DLN statement.

Module layout (ROADMAP 4b): `Core/Analysis/RLCT/{Basic,Zeta,Integrability,NormalCrossing,Cited}.lean`
(generic) + `DLN/RLCT/{AoyagiCited,Payoff}.lean` (DLN cite + transport).

---

## Gap 1 (folded in, runs parallel — pure geometry, no cite)

Non-monotone fibre `θ`: promote the already-arbitrary-`d` codim fibre-vs-`Σ` shift to a **component-count**
fibration transfer (the fibre over the rank-`r` normal form is Zariski-locally the irreducible exact-rank-`r`
stratum × the shifted zero-product problem, so `#comp(mult⁻¹(B)) = numTop(d,r)`), dropping `Monotone d`. Plus
the one-corollary arbitrary-`d` rank-locus count. **No new mathematics, no cite.** Greens the geometry side of
the README status table. Independent of the RLCT work (RLCT uses codim, already arbitrary-`d`), so it can run
alongside on its own thread.

---

## Caveats (carry from rung 0)
- **`m ≠ θ`** — the RLCT multiplicity (pole order) and the top-component count are *proved distinct* in general
  (`DLN/Aoyagi/ThetaOrderDistinction`; diverge for `|δ| ≥ 2`). Never claim the RLCT multiplicity is `θ`. (A
  light reminder — the θ story stays geometric, the `m` story analytic; the distinction is Proved, not cited.)
- **Domain risk:** real-analysis is new terrain vs the prior algebra — recon-first, and scope the first RLCT
  slice tight (value + core invariances + the quadratic block) once the cordon is battle-tested.

## Closing criterion
1. **Cordon** enforced in the build gate (`scripts/cited` nonzero-on-violation), battle-tested, `#audit_cited`
   available, `docs/policies/citation-cordon.md` landed, existing cites retrofitted onto it.
2. **RLCT foundation** built to the honest boundary — `RLCTPair` zeta-pole def + the buildable ladder — with
   the cordon **green** (UNACCOUNTED = ∅; every cite `@[cited]` + located).
3. **Payoff rewired** to read mathematically, cited bounds isolated over the real germ.
4. **Gap 1** closed (non-monotone fibre `θ`).
5. README status table + ROADMAP updated (per DA6 — folded into the one PR before the merge signal).
