# Synthesis — `theta-components` expedition

Successor to the codim hero expedition. Central question: the order **θ** + the full bundle content of
**Lemma 4.6 (scope B)**, to bedrock. Opened 2026-06-25.

## Status: kickoff threads returned (2 decorrelated certificates + controller assessment)

### Headline (RESOLVED, thread 03 + controller-verified): three distinct θ-invariants; Aoyagi correct; LR's printed rlcm off by one

Thread 01 (witness seat) reached a CANDIDATE "Aoyagi erred" verdict; thread 03 (obstruction seat,
decorrelated + Codex) **REFUTED it**, and the controller verified the key claim against LR `main.tex`. (The
decorrelated dialectic worked exactly as intended — the confident headline was wrong; the skeptical seat
caught it.) Settled picture — **three distinct invariants**, agreeing iff `|δ|≤1`, diverging for `|δ|≥2`
(witness `(2,2,2,2,2)` r=0):

| invariant | formula | what it is | (2,2,2,2,2) r=0 |
|---|---|---|---|
| `cTheta` (Lean / LR `k`) | `C(m,\|δ\|)` | # top-dim irreducible components | 6 ✓ correct |
| rlcm / pole order (Aoyagi) | `a(ℓ−a)+1` | the SLT multiplicity | 5 ✓ correct |
| LR's *printed* rlcm (`:1895`) | `a(ℓ−a)` | = θ−1, the log-log coefficient | 4 ✗ off by one |

- **Aoyagi (2023) is NOT in error.** `a(ℓ−a)+1` is the genuine pole order — internally consistent (Thm 1 /
  Thm 2 / equal-width Example agree) and cross-checked against the peer-reviewed Aoyagi–Watanabe (2005)
  reduced-rank-regression multiplicity (1127 cases, 0 mismatch).
- **`cTheta = C(m,|δ|)` is correct as a component count.** LR's own Remark (`:1934`) says there is "no simple
  relationship" between rlcm and the component count `k` — so #components ≠ the order; genuinely different
  invariants (general counterexample `F=xy(x−y)`: 3 components, pole order 1).
- **LR's *printed* rlcm (`:1895`) is off by one.** LR define (`:1808`) `rlcm ∈ ℕ` = the order of the largest
  pole (≥1), but the printed `m²{S̃/m}(1−{S̃/m})` = `a(ℓ−a)` is **0 at `|δ|=0`** — impossible for a pole
  order. The correct rlcm, by their own definition, is `a(ℓ−a)+1` = Aoyagi's; the printed expression is the
  log-log coefficient θ−1. **Controller-verified against the source** (certificate-strength via the
  definition-vs-formula contradiction; pinpointing the dropped `+1` in their resolution proof is the one open
  sub-question).
- **The `rlct = codim/2` (λ) story is UNAFFECTED** — λ agrees exactly; this touches only the secondary
  multiplicity. **This resolves #54:** the Lean `cTheta` is the correct component count; the "θ" confusion
  was conflating the component count with the pole order.

### Build terrain (thread 02, scout)

- **Σ̄^r θ-count AND component↔Kostant bijection: PROVED unconditionally** (`numTop_eq_ncard_topComponents`,
  `bijOn_partitionIdeal_topComponents`, `≃o` to Mathlib `irreducibleComponents`). BEDROCK.
- **The new content = the FIBRE `mult⁻¹(B)` θ** (for B≠0 the fibre isn't `G_d`-stable; orbit machinery
  doesn't transfer directly). Two routes:
  - **(A) cheap** — transport the proved Σ̄^r bijection through the existing chart `e` via
    `orderIsoOfPrime` (minimal primes survive localization; reducedness NOT needed for *counting*).
    **Kill-condition:** every top-dim component of `mult⁻¹(E)` meets the `{detΔ≠0}` pivot chart ⟹ fibre-θ ≈
    1–3 light lemmas, the reducedness wall is OFF the θ path.
  - **(B) full reduced bundle** — needs the reducedness wall (R2-3b, `fibreGenIdeal` radical; certified
    true thread 16, Lean-unproven, ≥2-module AG sub-project) + a hand-built scheme bundle API (no Mathlib
    `FiberBundle` at scheme level) + smoothness (GLOBAL smoothness is FALSE — fibre singular at E; only
    generic/per-chart).
- **Decisive next computation (commissioned, thread 04):** primary-decompose `fibreGenIdeal` on
  `(2,2,2),r=1`, `(2,2,2,2),r=1`; per top-dim component test `detΔ` non-zero-divisor ⟹ does fibre-θ need the wall?

## Strategic read (controller)

The expedition has three separable pieces, in rough dependency/value order:
1. **Fibre θ-count + bijection (scope-2 backbone)** — likely **cheap via the (A) decoupling** (transport
   through `e`), avoiding the reducedness wall *if* the kill-condition holds. High-value, near-term.
2. **The θ-formula findings (RESOLVED)** — a precision contribution: (i) `cTheta`/component count and the
   rlcm/pole order are *distinct* invariants (formalise both, named distinctly — never conflate); (ii) LR's
   *printed* rlcm is off by one (correct rlcm = `a(ℓ−a)+1`). Does not touch the codim/λ results. #54 resolved.
3. **The full bundle + smoothness (scope-3, "rest of Lemma 4.6 B")** — the heavy lift: reducedness wall +
   hand-built bundle + smooth-locus scoping. This is where the consolidation design goal lives; it is a
   **strict scope increase, not a free consolidation** — `e` likely stays a load-bearing lemma.

Sequencing: the θ-formula question is settled (above). The (A) kill-condition (thread 04) decides whether the
fibre-θ backbone is cheap; then the bundle/smoothness heavy lift. The off-by-one warrants surfacing to the
operator (a precision finding on the paper being formalised — possible erratum/correspondence; operator call).

## Threads
- **01** θ adjudication (pen-and-paper) — DONE; certificate `threads/01-theta-adjudication/findings.md`.
  (Candidate verdict "Aoyagi erred" — REFUTED by thread 03.)
- **02** terrain map (scout) — DONE; `threads/02-terrain-map/findings.md`.
- **03** H1-vs-H2 stress-test (pen-and-paper, obstruction) — DONE; H1 REFUTED, three distinct invariants, LR
  printed rlcm off-by-one (controller-verified vs `main.tex`). Certificate `threads/03-theta-h1-h2/findings.md`.
- **04** (A)-decoupling kill-condition + `fibreGenIdeal` primary decomposition — DONE; **kill-condition HOLDS
  (`detΔ ≡ 1` on the whole fibre, a one-line definitional fact)** ⟹ Route A open, reducedness wall OFF the θ
  path. Fibre #top = `cTheta(d−r) = C(m,|δ|)` verified on 6 Singular cases. Certificate
  `threads/04-fibre-theta-route/findings.md`.

## The fibre-θ build plan (Route A — de-risked, next tide)

1. **`detΔ_unit_on_fibre`** — `detΔ − 1 ∈ fibreGenIdeal` (one-liner: `mem_fibre` + `chartΔ_normalForm`;
   general — any `d`, `r`, ring). The entry lemma.
2. **Transport** the PROVED Σ̄^r bijection `bijOn_partitionIdeal_topComponents` through the chart `e`
   (`Core.ChartLocalizedAlgEquiv`) via `IsLocalization.orderIsoOfPrime` — reducedness-free, since `detΔ` is a
   unit on `O(fibre)`. Gives: fibre top-components ↔ Σ^r top-components.
3. **Shift-width identity** `numTop(fibre d E_r) = cTheta(d−r)` — grounded in the PROVED
   `numTop_eq_ncard_topComponents` (Σ̄^r) + the block-triangular shift (rank-`r` fibre ≅ affine stratum ×
   zero-product locus of `d−r`; the affine factor adds no components). The one substantive input — check if the
   engine already has a `numTop` rank-shift (analogous to the proved `cCodim d r = cValue(d−r)`); if not, it is
   LR Lemma 4.5, a named input (commission a pen-and-paper cert if it blocks the tide).

After the fibre-θ count + bijection land (scope-2 backbone): the **heavy lift** — the full reduced bundle +
smoothness (scope-3, "rest of Lemma 4.6 B"), which DOES need the reducedness wall (R2-3b) + a hand-built scheme
bundle + smooth-locus scoping.

## Progress + recalibration (2026-06-25, thread 05)

**LANDED** (sorry-free, axiom-clean, aggregated, library green 3767):
- `Core.FibreDetUnit` — `ΔPdeep_sub_one_mem_fibreGenIdeal` (detΔ−1 ∈ fibreGenIdeal, general / scheme-level at
  the generator ideal), `isUnit_mk_ΔPdeep_fibreGenIdeal`, `fibreLocalizationAwayDetΔ_algEquiv` (O(fibre) ≃
  Localization.Away detΔ — the reducedness-free Route-A kill-condition payoff). **Build-plan step 1 DONE.**
- `Core.CThetaShiftCount` — `numTop_eq_cTheta_dminus` (`numTop d r = cTheta(d−r) = C(m,|δ|)`, field-free, via
  the engine `numTop_rankShift` = LR Lemma 4.5) + `ncard_topComponents_sigma_eq_cTheta_dminus` (Σ̄^r).
  **Step 3's combinatorial half was an ENGINE WIRE — DONE.**

**RECALIBRATION (formaliser ground-truth, Codex-confirmed):** the brief's "1-3 light lemmas" for the fibre
transport was optimistic. The chart `e`'s fibre side is `(O(F)[SchurVar])[1/detSchurS]` — a `|δ|`-variable
polynomial extension + a localization. Transporting the COMPONENT COUNT (not just dimension, which is all the
codim expedition needed from `e`) is a genuine successor tide whose hardest piece is a hand-built
**polynomial-extension minimal-prime descent** `TopDimMinPrimes(O(F)[X]) ≃ TopDimMinPrimes(O(F))` (classical —
minimal primes of `R[X]` are `p·R[X]` for `p ∈ minimalPrimes R` — but no packaged Mathlib lemma). The
`detΔ`-unit lemma removes the *reducedness* blocker; it does not itself prove the count.

**Next:** thread 06 (formaliser) — the fibre-count transport: `topDimMinPrimes_polyAway_equiv` → `orderIsoOfPrime`
through `e` → `numTop(fibre d E_r) = cTheta(d−r)` + the component bijection.

**The big decision ahead (scope-3 bundle/smoothness):** the full reduced bundle + smoothness genuinely needs the
**reducedness wall (R2-3b)** — `fibreGenIdeal` radical — which the codim expedition explicitly DECLINED as a
"≥2-module from-scratch AG sub-project" (it routed around radical-insensitively). The fibre-θ COUNT avoids the
wall (via `detΔ`-unit); the BUNDLE/SMOOTHNESS does not. So scope-B's hard core is climbing a wall previously
judged too costly — a large, multi-tide commitment. Surface to the operator when the count lands.

**Thread 07 (W1 avoidance) — SETTLED TRUE (2026-06-25).** Every top-dim minimal prime of `sigmaIdeal d r`
avoids `detΔ`, **globally** (one fixed `detΔ`, no per-component chart; only the witness point is per-component
via base change to `diag(I_r,0)`). Verified Singular `#BAD=0` on ~12 cases (incl. adversarial `(2,2,3,2)`),
Codex-concurred. **The math is ALREADY a landed Lean lemma:** `Core.SourceNoDrop.chartDsig_not_mem_partitionIdeal`
is the all-partition statement (any `m ∈ kostantPartitions d r`, no minimisation hyp). So W1 needs only WIRING
(quantify over `topComponents` via `bijOn_partitionIdeal_topComponents` + the localization-survival lemma + the
per-prime no-drop) — relayed to thread 08. Certificate `threads/07-dsig-avoidance/findings.md`.

**Thread 08 (fibre-count wiring) — running.** Building the reusable `TopDimMinPrimes` localization-survival
lemma + W2/W3/chart-`e` + assessing W0; W1 dischargeable now (per thread 07). Composes the headline
`numTop(fibre d E_r) = cTheta(d−r)` if W0 also wires.

**COUNT CHAIN — `_of` form LANDED + reviewed PASS; unconditional headline BLOCKED on a plumbing diamond
(2026-06-25, committed ba288ceb).** The full count chain (E0·W0·W1·chartE·W2·poly·W3) is composed in
`Core.FibreThetaCount.ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_of`: `(TopDimMinPrimes(O(fibre))).ncard =
cTheta(d−r)`, taking the W2 rung as an explicit hypothesis `hW2`. **Decorrelated fidelity reviewer: PASS** —
fidelity sound (TopDimMinPrimes genuinely counts top-dim components; `(2,2,2,2,2)`→6 not 10; W3 generator↔
radical; cTheta(d−r)=C(m,|δ|)), all 7 rungs compose, the keystone's **per-prime** no-drop `hper` genuinely
discharged (Codex produced the exact counterexample showing global-no-drop+avoidance is insufficient — the
Lean has the per-prime form), axiom-clean `[propext, Classical.choice, Quot.sound]`. All rung lemmas (W0–W3,
chartE, the keystone) committed green. **So the count is MATHEMATICALLY ESTABLISHED** (the `_of` chain + the
separately-proven W2 lemma `ncard_topDimMinPrimes_away_chartGfib_eq`).

**The one open piece — the UNCONDITIONAL headline** `numTop_fibre_eq_cTheta_dminus` (discharge `hW2` with the
W2 lemma) is **NOT yet landed**: composing them inline re-triggers the W2 instance-diamond at the
`Away(chartGfib)` boundary (leaks a `⊢ Field sorry` metavariable — the nested `MvPolynomial`-over-quotient
`AddMonoidAlgebra` vs `Ring.toSemiring` diamond W2 dodged via the flat iso). This is **plumbing, not a math
gap** (reviewer + Codex concur). Thread 09 is fixing it (pin the instance at the composition / consume W2's
flat-transported form), with a clean fallback (keep the green `_of` form; document the diamond). Controller
gates `#print axioms` sorryAx-free before committing. **Correction:** earlier framing of this as an "imminent
one-liner" was an overclaim the fidelity gate caught — the discharge hits the diamond.

**RESOLVED — SCOPE-2 CLOSED (2026-06-25, commit 50a9fa31).** Thread 09 landed the UNCONDITIONAL headline
`ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` : `(TopDimMinPrimes(O(fibre))).ncard = cTheta(d−r)`, no `hW2`.
The `sorryAx` had two causes, both fixed: (1) **universe** — W2 is `k : Type` (0), so the headline lives in a
`section UnivZero` (the universe-polymorphic rungs specialise to u=0; Type 0 carries ℂ / `AlgebraicClosure ℚ`,
matching the expedition's Type-0 codim/RLCT scope); (2) **diamond** — inline the 7-rung calc under a body
`letI : CommRing (MvPolynomial SchurVar (sweepFibreRing)) := inferInstance` and obtain W2 as a `have` under it
(matches the chain's instance path), rather than applying `_of` (whose `hW2` binder forced the
isDefEq-across-diamond that leaked the `Field` metavar). **Controller-gated** (not trusted): whole library
green 3780, sorries 0, `#print axioms` = `[propext, Classical.choice, Quot.sound]` (no sorryAx). So the
**fibre-θ count is CLOSED** — reviewer-PASS chain + the unconditional headline. Caveat: `k : Type 0` (to lift
to `Type u`, W2 needs re-generalising — peer-owned; Type 0 is the honest, sufficient scope). The explicit
fibre↔Kostant bijection is implicit via the composed BijOns; not separately assembled (optional).

---

# Scope-3 — the rest of Lemma 4.6 (bundle + smoothness). CLOSED 2026-06-26.

The operator chose the maximal "build it for real" push. The substantive mathematics is **complete,
unconditional, axiom-clean** (`[propext, Classical.choice, Quot.sound]`, whole library green at 3805 jobs).
The two remaining residuals are precisely characterised and **roadmapped** — both genuinely non-trivial
(new scheme-theoretic math / off-critical-path), both recommended-stop by the tides + multiple decorrelated
Codex consults. The expedition closes at its honest ceiling.

## Final scorecard
| Result | State | Headline lemma |
|---|---|---|
| θ-count `numTop(fibre)=cTheta(d−r)=C(m,\|δ\|)` | ✅ Unconditional | `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` |
| Codim `= C+δ` | ✅ (prior expedition) | `codimRepCanonical_fibre_eq_cCodim_add_shift` |
| **Generic smoothness of the fibre** | ✅ **Fully unconditional** | `isSmoothAt_sweepFibre_topComponent`, `exists_isSmoothAt_chartDsig_unconditional` |
| Σ̄^r component ↔ orbit labeling | ✅ Unconditional | `exists_sigma_topComponent_orbitRingEquiv` |
| Bundle: per-pivot local-product atlas over the rank-`=r` open | ✅ cover+triv+cocycle+intertwining+k-point tie | `reducedFibre_pivotLocalProductAtlasOnRankOpen` |
| `e` (fibre-component↔orbit), chart-localization transport | ✅ rung 1 | `schurComponent_chartQuotientEquiv` |
| 3-θ-invariants exposition | ✅ | `docs/expositions/theta-invariants-distinction.md` |

Reusable network-free spin-outs banked along the way: `mvPolynomialAwayMapTensorAlgEquiv`,
`exists_invertible_minor_of_rank` (a Mathlib v4.29 gap: rank-`r` matrix ⟹ invertible `r×r` minor), the
`awayOverlap`/`awayTriple` localization cocycle engine, `localizationAtPrimeQuotientAlgEquiv`,
`Algebra.Smooth.tensorProduct`, `isSmoothAt_bot_of_finitePresentation_domain`.

## How smoothness closed — the elegant shortcut (thread 17/20)
The planned route was an orbit-closure identification (C2(a): `sweepFibreRing⧸I ≃ orbit ring`). It proved
UNNECESSARY. A fibre top component `sweepFibreRing⧸I` is a finitely-presented **domain** over an
algebraically-closed (perfect) field, hence **generically smooth** (`IsSmoothAt k ⊥`, the generic-smoothness
theorem); the C1 localization-recovers-component bridge lifts that to `IsSmoothAt k I`, and the thread-17
chart transport carries it to the fibre chart. **The OrbitSmooth machinery was a red herring for
smoothness** — the component need not *be* an orbit, only a domain. Generic smoothness was the headline
goal and it landed cleanly, fully unconditional.

## Two decisive fidelity catches (the decorrelated discipline working)
1. **The dimensionally-impossible bare-orbit iso (thread 20).** Thread-17's stated C2(a) interface
   `sweepFibreRing⧸I ≃ orbitRing M` was confirmed (by reviewer+Codex×2) as "non-vacuous, confirmed-final" —
   but a later dimension count showed it is **dimensionally impossible** (fibre component = orbit × `A^δ`,
   `δ = r(d_0+d_N−r) > 0`; witness `(2,2,2)r1`: `4 = 1+3`). Lesson: a non-vacuity claim for a cited
   interface needs a **dimension/satisfiability check**, not just "the implication is non-circular".
2. **The globally-false consumer-shaped `e` (thread 24).** Even the corrected `sweepFibreRing⧸I ≃
   MvPolynomial η (orbitRing M_shifted)` is **globally false**: the chart `e_β` is intrinsically localized,
   so only a LOCALIZED, full-`d`-orbit form is reachable. The tide refused to build a 500-line iso to feed a
   consumer whose shape doesn't exist, and surfaced it. Both dead consumers were **relabeled** as superseded
   scaffolding (not deleted — honest record).

## The bundle tower (threads 11/18/19/21/22/23) and its honest ceiling
The bundle was a genuine multi-rung tower, each "last rung" revealing another: single-chart triviality (11)
→ per-minor cover + family (18) → ambient transition cocycle (19) → top-left `e_β`↔ambient bridge (21) →
per-pivot conjugation skeleton + trivializations at every pivot (22) → coherent per-pivot atlas + base-side
cocycle + scheme cover + k-point rank-tie (23). What is **earned** is a genuine coherent **per-pivot
local-product atlas over the rank-`=r` open** — honestly NOT named `locallyTrivial`. A 5th Codex consult
corrected a controller premise: the k-point rank-tie does **not** compose with the prime-level cover; the
bare `locallyTrivial` name needs the **prime residue-field-rank bridge = genuinely new scheme-theoretic
math**. The tide also correctly **overrode a mis-aimed controller steer** (the ambient-transition target was
a red herring; the genuine cocycle is base-side over `sweepSigmaRing`).

## Roadmapped residuals (future work — both recommended-stop here)
1. **Bundle → bare `locallyTrivial`:** the prime-level residue-field-rank bridge (`P ∈ rankROpen ↔ universal
   matrix over κ(P) has rank r`). Substantial NEW scheme-theoretic math, a fresh build — NOT a finishing
   touch.
2. **`e` → full localized iso:** rung 2, the orbit descent `exists_chartComponent_localizedOrbitEquiv`
   (`(Away chartDsig)⧸chartComponentIdeal → Away Δ (orbitRing (realizerD m))`). ~mid-hundreds LoC, off every
   critical path, consumed by nothing.
3. **Type-universe lift** (Core, `k : Type 0 → Type u`): mechanical, deferred, loses nothing for the
   ℝ/ℂ application.

## Controller lessons
- **The decorrelated dialectic earns its cost.** Three separate confident headlines were wrong and caught by
  the next pass: "Aoyagi erred" (refuted, thread 03), the "confirmed-final" bare-orbit iso (dimensionally
  impossible, thread 20), the shifted-orbit `e` (globally false, thread 24). Never bank the confident
  headline; let the skeptical / decorrelated seat fire.
- **Cost estimates repeatedly ran low** (the bundle "2–3 modules" → a 7-rung tower; C2(a) "~800 LoC" → a
  multi-tide undertaking + a false target). Surface each recalibration for a knowing operator decision rather
  than grinding by inertia — and when the experts on the ground recommend stop, recommend consolidating.
- **Tides exercised excellent independent judgment** — finding shorter routes (the smoothness domain
  shortcut), refusing to build false objects, overriding mis-aimed controller steers, and naming honestly
  (declining `locallyTrivial` four times). Honest scope was upheld throughout; no overclaim survived to a
  headline.
