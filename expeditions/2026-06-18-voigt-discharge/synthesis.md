# Synthesis — voigt-discharge (controller's durable plan + state)

> Recovery substrate. If context is lost, this file + `brief.md` + `priorities.md` + `threads.md`
> reconstruct the whole expedition. Flushed every tick.

## Mandate (operator, 2026-06-18)
Drive to the end as **one expedition**. **Zero new cited interfaces.** If Mathlib lacks a foundation,
**build it as far as needed** to fully discharge `hVoigt`. Controller holds discipline + ambition;
seat-bounded teammates, stood down at close.

## Target
Discharge `hVoigt` in `Core.OrbitCodim`:
`codimRep (canonicalCoord d) (orbitRankLocus M) = orbitLinearCodim M` — geometric codimension (height of
the vanishing ideal of the rank-locus, canonical coords) = tangent codimation = `dim Ext¹(M,M)`.
Then `codimRepCanonical_orbitRankLocus_eq_multSum` becomes **unconditional**.

**Already bedrock (do not reprove):** `orbitLinearCodim M = finrank C¹ − finrank (range δ⁰) = dim Ext¹(M,M)`
(`Core.OrbitLinearCodim`, `Core.DeformationExt`). The deformation complex is 2-term, so
`orbitLinearCodim = dim Rep − dim(tangent-to-orbit)`. The **algebra side is done**; only the AG bridge remains.

## Route — tangent space + smoothness (settled by recon 01)
NOT classical determinantal (loci are rank conditions on *products* = variety-of-complexes). NOT full
orbit–stabilizer AG. The bridge: orbit-rank-locus is irreducible; `M` is a smooth point with Zariski
tangent space `= im δ⁰`; smooth ⇒ local dim = tangent dim; `height(I(Z)) = dim Rep − dim Z`. Combine →
`codim = dim C¹ − dim(im δ⁰) = dim coker δ⁰ = dim Ext¹`.

## Field hypotheses (recon verdict)
`[Field k] [IsAlgClosed k]`. No char-0 needed (`IsAlgClosed ⇒ PerfectField` covers generic smoothness;
`IsAlgClosed` covers the Nullstellensatz bridge). These are **hypotheses, not citations** — allowed.
The engine is network-free, so `[IsAlgClosed k]` on the Core lemma is fine. *DLN-side note (out of scope
here):* DLN's field is ℝ; the real-vs-`k̄` codim equality is a separate small DLN-side fact, does not block
the Core discharge.

## Key structural facts (recon verdict)
- `codimRep` is **point-set commutative algebra** — `Ideal.height` of `MvPolynomial.vanishingIdeal` of the
  point set in `kⁿ`. Every Mathlib dimension/irreducibility theorem lives on `PrimeSpectrum`. So a
  **point-space ↔ PrimeSpectrum / Zariski-closure bridge** (Nullstellensatz) is needed first — this is what
  forces `[IsAlgClosed k]`.
- `orbitRankLocus M` is **defined as the rank locus** (`rankPattern · ≤ rankPattern M`, pointwise), NOT the
  orbit closure. `orbitRankLocus = Ō_M` (Thm 3.8) is currently **Cited** and is **in the zero-cited target**
  (L6): `codimRep` is the height of `vanishingIdeal(orbitRankLocus)`, so we must prove that locus is `Ō_M`
  (irreducible) to get height = codim. The engine already proves the *orbit* invariant
  (`rankPattern_eq_iff_orbit`); the *closure / ≤-direction* (degeneration order) is the remaining content.
- Mathlib positives: `MvPolynomial.ringKrullDim_of_isNoetherianRing` gives `dim Rep` for free;
  `RingEquiv.height_comap`/`height_map` exist (the OrbitCodim docstring's "no height transport at v4.29" is
  out of date); scheme-level generic smoothness (`dense_smoothLocus_of_perfectField`) and group-scheme
  smoothness (`smooth_of_grpObj_of_isAlgClosed`, 2026) are **present** — but scheme-level, unusable until
  `G_d`/orbit are modelled compatibly.

## The build ladder (dependency order)

Each layer's headline lemma is its **contract** (statement card at landing). Status: ☐ todo / ◐ in
progress / ☑ landed (green + AUDIT + hardener).

- **L0 — Nullstellensatz / point-space ↔ PrimeSpectrum bridge.** **☑ LANDED + fidelity-PASS** (hardener pass
  pending). `Core.NullstellensatzCodim`: `codimRepCanonical Z = #(RepCoord d) − varietyDim Z` for irreducible
  closed `Z` (`[IsAlgClosed k]`), via the Nullstellensatz dictionary (`vanishingIdeal` radical;
  irreducible⟺prime; closure round-trip) + L5 catenary + finite-index transport. Headline (additive, lossless):
  `height_vanishingIdeal_add_varietyDim_eq_card`. `[IsAlgClosed k]` enters only the dictionary.
- **L1 — `G_d = ∏ GL` + orbit map + irreducibility.** `G_d` as an (irreducible) variety; the action/orbit
  map; image of irreducible is irreducible; closure irreducible. *Size: sizeable module (no `GL` scheme).* ☐
- **L2 — affine Zariski tangent space + `T_M = ker Jac = im δ⁰`.** Concrete tangent space of `V(I) ⊆ kⁿ` at a
  point; identify the orbit's tangent at `M` with the coboundaries `im δ⁰`. *Size: sizeable, absent.* ☐
- **L3 — smooth point via homogeneity + orbit open in its closure.** Smooth locus dense + `G`-stable ⇒ orbit
  smooth everywhere; `M` is a smooth point of `Ō_M`. *Size: module → sizeable.* ☐
- **L4 — smooth ⇒ `IsRegularLocalRing` ⇒ tangent dim = local Krull dim.** (`IsRegularLocalRing.iff_finrank_
  cotangentSpace` present; geometric feed-ins absent.) *Size: module.* ☐
- **L5 — height–dimension formula.** `height p + dim(R/p) = dim R = n` for primes of `MvPolynomial (Fin n) k`.
  **SIZED (thread 02): bounded 2–3 module sub-library, days — NOT greenfield catenary, NOT multi-expedition.**
  Route = **integral-extension** (a), not catenary (b): recon 01 misread Mathlib — `dim k[x]=n` and per-prime
  going-down additivity (`height_eq_height_add_of_liesOver_of_hasGoingDown`) are PROVED; the gap is *assembly*.
  Sub-ladder L5.0–L5.8 in `threads/02-dimension-formula-sizing/findings.md`; hardest = L5.6 (`height+coheight=n`
  via going-down induction) and L5.4 (integral-extension `ringKrullDim` invariance). **Kill-condition:** if
  L5.6's induction needs absent instance-propagation it inflates toward "weeks" — first build move (L5.4+L5.1)
  settles this. **☑ COMPLETE + bedrock-confirmed + hardened** — headline `height_add_ringKrullDim_quotient_eq` (`Core.NoetherMonicPositioning`): `height p + ringKrullDim (R⧸p) = n` unconditionally (`[Field k]`). Modules IntegralDimension / PolynomialDimension / NoetherMonicPositioning. Kill-condition never fired; monic-positioning brick re-derived. Hardener: BEDROCK CONFIRMED.
- **L6 — Thm 3.8 at radical-ideal level.** `orbitRankLocus = Ō_M` (the degeneration order; ≤-direction). *Size:
  module.* ☐
- **L7 — final Voigt assembly.** Combine L0–L6 into `hVoigt`, drop the hypothesis from
  `codimRepCanonical_orbitRankLocus_eq_multSum`. *Size: tide.* ☐

### Phase grouping (how the one expedition is run)
- **Phase A — CA foundations:** L5 (size first, then build) + L0. The riskiest substrate; build to bedrock first.
- **Phase B — orbit geometry:** L1 + L2 + L3.
- **Phase C — regularity bridge:** L4.
- **Phase D — degeneration order:** L6.
- **Phase E — assembly:** L7.
A/B are largely independent and can interleave once L5 is sized; C depends on B+L5; D is independent; E last.

## Sequencing decision
1. ☑ **Size L5** (thread 02) — DONE: bounded sub-library, integral-extension route. Risk materially reduced.
2. **NEXT — first build tide: L5.4 + L5.1** (the recon's de-risking move). Both rest entirely on present
   Mathlib bricks (order transport + `ringKrullDim_quotient`); a green L5.4 confirms the order-transport
   machinery and de-risks the hard L5.6. New network-free `Core` module (general commutative algebra,
   upstream-grade). Watch the L5.6 kill-condition as we proceed up the L5 sub-ladder.
3. Then finish L5 (L5.2/5.3 → L5.4 done → L5.5 → L5.6 → L5.7), and **L0** (Nullstellensatz/`PrimeSpectrum`
   bridge, gates the geometry).
4. Then Phase B geometry (L1–L3), Phase C (L4), Phase D (L6), Phase E (L7 assembly).

## Discipline for this expedition
- **Gates:** every layer → reviewer fidelity AUDIT + independent `hardener` bedrock pass; decorrelated Codex on
  the hard CA proofs (L5) and any universal/exhaustiveness claim. Controller is sole merger + green-gater.
- **Seats (bounded):** `recon`/`scout` (terrain + sizing), `pen-and-paper` (CA/AG certificates), `formaliser`
  (tides), `reviewer` (fidelity), `hardener` (bedrock). Reuse across layers; stand all down at close.
- **Single-writer-per-file:** the Lean aggregator `DLNFibre.lean` and each new module have one writer per tide;
  controller integrates.
- **Build:** worktree `.claude/worktrees/voigt-discharge`, shared `.lake/packages`. Background long builds.

## State log (newest last)
- 2026-06-18: expedition scaffolded off `dev` (`9e99e01`). Recon 01 (Mathlib coverage) CLOSED — route confirmed
  (tangent+smoothness), `[IsAlgClosed k]`, orbitRankLocus = rank-locus (Thm 3.8 in scope), 8-layer ladder, L5
  (catenary/dim-formula) = dominant risk. Next: size L5.
- 2026-06-19: thread 02 (L5 sizing) CLOSED — **L5 downgraded** to a bounded 2–3 module sub-library via the
  integral-extension route (catenary avoided; key bricks proved in Mathlib, recon 01 misread). Sub-ladder
  L5.0–L5.8 pinned; kill-condition on L5.6. Next: first build tide L5.4 + L5.1.
- 2026-06-19: thread 03 (L5 dim-foundations) LANDED + fidelity AUDIT SURVIVED. `Core.IntegralDimension`:
  L5.0 `dim k[x]=n`, L5.1 `dim(R/p)=coheight p`, L5.2/5.3/5.4 integral-extension `ringKrullDim` invariance
  (`ringKrullDim_eq_of_integral_injective`, the headline). Green, 0 sorry, axiom-clean. **HARD #2 done.**
  Order-transport + going-up chain-lift machinery proven at our pin; kill-condition did NOT fire for this
  block (no going-down/IsIntegrallyClosed needed). Decorrelated Codex confirmed the `strictComono`-is-unsound
  catch with an explicit counterexample. Remaining L5 risk concentrates on **L5.6** (going-DOWN additivity →
  IsIntegrallyClosed/HasGoingDown propagation still untested). Hardener bedrock pass deferred to L5-phase close.
  Next: L5.6 (the hard one) and/or L0 (gates the geometry).
- 2026-06-19: thread 04 (L5.5/L5.7-≤) LANDED. `Core.PolynomialDimension`: L5.5 `dim(R/p)=noetherRank`,
  L5.7 `≤` (`primeHeight p + dim(R/p) ≤ n`), + the polynomial-tower additive height brick
  (`height_eq_height_under_add_height_map_quotient`). **Kill-condition CLEAN** (going-down instances fire by
  inferInstance). Full L5.7 equality NOT yet stated (no overclaim): the catenary `≥` needs a
  **monic-coordinate-positioning lemma** (Noether-normalization degree trick, `private` in Mathlib). Next:
  build that brick + close L5.7 `≥` → full equality. Then L0, then geometry.
- 2026-06-19: **L5 COMPLETE.** thread 05 closed the catenary `≥` via a re-derived Noether monic-positioning
  brick → full equality `height_add_ringKrullDim_quotient_eq` (`[Field k]`, axiom-clean). Hardener pass:
  BEDROCK CONFIRMED (3 low findings applied: dropped decorative `_hinj` + rename `ringKrullDim_le_of_integral`,
  fixed stale docstring, added height-1 witness). **Phase A's hard half done.** Next: L0 (Nullstellensatz /
  point-space↔PrimeSpectrum bridge) — connects `codimRep` height to L5's dim formula; `[IsAlgClosed k]` enters here.
- 2026-06-19: **PHASE A COMPLETE.** L0 (thread 06) landed + fidelity-PASS — the Nullstellensatz codim bridge
  `codimRep Z = #σ − varietyDim Z` (irreducible closed Z, [IsAlgClosed k]), `Core.NullstellensatzCodim`. The CA
  foundations (L5 dim formula + L0 bridge) are bedrock. **Pending:** a hardener bedrock pass on L0 (deferred from
  this turn's gate; run at Phase-A close / next turn). **Next — Phase B geometry:** the architectural fork
  (schemes vs concrete-affine for G_d/orbit/tangent/smoothness) — open with an L1 recon to decide it, then build
  L1 (G_d/orbit/irreducibility) → L2 (tangent = im δ⁰) → L3 (smoothness). The bridge note: discharging hVoigt now
  needs the orbit-closure variety-dimension identified with orbitLinearCodim (= dim Rep − dim im δ⁰), i.e.
  varietyDim(Ō_M) = dim(orbit) = dim(im δ⁰) — that's the geometry's job (L1–L4), then L6 (orbitRankLocus = Ō_M),
  then L7 plugs codimRep = #σ − varietyDim into orbitLinearCodim.
- 2026-06-19: L0 hardener pass — **BEDROCK CONFIRMED** (no critical; defs honest — `IsZariskiIrreducible`
  rescued by `isIrreducible_iff_closure`; non-vacuity at a real point; `[IsAlgClosed k]` placement drop-probed).
  **Phase A fully gated (L5 + L0, both AUDIT + hardener).** 2 optional-polish notes deferred to close:
  add inhabitation `example`s for `IsZariskiClosed`/`IsZariskiIrreducible`; the `[IsAlgClosed k]` on the
  `codimRep_*` corollaries is provably-unused-but-co-located (documented, keep). Cron heartbeat `e5d64339`
  armed (every ~10 min, session-only) as a backstop for genuine yields; driving continuously in-turn meanwhile.
  **Now Phase B (orbit geometry).** Goal: `varietyDim(Ō_M) = dim(im δ⁰)` via Ō_M irreducible + M smooth point
  + Zariski tangent at M = im δ⁰. Opening with an L1 recon to DECIDE schemes-vs-concrete-affine.

## PHASE B — ROUTE DECIDED: concrete affine (Route A) [2026-06-19, thread 07]
Route S (schemes) rejected — forces a scheme→`ringKrullDim` bridge our point-set stack doesn't need. **Phase B
owes exactly `varietyDim(orbitRankLocus M) = finrank(range δ⁰)`** (+ primeness). Full recon in
`threads/07-L1-geometry-recon/findings.md`. Route-A ladder:
- **L1** Ō_M irreducible AS `(vanishingIdeal …).IsPrime` (image of irreducible ∏GL under poly map). Module.
- **L2** orbit-map differential = `range δ⁰` (Jacobian/cotangent linearisation; the conceptual heart). Sizeable.
- **L3** M smooth point by homogeneity (transitive action + smooth locus G-stable + **dense** — density is the
  crux; ring-side density to build or a minimal Spec detour, NOT modelling G_d as a scheme). Module→sizeable.
- **L4** smooth ⟹ `IsRegularLocalRing` (a, ABSENT bridge) ⟹ `iff_finrank_cotangentSpace` (b) + `ResidueField=k`
  (c) + local↔global dim (d) ⟹ `varietyDim = finrank(range δ⁰)`. Module (hardest finish).
- (then L6 `orbitRankLocus = Ō_M` set-equality [Phase D], L7 assembly.)
**KILL-CONDITION:** if L4(a)+L4(d) need a regular-locus/local↔global CA *sub-library* (not modules), Phase B
inflates — doesn't favour S (shared); build the regular-local-ring bridge as its own Core module.
**Sequencing (adopt recon's "size the hard middle"):** de-risk L4(a)+L4(d) FIRST (kill-condition, reusable CA),
then L2, then L3 (density), L1, L4-assembly.
- 2026-06-19: thread 07 (Phase B architecture) CLOSED — Route A decided. Next: de-risk L4(a)+L4(d) (smooth ⟹
  regular local ring + local↔global dim) as a standalone general-CA tide; report if it balloons (kill-condition).

## ⚠ KILL-CONDITION FIRED — L4 is a foundational sub-library (operator decision pending) [2026-06-19, thread 08]
Sizing of L4(a)/(d) (formaliser + decorrelated Codex, both independent): **the regular-local-ring finish is NOT
module-scale — it is a multi-week foundational AG/CA sub-library Mathlib entirely lacks.** No Lean landed
(correctly — sorry-patching a sub-library is forbidden).
- **The absent theory** (verified by `rg`): `rg ringKrullDim` over all of `RingTheory/{Kaehler,Smooth,Etale}/`
  = **0 hits** — no `rank Ω ↔ ringKrullDim` link anywhere. `IsRegularLocalRing` is an **isolated definition**
  (nothing produces it; only `iff_finrank_cotangentSpace` consumes it). No affine-domain dimension formula
  (`height m + dim(A/m) = dim A` for `A = R/I`, only our R-only L5). Codex: "multi-week."
- **No shortcut:** the alternative route (orbit-stabiliser / fibre-dimension `dim O = dim G − dim Stab`) hits the
  SAME absent dimension theory (fibre-dimension ↔ ringKrullDim, also 0 hits). Every standard route to
  `varietyDim(Ō_M) = dim(im δ⁰)` needs the infinitesimal↔Krull-dimension bridge Mathlib does not have.
- **Sub-sizing:** L4(d) (affine-domain equidimensionality, lift L5 to `R/I`) ≈ 1–2 modules (Noether normalization
  PRESENT; reuses `ringKrullDim_eq_of_integral_injective`). L4(a) (smooth ⟹ regular via cotangent↔dim + the
  conormal/Kähler comparison) = the binding multi-week sub-library.
- **Mandate tension:** the only module-scale alternative is to **Cite** the smooth-point regularity bridge as a
  named interface — a *new cited interface*, forbidden by the zero-cited mandate. So: build the sub-library, or
  relax the mandate to one named standard citation, or stop at the current hybrid. **SURFACED TO OPERATOR.**
- **Banked regardless:** Phase A (L5 polynomial dimension formula + L0 Nullstellensatz bridge) is real
  upstream-grade reusable bedrock, independent of this decision.
- **Autonomous loop PAUSED** (cron `e5d64339` deleted) pending the operator's scope decision.

## OPERATOR DECISION: BUILD IT (zero-cited) [2026-06-19]
Operator chose to build the foundational sub-library — full zero-cited discharge, multi-week accepted. The
drive resumes. **L4 is restructured into a sub-campaign (L4★)**, staged (recon's order: equidimensionality
tools first, they feed smooth⟹regular):

### L4★ sub-ladder (the infinitesimal↔Krull-dimension sub-library, network-free Core, upstream-grade)
- **L4d — affine-domain dimension formula / equidimensionality.** For a finite-type DOMAIN `A` over a field:
  `height p + ringKrullDim (A ⧸ p) = ringKrullDim A` (lift L5's polynomial-ring formula to `A = R/I`); hence
  `height m = ringKrullDim A` for maximal `m`, and `ringKrullDim (Localization.AtPrime m) = ringKrullDim A`
  (local↔global). *~1–2 modules.* Reuses Noether normalization (present) + `ringKrullDim_eq_of_integral_injective`
  + the going-down height-additivity. **BUILD FIRST.**
- **L4a — cotangent ↔ dimension + smooth ⟹ regular** (the binding multi-week core). Stages: cotangent space at a
  `k`-point = `m/m²` (Mathlib cotangent API); smooth-at-`m` ⟹ `finrank(cotangent) = relative dim (rank Ω)`
  (the absent Kähler/conormal comparison); at a smooth point `relative dim = ringKrullDim(AtPrime m)` (the
  absent `rank Ω = ringKrullDim` bridge, uses L4d equidimensionality); combine via
  `IsRegularLocalRing.iff_finrank_cotangentSpace` ⟹ `IsRegularLocalRing`. **Size then build.**
- **L4-assembly:** smooth point of Ō_M (L3) + `T_M = range δ⁰` (L2) + L4a ⟹ `varietyDim(Ō_M) = finrank(range δ⁰)`.

### Updated sequencing
1. **L4d** (bounded, build now) → 2. **L4a** (the sub-library, size-then-build) → 3. geometry **L1** (irreducible
= prime), **L2** (T_M = range δ⁰), **L3** (smooth point via homogeneity + density) → 4. **L4-assembly** → 5.
**L6** (orbitRankLocus = Ō_M, Phase D) → 6. **L7** (final assembly closing hVoigt).

- 2026-06-19: operator chose BUILD IT (zero-cited). Loop re-armed (cron, every ~10 min, session-only; 7-day
  expiry — re-arm weekly for the multi-week horizon). Building L4d (affine-domain equidimensionality) first.

- 2026-06-19: **L4d LANDED** (thread 09, one module, reviewer fidelity PASS) — `Core.AffineDomainDimension`:
  `affine_domain_height_add_ringKrullDim_quotient_eq` (affine-domain dim formula via Noether-normalize + L5),
  `height_eq_ringKrullDim_of_isMaximal`, **`ringKrullDim_localizationAtPrime_isMaximal_eq`** (the local↔global
  feed-in L4a needs). Kill-condition did NOT fire (going-down theorem IS in Mathlib `@[stacks 00H8]`, another
  recon misread like L5). Axiom-clean.
  **REMAINING L4★ core = L4a only** (the genuine multi-week sub-library): the cotangent↔Krull-dimension bridge.
  Two absent pieces (thread 08): (i) **cotangent comparison** — `IsLocalRing.CotangentSpace (AtPrime m) = m/m²`
  identified with the Kähler `Ω[A⁄k] ⊗ k(m)` at a `k`-rational point; (ii) **`rank Ω = ringKrullDim` at a smooth
  point** (uses L4d equidimensionality `ringKrullDim_localizationAtPrime_isMaximal_eq`). Then
  `IsRegularLocalRing.iff_finrank_cotangentSpace` ⟹ `IsRegularLocalRing` at a smooth `k`-point.
  **NEXT TICK:** a pen-and-paper/scout produces the **L4a build sub-ladder** (the exact lemma chain + which
  Mathlib cotangent/Kähler API to build on — `Ideal.cotangentSpace`, `KaehlerDifferential`, `Extension.Cotangent`,
  `SubmersivePresentation.rank_kaehlerDifferential`), decorrelated Codex; THEN build tides. After L4a: geometry
  L1 (irreducible=prime), L2 (T_M = range δ⁰), L3 (smooth point via homogeneity+density), L4-assembly, L6, L7.

## L4a RE-SIZED: BOUNDED (~3 modules) via the étale route [2026-06-19, thread 10]
The "multi-week sub-library" verdict (thread 08) was the **complete-intersection framing**; the **étale-over-
affine-space route** is bounded (~3 modules). Smooth point ⟹ étale over 𝔸ⁿ ⟹ flat+quasi-finite ⟹ prime height
preserved (0-dim fibre) ⟹ `ringKrullDim(AtPrime m) = n = rank Ω`, INDEPENDENTLY of the cotangent (non-circular).
Codex independently chose the same route + load-bearing lemma + ~3-module size. **So the whole expedition is
bounded again** (no multi-week tower). [The operator accepted "build it / multi-week"; this is good-news scope
reduction — continuing the drive, no need to re-surface per the autonomous mandate.] Full blueprint:
`threads/10-L4a-recon/findings.md`. Sub-ladder:
- **M1 `Core/FlatQuasiFiniteHeight.lean`** — `height_eq_under_of_flat_quasiFiniteAt` (+`_of_etale`): flat +
  quasi-finite ⟹ prime height = contraction's height (going-down additivity + 0-dim fibre). Self-contained
  general CA, **BUILD FIRST** (de-risks). Kill-condition: fibre-prime-height-0 — judged not to fire.
- **M2 `Core/SmoothLocalRelativeDimension.lean`** — the dimension bridge `ringKrullDim(AtPrime m) = n = rank Ω`
  (standard-smooth presentation + `exists_etale_mvPolynomial` + M1 + our catenary `p.height = n`).
- **M3 `Core/SmoothPointRegular.lean`** — cotangent comparison `finrank(m/m²) = rank Ω` (scope JOINTLY with L2)
  + `iff_finrank_cotangentSpace` ⟹ `IsRegularLocalRing` (target `smooth_point_isRegularLocalRing`).
- 2026-06-19: thread 10 (L4a recon) CLOSED — L4a bounded via étale route. Next: build M1 (flat-quasi-finite
  height), then M2, then M3/L2 jointly. After L4a: geometry L1/L2/L3, L4-assembly, L6, L7.
- 2026-06-19: **M1 LANDED** (thread 11) — `Core.FlatQuasiFiniteHeight.Ideal.height_eq_under_of_flat_quasiFiniteAt`
  (+`_of_etale`): flat + quasi-finite-at ⟹ `Q.height = (Q.under R).height`. **Kill-condition did NOT fire** (fibre
  height 0 via `QuasiFiniteAt.eq_of_le_of_under_eq`; no Artinian-fibre route needed). Reviewer FAITHFUL (Lean is
  more general; QuasiFinite-vs-00PL caveat disclosed, coincide for finite-type). Green (2673 jobs), axiom-clean.
  The étale route is CONFIRMED viable. **Next: M2** (`Core/SmoothLocalRelativeDimension.lean`) — the dimension
  bridge `ringKrullDim(AtPrime m) = n = rank Ω` (standard-smooth presentation + `exists_etale_mvPolynomial` +
  M1's `height_eq_under_of_etale` + our catenary `p.height = n` for the maximal `p` of `k[x₁..xₙ]`). Then M3/L2.
