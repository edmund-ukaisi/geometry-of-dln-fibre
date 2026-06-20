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
- 2026-06-19: **M2 LANDED** (thread 12, reviewer FAITHFUL) — `Core.SmoothLocalRelativeDimension.ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`:
  the **non-circular dimension bridge** `ringKrullDim(AtPrime m) = n = rank Ω` via the étale route (M1
  `height_eq_under_of_etale` + L5 catenary + Zariski's lemma for the maximal contraction). Came in BOUNDED;
  **holds for ANY field** (no IsAlgClosed needed — stronger than planned). Green (2674 jobs), axiom-clean.
  Non-circularity independently traced (routes M1+L5+Zariski only, never cotangent=dim). **Next: M3**
  (`Core/SmoothPointRegular.lean`) — transport `rank Ω = n` to `AtPrime m`, the cotangent comparison
  `finrank(m/m²) = rank Ω = n` (scope JOINTLY with L2's tangent identification), then
  `iff_finrank_cotangentSpace.mpr` ⟹ `IsRegularLocalRing` (= L4a target `smooth_point_isRegularLocalRing`).
  After M3 (L4a done): geometry L1 (irreducible=prime), L2 (T_M = range δ⁰; overlaps M3 cotangent), L3 (smooth
  point of Ō_M via homogeneity), L4-assembly, L6, L7.

## ✅ L4★ COMPLETE — the infinitesimal↔Krull-dimension sub-library is bedrock [2026-06-19]
M3 landed (thread 13, reviewer FAITHFUL): **`Core.SmoothPointRegular.smooth_point_isRegularLocalRing`** — for a
finite-type `k`-algebra (`k` PERFECT — `[IsAlgClosed k]` only used via `PerfectField`), `m` maximal,
`IsSmoothAt k m` ⟹ `IsRegularLocalRing (Localization.AtPrime m)`. Cotangent comparison bounded (conormal
injectivity `FormallySmooth.kerCotangentToTensor_injective_iff`, no conormal sub-library). Also exposes
**`finrank_cotangentSpace_eq_of_isSmoothAt`** (`finrank_{κ(m)}(m/m²) = n`) — the L2 reuse point.
**L4★ = L4d (equidimensionality) + M1 (flat/q-finite height) + M2 (dimension bridge) + M3 (smooth⟹regular), all
landed/gated/axiom-clean.** The feared "multi-week tower" is done. 10 Core modules; whole lib green (2686 jobs).

## REMAINING — the orbit geometry (apply L4★ to our orbit) → assembly
Goal still owed: **`varietyDim(orbitRankLocus M) = finrank(range δ⁰)`**, then L7 chains to `hVoigt`.
The assembly logic (all pieces now have a home):
`codimRep(orbitRankLocus M) =[L0, needs L1 prime] #σ − varietyDim` ; `varietyDim =[L4d local↔global] ringKrullDim(AtPrime m_M)`
`=[M3: regular ⟹ iff] finrank(cotangent at m_M) =[L2] finrank(range δ⁰)` ; `orbitLinearCodim =[Phase A] #σ − finrank(range δ⁰)`.
So `codimRep = orbitLinearCodim` ✓. Remaining tides (orbit-specific; size-then-build each):
- **L6** `orbitRankLocus M = Ō_M` (rank locus = orbit closure; the degeneration-order ≤-direction). Needed so the
  variety is the orbit closure (irreducible, smooth at M). Currently Thm 3.8 Cited — must PROVE (zero-cited).
- **L1** `(vanishingIdeal (canonicalCoord '' orbitRankLocus M)).IsPrime` (irreducible) — `O_M = image of
  irreducible ∏GL` under a poly map ⟹ closure irreducible ⟹ ideal prime. Feeds L0.
- **L3** `IsSmoothAt k m_M` for the coordinate ring of `orbitRankLocus M` (= Ō_M) — via homogeneity: orbit smooth
  (smooth locus G-stable + dense), M in the open orbit. **The density is the substantive piece** (recon's crux;
  ring-side density from `FormallySmooth.of_perfectField` or a minimal Spec detour).
- **L2** cotangent/tangent of `orbitRankLocus M` at M = `range δ⁰` over `k` (with `κ(m)=k`, identify M3's
  `finrank(m/m²)=n` with `finrank(range δ⁰)`). The orbit-map differential = `δ⁰` is already pinned (recon 07).
- **L4-assembly** + **L7** (drop `hVoigt` from `codimRepCanonical_orbitRankLocus_eq_multSum`).
Suggested order: L6 (or L1) first (set up the variety = orbit closure, prime), then L3 (smoothness), L2 (tangent),
assembly. Each size-then-build.
- 2026-06-19: **L4★ COMPLETE.** Next: orbit geometry — start with L6/L1 (variety = irreducible orbit closure).

## ORBIT GEOMETRY — sized [2026-06-19, thread 14]. Full blueprint in `threads/14-geometry-recon/findings.md`.
Key insight: `varietyDim` depends only on `vanishingIdeal` ⟹ **L6 stated at the IDEAL level** (no point-space
topology). The whole AG bridge keys on producing `IsSmoothAt k m_M` + `κ(m_M)=k` + `varietyDim(Z_M)=r`.
- **L6** `vanishingIdeal Z_M = vanishingIdeal O_M` — **sub-library (3–4 modules)**. Core = box-move/lace-diagram
  **degeneration** (L6.1+L6.2) — the Abeasis–Del Fra theorem the PAPER ITSELF only cites; genuine new content.
  KILL-COND: if the generation doesn't reduce to a clean `diff`-induction it inflates. (Within "build it" mandate;
  surface only if the kill-condition fires.)
- **L1** primeness — one module (orbit ideal = ker μ_M^* into a domain `𝒪(G_d)`), given L6.4.
- **L2/L3** — bounded via the **pivot chart** L3.0 (`O_M` nbhd of `M` ≅ `Localization.Away f (k[Fin r])`,
  `r=finrank(range δ⁰)`, from `baseChange_normalForm`). KILL-COND: chart not an `AlgEquiv` ⟹ heavy fallback.
- L6.0 (limit lemma: polynomial curve in `O_M` for `t≠0` ⟹ `t=0` limit in `V(vanishingIdeal O_M)`) — FREE,
  bricks verified, independent.
**Build order:** (1) L6.0 [free] → (2) L3.0 pivot chart on (2,2,2) [high-leverage gamble, collapses L2+L3] →
(3) L3.1+L2.* [chart payoff] → (4) L6.1+L6.2 [box-move generation, heavy] → (5) L6.3/6.4/L1 → (6) L4-assembly+L7.
Critical path: L6 stays on it for the dimension (chart gives `dim O_M`; `varietyDim(Z_M)` needs L6.4 ideal equality).
- 2026-06-19: thread 14 (geometry sizing) CLOSED. Next: build L6.0 (limit lemma, free), then the (2,2,2) pivot
  chart witness. L6's degeneration is a 3–4 module sub-library (paper-cited) — anticipated, within mandate; surface
  only if a kill-condition fires.
- 2026-06-19: **L6.0 LANDED** (thread 15, reviewer FAITHFUL) — `Core.PolynomialCurveLimit.curvePoint_zero_mem_zeroLocus_vanishingIdeal`:
  polynomial curve in `Z` for `t≠0` ⟹ `t=0` limit in `zeroLocus(vanishingIdeal Z)`. Weakest hyp `[Infinite k]`
  (no IsAlgClosed; Codex-confirmed sharp). Curve encoding `c : σ → Polynomial k` (feeds L6.1's explicit family).
  Green, axiom-clean. **Next: L3.0 pivot chart on (2,2,2)** — the high-leverage gamble (collapses L2+L3 if it
  lands; fires the L3 kill-condition). Then L3.1+L2.* payoff, then L6.1+L6.2 box-move generation (the heavy core).
- 2026-06-19: **Orbit-variety foundation LANDED** (thread 16, FAITHFUL) — `Core.OrbitVariety`:
  `isPrime_vanishingIdeal_orbitSet` (O_M Zariski-irreducible), orbit map `orbitMap M`, `groupRing d = 𝒪(G_d)`
  domain, `vanishingIdeal_range_orbitMap_eq_ker` (= ker μ_M^*). Bounded (402 LoC). Green (2688 jobs), axiom-clean.
  Prerequisite for chart/L6/L1 in place. **Next: L3.0 pivot chart on (2,2,2)** (high-leverage gamble for L2+L3,
  built on `baseChange_normalForm` + `orbitMap`). Then L6 degeneration (heavy core), L4-assembly, L7.
  Handoff note: this gives O_M irreducible; transferring primeness to Z_M (= orbitRankLocus) needs L6.

## L2/L3 route — chart>descent (thread 17); OPEN: chart-general vs homogeneity (thread 18) [2026-06-19]
Thread 17: smooth-descent rejected (fppf descent of smoothness absent in Mathlib). (2,2,2) chart CERTIFIED
(pivot f=A_1[0,1], r=5=finrank(range δ⁰), graph-ideal=closure-ideal by Gröbner; `R_f̄ ≅ Away f (k[Fin 5])`;
L2: cotangent ≃ Dual(range δ⁰)). Cert in `threads/17-chart-design/findings.md`.
**BUT** that's ONE orbit; hVoigt is general (`M = intervalDirectSum L`). The chart route needs a GENERAL per-orbit
construction — **scale unsized**. The recons compared chart vs descent, NOT chart-general vs the UNIFORM
**homogeneity** route (O_M smooth because homogeneous: generic-smoothness + G-stable smooth locus + transitivity
G·M=O_M; L2 via orbit-map differential dμ_M=δ⁰). For general M, uniform may beat per-orbit charts. **Thread 18
resolves this fork BEFORE building** (a wrong choice risks a large wasted general-chart sub-library).
- 2026-06-19: thread 17 (chart design) CLOSED — chart>descent, (2,2,2) cert ready. Next: thread 18 sizes
  chart-general vs homogeneity for general-M L3/L2; recommend. Then build the chosen route.

## ✅ GEOMETRY ROUTE DECIDED: HYBRID [2026-06-19, thread 18]
Route A (general explicit chart) = SUB-LIBRARY (re-imports L6's Abeasis–Del Fra lace combinatorics; pivot set
`L`-dependent) — REJECTED. **HYBRID** (Codex convergent): homogeneity for L3 + uniform local Jacobian for L2.
Full analysis: `threads/18-geom-route-general/findings.md`. **Updated remaining ladder:**
- **L2a (NEXT, de-risk):** general-CA cotangent↔Jacobian-kernel bridge — `finrank_k(cotangent of V(I) at a
  k-rational point) = finrank(ker Jacobian of generators)` (Mathlib has `Ideal.Cotangent`/`kerCotangentToTensor`
  but not the packaged Zariski-tangent=Jacobian-kernel; the hybrid's shared absent-brick). De-risk on (2,2,2)
  (thread 17 has `ker J_M = range δ⁰` there). Reusable.
- **L2b:** `ker(J_M) = range δ⁰` for our orbit (orbit-map linearisation; (2,2,2) done).
- **L3 (homogeneity, bounded):** (i) Spec-detour generic smoothness (`dense_smoothLocus_of_perfectField` + stalk
  iso — the ONE scheme entry point, `Group/Smooth.lean` runs the same stack); (ii) smoothLocus G-stable (ring-side
  `k`-algebra automorphism `α_P`, `iff_of_equiv`); (iii) transitivity (DONE, `rankPattern_eq_iff_orbit`); (iv)
  smooth witness ∈ open orbit. ⟹ `IsSmoothAt k m_M`.
- **L6:** `orbitRankLocus = Ō_M` (box-move degeneration sub-library, 3–4 modules, paper-cited) — still needed.
- **L1** (`vanishingIdeal Z_M` prime, from L6 + thread-16 O_M irreducible), **L4-assembly**, **L7**.
No new scope explosion — the bounded uniform route exists (homogeneity); the chart-sub-library is avoided.
- 2026-06-19: thread 18 CLOSED — HYBRID decided. Next: L2a de-risk (cotangent↔Jacobian bridge, general CA, (2,2,2) check).
- 2026-06-19: **L2a LANDED + fidelity AUDIT SURVIVED** (thread 19) — `Core.CotangentJacobian.finrank_cotangentSpace_eq_finrank_ker_jacobian`:
  `finrank(cotangent of V(I) at a k-rational point) = finrank(ker Jacobian)`, **unconditional** (no smoothness/
  radical; Codex-confirmed). The shared absent-brick — BOUNDED (~475 LoC, on `Ideal.Cotangent`/`kerCotangentToTensor`).
  Kill-condition did NOT fire. Green (2690 jobs), axiom-clean. Reusable general CA. One audit NOTE (card claimed a
  (2,2,2) in-Lean `example` not in source) — card CORRECTED to honest (external sympy + reviewer's smaller in-Lean
  witnesses); adding the (2,2,2) example = deferred optional polish (lemma bedrock regardless).
  **Next: L2b** — `ker(jacobian) = range δ⁰` for our orbit (the orbit-map linearisation; identifies L2a's
  Jacobian-kernel with `range δ⁰`; (2,2,2) done in thread 17). Then L3 (homogeneity), L6 (degeneration), L1, assembly, L7.

## ⚠⚠ SCOPE SURPRISE — geometry's remaining content IS the quiver-determinantal-ideal sub-library [2026-06-19, thread 20]
L2b sized: NOT a bounded module. Circularity confirmed (orbit-map/smoothness route circular). Both non-circular
routes pull a SUB-LIBRARY: (a) determinantal — `vanishingIdeal(Z_M) = (minors)` prime = **Lakshmibai–Magyar/KMS
quiver-determinantal-ideal theorem** (absent; the ideal-level twin of L6 — so L6+L2b are ONE body of theory the
paper invokes via lace diagrams / cites Abeasis–Del Fra); (b) orbit-stabiliser — needs algebraic-group orbit-
dimension (absent). The CA foundations (L4★, L5, L0) are DONE bedrock; the geometry's irreducible remaining content
is this second foundational sub-library (≈ L4★-scale, possibly larger — it's research-grade quiver-loci theory).
**AUTONOMOUS LOOP PAUSED (cron deleted). SURFACED TO OPERATOR** with options: (a) build the quiver-determinantal
sub-library (zero-cited, another major sub-campaign, subsumes L6); (b) Cite the one orbit-closure/determinantal
theorem the SOURCE PAPER ITSELF cites (Abeasis–Del Fra / Lakshmibai–Magyar) — closes the geometry in modules,
reduces hVoigt to one named standard citation, consistent with the paper + the Aoyagi-RLCT precedent; (c) bank the
CA bedrock, defer the geometry. Decision pending.

## OPERATOR DECISION: BUILD IT (zero-cited) — the geometry-dimension sub-library [2026-06-19]
Operator chose to build the second foundational sub-library. The drive resumes. **Remaining = one sub-campaign:
prove `varietyDim(orbitRankLocus M) = finrank(range δ⁰)` (then L1 + L4-assembly + L7 close hVoigt).** Two
non-circular routes to the core `dim O_M = finrank(range δ⁰)`:
- **(a) Determinantal-KMS:** `vanishingIdeal(Z_M) = (minors)` prime (Lakshmibai–Magyar/KMS) + `ker(J_minors)=range δ⁰`
  + L2a/L4★/L3. Subsumes L6. Reuses landed work.
- **(b) Orbit-stabiliser/fibre-dimension:** `dim O_M = dim G − dim Stab = finrank C⁰ − finrank(ker δ⁰) =
  finrank(range δ⁰)` (rank-nullity LANDED) via Chevalley fibre-dimension + `Stab(M)=Aut(M)` open in `Hom(M,M)=ker δ⁰`
  + `dim Z_M = dim O_M` (closure). Sidesteps L2a/L4★/L3/IsSmoothAt entirely IF Chevalley fibre-dim is in/near Mathlib.
**NEXT (final scoping): sizing recon comparing (a) vs (b)** — pick the genuinely smaller Lean build, produce its
build sub-ladder. Then build, layer by layer. Loop re-armed.
- 2026-06-19: operator BUILD IT. Next: route-sizing recon (determinantal-KMS vs orbit-stabiliser/Chevalley).

## ✅ SCOPE CORRECTED — KMS determinantal sub-library AVOIDED; remaining ~8–10 modules [2026-06-19, thread 21]
Route (a) smooth-point assembly chosen (route (b) needs absent Chevalley fibre-dim + orbit-dimension, reuses no
bedrock — dominated). **Thread 20's scope surprise OVER-STATED:** KMS/Lakshmibai–Magyar determinantal primeness is
NOT needed — take `I = vanishingIdeal(Z_M)` directly (prime from landed `isPrime_vanishingIdeal_orbitSet` + L6),
and L2b via the orbit-map differential `dμ_M=δ⁰` (non-circular), NOT minor Jacobians. So the remaining campaign is
~8–10 modules on LANDED bedrock; the ONE genuine sub-library piece is **L6.2** (box-move/lace degeneration,
Abeasis–Del Fra, 1–2 modules — the paper cites it). NOT a second multi-month sub-library. Full sub-ladder +
assembly chain: `threads/21-route-sizing/findings.md`. Guards: K1 (L6.2 generation = clean diff-induction?),
K2 (L2b via dμ_M=δ⁰, not minor pderivs — else re-imports KMS). [Operator chose BUILD IT under the larger scope;
this is a reduction — continuing the drive, no re-interrupt for good news.]
- 2026-06-19: thread 21 CLOSED — route (a), KMS avoided. Next: de-risk L6.2 (the box-move generation, K1) —
  design+stress-test the degeneration induction + the explicit box-move family, then build L6.1/L6.2.

## L6 DEGENERATION sized [2026-06-19, thread 22]
L6.1 box-move family CERTIFIED (explicit `F(t)`, sympy-verified; rank drop `[a≤i<c]·[b<j≤e]`; perturb one
recombination arrow by `[t,1]`; `t≠0` upstairs orbit via base-change-to-dirSum, `t=0` downstairs, L6.0 ⟹ closure).
L6.2 generation: **K1 fires (scoped)** — move-existence = Abeasis–Del Fra **cover-classification** (covers = linked
box moves), a **2–3 module combinatorial sub-library**, NOT a diff-induction. Within "build it" scope (refinement of
the known-hard L6, not a new sub-library). Route: maximal `u∈[s,r)` + cover-classification. Full: `threads/22-…/findings.md`.
**Next: build L6.1** (certified family — concrete progress + de-risks the L6.0+family degeneration in Lean), then
L6.2 (cover-classification combinatorics on rank patterns), then L6.3/6.4/L1/L2b/L3/assembly/L7.
- 2026-06-19: thread 22 CLOSED — L6.1 certified, L6.2 = 2–3 module cover-classification. Next: build L6.1.
- 2026-06-19: **L6.1 LANDED** (thread 23, reviewer PASS) — `Core.BoxMoveDegeneration`: the degeneration ENGINE
  `mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily` (general in d; consumes L6.0; `[Infinite k]`) +
  certified (1,2,1) box-move witness. Orbit membership via explicit base change (`t⁻¹` only in t≠0 cert, not the
  curve). Green (2691 jobs), axiom-clean. **NAMED GAP:** the general box-move construction (arbitrary `a<c≤b+1≤e`
  + arbitrary `rest`) plugs into the engine but needs `foldDim`-transport + `dirSum`-reindex surgery — next piece.
  Then **L6.2 cover-classification** (the 2–3 module combinatorial sub-library: covers = linked box moves, via
  maximal `u∈[s,r)`), then L6.3/6.4 (ideal equality) → L1 → L2b (dμ_M=δ⁰) → L3 (homogeneity) → L4-assembly → L7.
- 2026-06-19: **L6.3 LANDED** (thread 25, reviewer PASS) — `Core.RankLocusClosed`:
  `isZariskiClosed_orbitRankLocus` + `orbitSet_subset_orbitRankLocus` + easy ideal inclusion
  `vanishingIdeal_orbitRankLocus_le_orbitSet`. The missing Mathlib brick `rank_le_iff_forall_submatrix_det_eq_zero`
  (rank ≤ k ⟺ all (k+1)-minors vanish, over a field) BUILT from scratch. Green (2692 jobs), axiom-clean,
  `[Field k]` only. Commits 935f114/07f2fd1/a088956. This is the EASY direction `Ō_M ⊆ orbitRankLocus M`.
- 2026-06-19: **L6.2 DESIGN — K1 FIRES (scoped)** (thread 24, decorrelated Codex convergent). Generation
  (`s≤r ⟹ O_s⊆Ō_r`, hard dir of Abeasis–Del Fra) reduces to a clean `Φ=Σ(r−s)`-induction GIVEN move-existence.
  Move-existence = sub-fact 1 (linked applicability `m(r)_{[c,b]}≥1`: **ELEMENTARY**, 2nd-difference identity)
  + sub-fact 2 (`∃(a,e)` rect⊆supp(g) ∧ `m(r)_{[a,e]}≥1`: **TRUE on >20,000 verified pairs but NOT elementary —
  logically EQUIVALENT to the AD rank-cover classification**, no closed-form selector). So L6.2 = genuine 2–3
  module sub-library; the load-bearing input (sub-fact 2) is irreducible content, not a freebie.
  - **NEXT (two parallel, in-mandate "drive to the end / zero-cited"):**
    (A) `obstruction`-seat pass on **sub-fact 2** — try the double-extremal induction on supp(g) (peel extremal
        cell, residual stays a valid difference). KILL: if it doesn't close on paper → sub-fact 2 is a genuine
        lace-combinatorics sub-expedition → SURFACE to operator with sized roadmap (this is a boundary-move,
        not a 2–3 module fill). If it closes → build L6.2 at 2–3 modules.
    (B) **L6.1-general** build — the per-move degeneration over arbitrary `rest` (thread-23 named gap), statement
        pinned in thread-24 §4, plugs into the landed `BoxMoveDegeneration` engine. INDEPENDENT of L6.2, bank now.
  - After L6: L6.4 (ideal equality, easy ⊆ done by L6.3) → L1 (primeness) → L2b (dμ_M=δ⁰) → L3 (homogeneity)
    → L4-assembly → L7 (discharge hVoigt).

## 2026-06-20 — L6 nearly closed; geometry half sized (3-front wave)

**L6.2 generation (thread 28) — LANDED** `Core.BoxMoveGeneration`: telescope crux ★
`sum_secondDiff_coveringRect_ge`, move-existence `exists_coveringInterval_diff_pos`, the box move +
rank-drop `r'=r−1_D` + `Φ`-strict-descent, sub-fact 1, and the reusable interface `BoxMoveStep` /
`BoxMoveChain := Relation.ReflTransGen BoxMoveStep`. Green, axiom-clean. Subtlety (caveat in card):
split `c=b+1` puts the corner below-diagonal, so achievability is scoped to `i≤j` (rank pattern's real
domain). **DEFERRED L6.2c** (extremal-cell existence + descent step assembling one `BoxMoveStep` with
`s≤r'<r` + the `Φ`-induction `s≤r → BoxMoveChain r s`) — route clear, verified 198k pairs.

**L6.1-general (thread 27) — split DONE, non-split residual.** `splitMove_intervalDirectSum_mem_closure`:
full §4 list headline for the **split** move × arbitrary `rest` (reviewer PASS). Non-split (`a<c≤b<e`):
scaffolding landed (`splice`, crossing factorization), residual = the **crossing-rank computation**
`rankPattern (splice λ) i j` for `i≤b<j` (~150–250 LoC heavy `Fin`-index, route sympy-certified +
scratch-verified). **= FRONT A (in progress).**

**Geometry assembly ladder (thread 29) — the second-half map.** Build-order DAG in
`threads/29-geometry-assembly-ladder/findings.md`. Key findings:
- **L2b entanglement resolved:** NO standalone `ker Jac = range δ⁰`. Easy: `range δ⁰ ⊆ ker Jac` (orbit
  tangent ⊆ Zariski tangent; guard `dμ_M = δ⁰` = Lie linearization `φ↦φ_{i+1}M_i−M_iφ_i`, NOT minor-pderiv).
  **Hard nugget = L2b★:** `finrank(range δ⁰) ≥ dim O_M`, the **orbit-map submersion**
  `dim O_M = dim G − dim Stab(M)`. **Mathlib v4.29 has NO fibre-dimension theorem, NO G/Stab quotient**
  (grep-confirmed) ⟹ multi-module, possibly a sub-expedition. **= FRONT B (de-risk: is the fibre-dim
  bridge 1–2 modules or a sub-expedition? stabilizer `(End M)ˣ=D(det)` is cheap).**
- **L3 homogeneity = 5–7 modules.** Hardest single lemma `exists_closed_smooth_point_mem_openOrbit`
  (needs `IsOpen O_M`, not just dense; thread-18's caution holds). Spec-detour necessary at v4.29.
- **NEW CORRECTNESS GUARD: `[CharZero k]`** for the geometric reading `orbitLinearCodim = codim Ō`
  (Codex char-p counterexample `𝔾ₐ↷𝔸¹` by `t·x=x+tᵖ`). Fold into L7/L2b + `OrbitCodim.lean`. The L6 half
  (degeneration/generation/closure) stays char-free.
- **WRINKLE:** L2a is fed `g = rankMinorSet M`, but those minors generate an ideal whose **radical** (not
  the ideal) is `vanishingIdeal Z_M` — need a ~1-module "local ideals agree at the smooth point M" lemma
  (guarded by L3 reducedness; de-risk on (2,2,2)).

**SEQUENCING (the discipline: close the first layer hole-free before the next stands on it):**
1. **Close L6 → L1** (first complete, char-free layer = Abeasis–Del Fra `orbitRankLocus M = Ō_M` + its
   primeness, proved ZERO-CITED): Front A (non-split crossing-rank) → L6.2c → L6.4 (ideal equality;
   easy ⊆ landed via L6.3, hard ⊇ = compose `BoxMoveChain` + per-move degeneration) → L1 (primeness,
   1 module given L6.4 + O_M irreducible).
2. **Geometry half:** Front B de-risks L2b★. If bounded → build L3 (5–7) + L2b + assembly + L7 (all with
   `[CharZero k]`). If L2b★ is a genuine multi-week fibre-dimension sub-library → SURFACE to operator with
   a decision-grade roadmap (grind-it vs scoped-CITE for that one submersion step).

## 2026-06-20 (cont.) — L6.1-general CLOSED; L2b★ de-risked → AG half is a sub-expedition

**L6.1-general (thread 27) — FULLY CLOSED.** `nonsplitMove_intervalDirectSum_mem_closure` (non-split §4
headline) + `rankPattern_splice_cross` (crossing-rank crux) landed (reviewer PASS). Both split AND non-split
covers now have the per-move degeneration headline ⟹ **L6.4 is unblocked.** Caveat carried: the headline's
orbit base is left-associated `dirSum (dirSum M_{[a,e]} M_{[c,b]}) (idS rest)` (= `Lup` up to a `dirSum`
re-association, not defeq to right-nested `intervalDirectSum Lup`) — L6.4 needs an explicit assoc/reindex
bridge.

**L2b★ de-risk (thread 30) — VERDICT: bounded SUB-EXPEDITION (~4 modules, route c).** The "explicit
stabilizer collapses it" hunch REFUTED. Both routes reduce to ONE theorem Mathlib v4.29 lacks: **Jacobian
rank ⟹ transcendence-degree bound** (`affine_image_dim_le_const_jacobianRank`, via Kähler differentials of
the image function field, char-0-essential). Target `orbitPullback_dim_le_finrank_range_delta`. Mathlib has
NEITHER fibre-dim NOR `ringKrullDim=trdeg`. (2,2,2) identity `dim O_M = dimG − dim Stab = finrank(range δ⁰)`
checks exactly (codims 3,4 match landed witnesses). **`[CharZero k]` enters ONLY at L2b★/L7** (char-p
counterexample `𝔾ₐ↷𝔸¹` `t·x=x+tᵖ`) — must be added to `OrbitCodim.lean`'s L7/L2b theorems; everything else
(L6, L0, L4d, L2a, M3, the `(C,θ)` engine) stays char-free. Swing risk 4→7 if the Kähler API is thin.

**DECISION (controller):** the de-risk fires the operator-surface kill-condition (AG half = genuine new AG
sub-library, not "small holes"; + a CharZero scope refinement on the geometric-codim headline). **Plan:**
1. **CLOSE the L6 layer first** (in-mandate, unambiguous, completes the first half): L6.2c (chain assembly:
   extremal-cell existence + descent step + `Φ`-induction ⟹ `s≤r → BoxMoveChain r s`) → L6.4 (compose chain
   + per-move degeneration ⟹ `orbitRankLocus M ⊆ Ō_M`, combine with L6.3 easy ⊆ ⟹ `vanishingIdeal Z_M =
   vanishingIdeal O_M`; handle the assoc bridge) → L1 (primeness from O_M irreducible). Deliverable:
   **Abeasis–Del Fra `orbitRankLocus M = Ō_M` + its primeness, ZERO-CITED, char-free** — the first half done.
2. **THEN SURFACE** a consolidated checkpoint to the operator: L6 half complete; AG half = bounded
   sub-expedition (L2b★ ~4–7 [new Jacobian-rank⟹trdeg theorem] + L3 ~5–7 [homogeneous-space smoothness via
   Spec detour] + assembly), `[CharZero k]` scope refinement. Recommend driving it to completion (in-mandate),
   flag the scope-surprise + CharZero for ratification, offer scope options.

## 2026-06-20 (cont.) — ★ L6 FULLY CLOSED ★ (first half of the hero task delivered)

**`orbitRankLocus M = Ō_M` (Abeasis–Del Fra) PROVEN, zero-cited, char-free.** `Core.OrbitClosure`
(thread 31, reviewer PASS-WITH-NOTES): `vanishingIdeal_orbitRankLocus_eq_orbitSet` (ideal-level),
`image_orbitRankLocus_eq_repClosure_orbitSet` (set-level k-points, any infinite field, NO IsAlgClosed),
`isPrime_vanishingIdeal_orbitRankLocus` (primeness, `[IsAlgClosed k]`, = L1). The per-step crux dissolved
via the rank-pattern bridge (geometric per-move lemmas invoked in their own shapes, reconciled by "same
rankPattern ⟹ same orbit ⟹ same repClosure" — no defeq list-matching). New infra: `repClosure` algebra,
`baseChangePullback` (change-of-vars hom for G_d-stability). Green (2695 jobs), all headlines axiom-clean.
Head `733cf56`.

**This completes the ENTIRE combinatorial/degeneration content the paper only CITES** (Abeasis–Del Fra
Thm 3.8 hard direction): L6.0 limit · L6.1 engine+witness · L6.1-general (split+nonsplit per-move
degeneration) · L6.2 (telescope ★ + move-existence + generation chain) · L6.3 (rank locus closed) · L6.4
(orbit closure = rank locus) · L1 (primeness). Proved zero-cited, char-free.

**Geometric foundation now in hand for the AG half:** `Z_M = orbitRankLocus M` is the orbit closure Ō_M,
irreducible, with prime vanishing ideal — exactly what L0 (Nullstellensatz codim) consumes.

**→ SURFACING to operator** (per plan): L6 half complete; AG half (L2b★ ~4–7 [new Jacobian-rank⟹trdeg
theorem Mathlib lacks] + L3 ~5–7 [homogeneous-space smoothness via Spec detour] + assembly + L7) is a
bounded but substantial sub-expedition, with a `[CharZero k]` scope refinement on the geometric-codim
headline. Awaiting scope decision: full zero-cited grind / scoped-CITE the one trdeg step / bank L6 + defer.

## 2026-06-20 — AG HALF sub-campaign (operator: FULL ZERO-CITED) — scaffold

Discharge `hVoigt`: `codimRep (canonicalCoord d) (orbitRankLocus M) = orbitLinearCodim M`, via
`varietyDim(Z_M) =[L0,L1✓] #σ−codimRep`, `varietyDim =[L4d✓] ringKrullDim(AtPrime m_M) =[M3✓,needs L3]
finrank(cotangent) =[L2a✓] finrank(ker Jac) =[L2b] finrank(range δ⁰) = #σ−orbitLinearCodim✓`.
LANDED bricks: L0 (`NullstellensatzCodim`), L1 (`isPrime_vanishingIdeal_orbitRankLocus`), L4d, M2, M3, L2a.
`Z_M = Ō_M` irreducible/prime ✓ (L6). All AG-half headlines carry **`[CharZero k]`** (char-p counterexample);
engine + L6 + RLCT-over-ℝ/ℂ stay char-free.

**Ladder + build-order DAG:**
- **A0** [build, short, char-free] `dμ_M = δ⁰` (orbit-map differential = coboundary `φ↦φ_{i+1}M_i−M_iφ_i`) +
  **L2b-easy** `range δ⁰ ⊆ ker Jac` (μ_M lands in Z_M=orbitRankLocus ✓ ⟹ orbit directions ⊆ Zariski tangent).
  Independent. Bank first. (δ⁰ + tangent side live in `Core.OrbitCodim`.)
- **A1** [scout, quick] pin Mathlib v4.29 Kähler/trdeg API for L2b★ (`Algebra.trdeg`, `KaehlerDifferential`,
  `rank Ω`, `trdeg ≤ rank Ω`) — the thread-30 **4-vs-7-module swing factor**.
- **A2** [scout, quick] pin L3 Spec-detour API (`Scheme.Hom.dense_smoothLocus_of_perfectField`,
  `StructureSheaf.stalkIso`/`AtPrime ≃ stalk`, `IsSmoothAt` unfold) + whether **`IsOpen O_M`** (open orbit)
  is reachable (L3.3, thread-29's most-likely-to-break).
- **A3** [build, ~5–7 mod, needs A2] **L3** `IsSmoothAt k m_M` via homogeneity: L3.0 G-action ring autos ·
  L3.1 G-stable smooth locus (`FormallySmooth.of_equiv`) · L3.2 smooth closed point (Spec detour, hardest) ·
  L3.3 smooth pt ∈ open orbit · L3.4 assemble.
- **A4** [build, ~4–7 mod, needs A1, `[CharZero k]`] **L2b★** target `orbitPullback_dim_le_finrank_range_delta`
  via the NEW theorem `affine_image_dim_le_const_jacobianRank` (Jacobian rank ⟹ trdeg, Kähler diff of image
  function field). Route c (thread 30). The irreducible nugget.
- **A5** [build, ~1 mod, needs A3] **§WRINKLE** — L2a is fed `rankMinorSet M` but those minors generate an
  ideal whose RADICAL is `vanishingIdeal Z_M`: "local ideals agree at the smooth point M" (guarded by L3
  reducedness; de-risk on (2,2,2)).
- **A6** [build, ~1–2 mod, needs A3,A4,A5] **L4-assembly + L7** — compose ⟹ discharge `hVoigt`, add `[CharZero k]`
  to L7/L2b in `OrbitCodim.lean`.

**Build waves:** W1 = A0 (build) ∥ A1 (scout) ∥ A2 (scout). W2 = A3 ∥ A4 (from A1/A2). W3 = A5, A6.
**Surface to operator** only at completion (hVoigt discharged → close PR) or if A4's Kähler API / A3's IsOpen-O_M
inflates beyond the sizing (genuine new blocker).

## 2026-06-20 — AG half W1 results (A0 built, A1/A2 recon) → refined A3/A4 plans

**A0 LANDED** `Core.OrbitPullbackDim.varietyDim_eq_ringKrullDim_range_orbitPullback`:
`varietyDim(Z_M) = (ringKrullDim (orbitPullback M).range).unbotD 0`, `image μ_M^*` a DOMAIN. Char-free
(`[Infinite k]`; a brick honestly weakened from `[IsAlgClosed k]`). Reviewer PASS. The route-c first link.

**A1 recon (thread 33) — route-c = 4 modules (cheap branch).** `ringKrullDim = trdeg` (f.g. domain) ABSENT
as named but CHEAP via landed `ringKrullDim_quotient_eq_noetherRank` + the present `trdeg` API. Hardest =
the **char-0 Jacobian criterion** `trdeg_k(image) ≤ generic-rank(Jac μ_M^*)` (genuinely absent, char-0).
**SOUNDNESS FLAG (Codex):** naive "identity differential rank ≥ image dim" is FALSE (`t↦t²`); rescued ONLY
by **constant rank under the G-action** (homogeneity) ⟹ identity-rank = generic-rank. A4 plan (4 mod):
A4.1 `ringKrullDim(range)=trdeg(range)` · A4.2 char-0 Jacobian criterion (HARDEST, de-risk gate) · A4.3
`dμ_M@e = deformationδ M M` + constant-rank-under-G (holds soundness) · A4.4 assemble + chain A0.
Target: `(ringKrullDim (orbitPullback M).range).unbotD 0 ≤ finrank k (LinearMap.range (deformationδ M M))`.

**A2 recon (thread 34) — L3 = ~6 modules; thread-29 break-point DISSOLVES.** `IsOpen O_M` was the WRONG
target (orbitSet M = closed points, not open). **Route DENSE:** orbit closed points DENSE
(`vanishingIdeal {orbit closed pts} = ⊥`, cheap L6 rewrite) ∩ dense-open smooth locus ⟹ smooth pt is an
orbit pt. All bricks (i)–(iv) PRESENT (`dense_smoothLocus_of_perfectField`, `pointEquivClosedPoint`,
`StructureSheaf.stalkIso`, `FormallySmooth.of_equiv`, `baseChangePullback` landed, `residueFieldIsoBase`).
A3 plan (6 mod): L3.0 G-action α_P ≃ₐ (mostly landed) · L3.1 iff_of_equiv transfer · L3.2 Spec model +
generic smoothness (TIME SINK = instance plumbing, not deep math; de-risk: stand up instance skeleton as a
sorry-free `example` first) · L3.3 dense orbit closed pts (cheap) · L3.4 assemble (smooth_of_grpObj template).
`[IsAlgClosed k]` (perfect field).

**L2b final equality structure (for A6):** `finrank(range δ⁰) = varietyDim(Z_M)` by SQUEEZE:
(≤) `range δ⁰ ⊆ ker Jac` [easy] + chain `finrank(ker Jac)=varietyDim` [L2a✓+M3✓(needs L3=A3)+L4d✓];
(≥) route c [A4]. The easy `range δ⁰ ⊆ ker Jac` is a small piece for A6.

**W2 dispatched:** A3 (L3 build, Route DENSE, 6-mod, land-what-closes) ∥ A4.2 de-risk (pen-and-paper: char-0
Jacobian-criterion certificate + the constant-rank-under-G soundness handling, before the A4 build).
