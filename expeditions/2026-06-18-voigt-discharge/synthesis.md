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

- **L0 — Nullstellensatz / point-space ↔ PrimeSpectrum bridge.** `[IsAlgClosed k]`: `vanishingIdeal` of a
  point set ↔ radical ideal ↔ closed subscheme; height of `vanishingIdeal(Z)` = codim of the Zariski closure;
  irreducible closed set ↔ prime. *Size: module. Gates everything.* Status ☐
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
