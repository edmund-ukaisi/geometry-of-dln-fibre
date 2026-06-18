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
- **L5 — ★ height–dimension formula / catenary.** `height I + dim(R/I) = dim R`, i.e. `dim = trdeg`, for
  finite-type domains / `MvPolynomial` over a field. **`IsCatenary` is 0% in Mathlib.** *Size: sub-library.
  THE RISK — size first.* ☐
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
1. **Size L5 first** (highest VOI — it dominates total size; if it's a multi-module CA sub-library the
   expedition's shape changes). A `pen-and-paper`/scout traces `NoetherNormalization` + `AlgebraicIndependent`
   → `dim = trdeg` and reports the gap size + the cleanest target form (Codex: *smooth `k`-point of `V(I)` with
   tangent dim `t` ⇒ `I.height = n − t`*).
2. In parallel/after: **L0** (gates all, well-bricked) as the first build tide.
3. Then Phase B geometry, Phase C, Phase D, Phase E.

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
