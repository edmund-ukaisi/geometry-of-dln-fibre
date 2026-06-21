# Thread 07 — Phase B (orbit geometry) architecture recon (scout, 2026-06-19)

## DECISION: Route A (concrete affine). Route S (schemes) rejected.
Route A is the only route avoiding a **scheme→`ringKrullDim` dimension bridge**. Our whole stack —
`codimRep`, `varietyDim`, L0 (`codimRep = #σ − varietyDim`), L5 (catenary `height + ringKrullDim = n`) — is
point-set / `MvPolynomial` / `ringKrullDim (R⧸I)`. Route A stays there. Route S forces TWO absent bridges:
(1) model `G_d = ∏GL`/orbit/orbit-map/rank-locus as compatible `Scheme`/group objects (0 hits in
`AlgebraicGeometry/` — no GL-scheme, no orbit-scheme, no action-morphism); (2) transport scheme dimension
back to `ringKrullDim` (only link: `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`). Decorrelated Codex
(xhigh, view-withheld) independently chose A with the same bridge reasoning + same hardest lemma.

**Irreducibility needs NO point-space topology** — delivered as `(vanishingIdeal Z).IsPrime`
(`Spec(R⧸I)` irreducible ⟺ `R⧸I` domain ⟺ `I` prime), exactly what L0 consumes.

## Target (pinned against the actual defs)
- `δ⁰ = deformationδ M M`, `δ⁰(φ)_i = φ(i.succ)·M_i − M_i·φ(i.castSucc)` IS the orbit-map differential at `P=1`
  (`(P•A)_i = P_{i+1} A_i P_i⁻¹`); `range δ⁰` = tangent-to-orbit.
- Phase A proved `orbitLinearCodim M = finrank C¹ − finrank(range δ⁰) = dim Ext¹`; L0 gives
  `codimRep + varietyDim = Nat.card σ` (prime vanishing ideal).
- **Phase B owes exactly: `varietyDim(orbitRankLocus M) = finrank(range δ⁰)`** (+ the primeness hypothesis).
  L7 then chains `codimRep = #σ − varietyDim = finrank C¹ − finrank(range δ⁰) = orbitLinearCodim`. ∎
- `n = Σ_i d_{i+1} d_i = finrank C¹` (canonicalCoord is a linear entry-flattening).

## Build ladder (Route A, dependency order)
- **L1** — Ō_M irreducible AS primeness of the rank-locus ideal `(vanishingIdeal(canonicalCoord '' orbitRankLocus M)).IsPrime`.
  `O_M = range μ_M` = image of irreducible `∏GL` (principal-open `D(det)`, domain localisation) under a
  polynomial map ⟹ closure irreducible ⟹ ideal prime. *Module.* (pairs with L6's set-equality, Phase D.)
- **L2** — orbit-map differential = `range δ⁰` (Jacobian/cotangent linearisation): Zariski tangent of `V(I)` at
  `M` (via `MvPolynomial.pderiv` / `Ideal.cotangentSpace`) = `range δ⁰`. *Sizeable, load-bearing — the
  conceptual heart.* Entirely to-build.
- **L3** — `M` smooth point of Ō_M by homogeneity (`G_d` transitive, smooth locus `G`-stable + dense ⟹ smooth
  everywhere) + orbit-open-in-Ō_M. *Module→sizeable.* **Crux = density** (only scheme-side density theorem
  `dense_smoothLocus_of_perfectField` exists; ring-side `smoothLocus` gives openness not density — build
  ring-side density from `FormallySmooth.of_perfectField`, or a minimal `Spec`-only detour WITHOUT modelling
  `G_d` as a scheme).
- **L4** — smooth ⟹ `IsRegularLocalRing` ⟹ `varietyDim = finrank(range δ⁰)`. *Module, hardest finish.*
  (a) smoothLocus membership at `m_M` ⟹ `IsRegularLocalRing (Localization.AtPrime m_M)` [ABSENT bridge];
  (b) `IsRegularLocalRing.iff_finrank_cotangentSpace`; (c) `ResidueField = k` so `finrank = finrank(range δ⁰)`
  (from L2); (d) local↔global `ringKrullDim(AtPrime m_M) = ringKrullDim(R⧸I) = varietyDim` (closed point;
  `AtPrime.ringKrullDim_eq_height` + L5).

## Hardest sub-lemmas + kill-condition
1. **L4(a)** smoothLocus membership ⟹ `IsRegularLocalRing` — ABSENT (`IsRegularLocalRing` only has `Defs`),
   standard CA from scratch. Shared with Route S. (Codex's named hardest.)
2. **L2** `finrank(CotangentSpace at M) = finrank(range δ⁰)` — the conceptual heart.
3. **L4(d)** local↔global dim `ringKrullDim(R⧸I) = ringKrullDim(AtPrime m_M)`.
**KILL-CONDITION:** if L4(a)+L4(d) need a substantial regular-locus / local↔global-dim CA *sub-library* (not
modules), Route A inflates — but this does NOT favour S (obligations shared); it favours building the
regular-local-ring bridge as its own network-free `Core` module first.

## Recommended next move (controller adopting): size the hard middle first
A focused tide on **L4(a) (smooth ⟹ regular local ring) + L4(d) (local↔global dim)** — the kill-condition CA,
reusable + standalone — to settle whether the regularity finish is module-scale (same discipline that de-risked
L5). Then L2 (the Jacobian identification), then L3 (density), L1, L4-assembly.

## Rejected third routes (Codex-corroborated)
- Orbit-stabiliser `dim O = dim G − dim Stab` (`Stab = ker δ⁰`): needs fibre-dimension/orbit-scheme/stabiliser
  smoothness — all absent; cost ≈ S.
- Rational parametrization / local slice (reuse `baseChange_normalForm`): bespoke chart algebra; hold as
  fallback if L3 density is expensive.
- Determinantal / quiver-rank-locus height: 2026-06-17 probe showed non-CI (excess intersection, needs
  Schubert/KMS + catenary); larger than A.

Codex artefacts: `threads/07-L1-geometry-recon/codex/arch-{prompt,answer}.md`.
