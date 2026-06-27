<task>
Lean 4 + Mathlib v4.29 formalisation. I am formalising the "flatness payoff" (S3) of a fibre-bundle
construction. I must decide the HONEST statement to prove and a "cheap-flatness verdict": is flatness
provable cheaply (miracle/generic flatness or trivially) WITHOUT routing through the bundle atlas /
Schur charts / rank bridge? I want your independent read on the mathematics and the right Lean
statement shape.

## The concrete objects (all already in the repo, sorry-free)

- `Base := sweepSigmaRing k d r := MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (sweepSigma k d r)`,
  the coordinate ring O(Σ̄^r) of the closure of the rank-exactly-r product locus. A finite-type
  k-algebra (a quotient of a polynomial ring). `k` is a field (for the corollaries: alg-closed,
  char 0, infinite).

- `rankROpen d r : Set (PrimeSpectrum Base)` — DEFINED as the complement of the common-vanishing
  locus V({chartDsigAt s t}) of the "pivot minors" chartDsigAt s t ∈ Base (the r×r minors of the
  universal product matrix, pushed into Base). So rankROpen = ⋃_{s,t} basicOpen (chartDsigAt s t)
  (proved: `iSup_pivot_basicOpen_eq_rankROpen`).

- S1 keystone (proved): for a prime P of Base, `P ∈ rankROpen ↔ (universal matrix over κ(P)).rank = r`.

- The per-pivot atlas: for each pivot (s,t), the chart TOTAL ring is
  `Total_{s,t} := Localization.Away (chartDsigAt s t)` — a localization of `Base`. The atlas carries
  a k-ALGEBRA equiv (trivialization): `Total_{s,t} ≃ₐ[k] SchurLoc ⊗[k] sweepFibreRing`, where
  `SchurLoc := Localization.Away (detSchurS …)` (a localized polynomial ring over k, regular of
  dimension δ) and `sweepFibreRing := MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (sweepFibre …)`
  is the FIBRE coordinate ring.

- "The structure map of the bundle's coordinate ring over the base" is the algebra map
  `Base → Total_{s,t}` (the bundle total space, chartwise, sits over the base via this map). On each
  chart this map is precisely the localization map `Base → Localization.Away (chartDsigAt s t)`.

## My current reading of the cheap-flatness verdict

Each chart's structure map `Base → Localization.Away (chartDsigAt s t)` is a LOCALIZATION, and a
localization is ALWAYS flat (`IsLocalization.flat` / localizations are flat ring maps). This needs
NEITHER the Schur trivialization, NOR the rank bridge, NOR generic/miracle flatness — it is automatic.
So "flat over the base, chartwise" is essentially free, and the trivialization to SchurLoc ⊗ sweepFibreRing
is irrelevant to base-flatness (it pins the FIBRE structure, not flatness over the base). The genuine
content of S3 is then: (a) which precise statement is non-vacuous and load-bearing, and (b) the
corollaries (UniversallyOpen.of_flat, rankAtStalk locally constant).

I worry this reading makes S3 almost trivial / mis-scoped — that the INTENDED flatness is a different
map (e.g. the map to a DIFFERENT base, like the target Mat^{=r}, or the projection of the FIBRE family
mult⁻¹(B) → rankROpen), where flatness is genuine content.

## Questions

1. Is my cheap-flatness verdict correct: that `Base → Localization.Away (chartDsigAt s t)` is flat
   purely because it is a localization, independent of the atlas/rank-bridge? Any subtlety I am
   missing (e.g. does "structure map of the bundle" mean something other than this localization map)?

2. Given the objects above, what is the HONEST, non-vacuous, name=content flatness statement to
   register for S3? Rank these candidate readings by how load-bearing / honest they are:
   (A) chartwise: each `Base → Localization.Away (chartDsigAt s t)` is flat (localization);
   (B) global-over-rankROpen: the structure sheaf of the total space restricted over rankROpen is
       flat over O_rankROpen — does this need a gluing step beyond (A)? Is "flat is local on the base"
       the right tool, and is it cheap given (A)?
   (C) the fibre family `mult⁻¹(B) → rankROpen` is flat — is THIS the genuine target, and is it
       reachable from the atlas (chart = SchurLoc ⊗ sweepFibreRing, base-change of a k-algebra over
       the field k is flat)? Or is this a different, harder object?
   (D) miracle flatness (CM source + regular base + equidim fibres) or generic flatness as a route
       to a GLOBAL flatness — is either cheap here, and does either bypass the charts?

3. If (A) is the honest reachable statement and (B)/(C) need gluing I should NOT overclaim, tell me
   to state (A) chartwise and NAME the gap. If (C) is genuinely the intended payoff and reachable via
   the SchurLoc ⊗ sweepFibreRing trivialization (flat = stable under base change; every k-algebra is
   flat over the field k), tell me to route through the atlas for (C).

4. Corollaries: with flatness in hand (whichever reading), are `UniversallyOpen.of_flat` (needs
   LocallyOfFinitePresentation) and `Module.isLocallyConstant_rankAtStalk` (needs Flat) genuinely
   applicable to the chart map `Base → Localization.Away (chartDsigAt s t)`, or do they want the
   scheme-morphism `AlgebraicGeometry.Flat` class on Spec(Total) → Spec(Base)? Which is cheaper.
</task>

<output_contract>
Four numbered sections matching the four questions. For Q2, give an explicit ranking (most-honest /
most-load-bearing first) with one line each on reachability and on the vacuity risk. End with a single
"VERDICT" line: the one statement shape I should SPECIFY first, and whether the cheap route exists
(yes/no + which lemma).
</output_contract>

<grounding_rules>
You are reasoning about standard commutative algebra / algebraic geometry; flag any claim that depends
on a Mathlib lemma you are not sure exists at v4.29 as "needs API check". Distinguish "mathematically
true" from "cheaply formalisable in Lean v4.29". Do not invent Mathlib lemma names; if you reference one,
mark it as a name to verify.
</grounding_rules>
