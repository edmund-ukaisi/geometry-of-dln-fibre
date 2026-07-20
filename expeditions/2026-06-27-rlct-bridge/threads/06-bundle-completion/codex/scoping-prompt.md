<task>
Design review for a Lean 4 + Mathlib (v4.29) formalisation thread. I am completing the fibre-bundle
geometry of the multiplication map of deep linear networks (Lehalleur–Rimányi). The library is very
mature; I must NOT overclaim. I want your independent judgement on REACHABILITY and the HONEST CEILING
of two open items, and which is the highest-value reachable increment.

SETUP (precise object names, all in namespace DLNFibre.Core, k a field, often [Infinite k], over a
dimension vector d : Fin (N+2) → ℕ and a rank r):

- `mult : Tuple d → Matrix (Fin d_last) (Fin d_0) k` is the matrix-product map; `Σ^r` is the
  rank-exactly-r product locus, `Σ̄^r` its closure (rank ≤ r).
- `sweepSigmaRing k d r := MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(Σ^r)` is the coordinate ring of
  the SOURCE/TOTAL locus Σ̄^r (this is the source of `mult`, NOT the target base).
- The target/base matrix space coordinate ring is `MvPolynomial (Fin d_last × Fin d_0) k`. The
  comorphism of `mult` is `multComap d : MvPolynomial (Fin d_last × Fin d_0) k →ₐ[k] MvPolynomial
  (RepCoord d) k`, sending the target entry variable X(r,c) ↦ multPoly d r c = (mult d genericTuple) r c.
- `rankROpen d r ⊆ PrimeSpectrum (sweepSigmaRing)` is the rank-exactly-r open; PROVED equal to the
  residue-field rank-=r locus (S1, `mem_rankROpen_iff_rank_universalMatrixResidue_eq`).
- Per pivot (s,t) (an r×r selector pair), the chart is `Localization.Away (chartDsigAt d r s t)`
  (a localization of `sweepSigmaRing`). The pivot charts cover `rankROpen`.
- `SchurLoc q p r := Localization.Away (detSchurS …)` is a localization of the polynomial ring
  `MvPolynomial (SchurVar …) k` in the SCHUR-BLOCK entry variables — these are the target/base
  rank-chart coordinates (the Schur complement parametrizing rank-=r matrices near a pivot).
- `sweepFibreRing k d r hp hq := O(F)` is the coordinate ring of the fixed normal-form fibre F.
- BANKED (S4b, all sorry-free, axiom-clean): per pivot there is an HONEST structure map
  `schurToDsigAt : SchurLoc →ₐ[k] Away (chartDsigAt s t)` (= awayCongr(gauge) ∘ schurToDsig, where
  schurToDsig = chartPhiLoc ∘ schurToGfib, schurToGfib = IsLocalization.Away.mapₐ of the coefficient
  base-change). Over the schurToDsigAt-induced SchurLoc-algebra structure:
    `chartDsigAt_schurLocTensorEquiv : Away (chartDsigAt s t) ≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing`
  AND `chartDsigAt_flat_over_schurLoc : Module.Flat SchurLoc (Away (chartDsigAt s t))`.
  Also PROVED: `chartDsigAt_tensorEquiv_schurToDsigAt : triv (schurToDsigAt x) = x ⊗ₜ 1` (so the triv is
  already an AlgEquiv over the NAMED base map schurToDsigAt — the "over-base" compatibility against
  schurToDsigAt is DONE).
- BANKED (thread 23, atlas `PivotLocalProductAtlas`): the scheme open-cover, per-pivot
  `LocalTrivializationDatum`, and the PAIRWISE BASE-SIDE overlap cocycle `chartOverlapTransition I J`
  over `sweepSigmaRing` (= `awayOverlapTransition (pivotElt I)(pivotElt J)` from localization
  initiality), with laws: round-trip (`_trans_symm`), base-normalization (`_commutes`),
  overlap-LOCAL restriction (`_restrict`: the transition restricted to the single chart on the double
  overlap = canonical `chartToSwappedOverlap`). PLUS `transitionFactors` / a gauge-factoring lemma:
  `triv I ≪≫ (triv J).symm` (between the FIXED-target single chart rings) factors through the base-ring
  gauges (the deep chart e_β cancels), so it is base-algebraic.

THE TWO OPEN ITEMS (the residual to a global `Flat π` / FiberBundle over rankROpen):

(1) PROJECTION COMPATIBILITY. Prove `schurToDsigAt : SchurLoc → Away(chartDsigAt s t)` IS the pullback
    of `mult`'s projection — i.e. the in-chart base direction SchurLoc agrees with the geometric
    projection `mult⁻¹(B) → Mat^{=r}` restricted to the chart. Concretely this seems to require
    identifying SchurLoc (a localization of the Schur-block target coordinate ring) with the target
    rank-chart presentation, and tracing `multComap` through the gauge + deep-chart equivalences to land
    on `schurToDsigAt`. The structure map was built from the gauge-conjugated DEEP CHART (the
    route-β chart AlgEquiv), NOT from multComap, so the identification is a genuine new compatibility.

(2) R1 OVERLAP-GLUING / target-side cocycle. The atlas carries BASE-SIDE overlap data only. R1 needs the
    per-chart PRODUCT trivializations (target = SchurLoc ⊗ sweepFibreRing, but the SchurLoc-base differs
    per chart via different gauges) to be identified on overlaps — a TARGET-side cocycle
    `targetOverlapTransition` — to assemble one global FiberBundle / Flat π morphism over all of
    rankROpen.

What I already know / suspect:
- The chartwise SchurLoc-flatness + over-base triv is LANDED; the genuine missing geometric content is
  (1) tying schurToDsigAt to mult, and (2) the global gluing.
- A bare global `Flat π` is probably NOT reachable cheaply: the per-chart SchurLoc base rings are
  different localizations conjugated by different gauges, so even the BASE of the bundle is presented
  chart-locally, not globally.
- The base-side overlap cocycle + `transitionFactors` (deep chart cancels, residual = relative gauge
  P_J·P_I⁻¹) may be exactly the ingredient to glue, OR may be a red herring for the TARGET side.

QUESTIONS:
A. Is PROJECTION COMPATIBILITY (1) reachable as a clean Lean statement+proof at modest cost (say ≤ a few
   hundred lines, reusing banked equivalences), or is it a multi-module build? What is the SHARPEST
   honest statement of it that is actually provable here — e.g. an equality of two AlgHoms
   `SchurLoc → Away(chartDsigAt)` (schurToDsigAt vs a multComap-derived map), or a weaker compatibility?
   Give the exact algebraic identity to target and the most likely Mathlib lemma(s)/obstruction.
B. For R1 (2): can the existing base-side `chartOverlapTransition` + `transitionFactors` be assembled
   into a genuine TARGET-side overlap cocycle on `SchurLoc ⊗ sweepFibreRing`, or is that the wrong
   object? If a full global `Flat π` is out of reach, what is the STRONGEST genuine intermediate that IS
   reachable (e.g. a per-pair target-side trivialization-transition AlgEquiv with cocycle laws, stated
   honestly as "pairwise, not a bundled triple cocycle")? Name it.
C. Given the maturity and the honesty constraints, RANK the candidate increments by value/cost:
   (1) projection compatibility; (2a) target-side pairwise overlap cocycle; (2b) a global Flat π;
   plus any I'm missing (e.g. packaging the chartwise SchurLoc-flatness into a clean reusable
   "chartwise Flat over the named base map" headline that names the open residual). Which one or two
   should I build, and which should I roadmap as the honest ceiling?
D. The single biggest TRAP to avoid here (a statement that would look like progress but be vacuous or
   subtly wrong). Be specific to this setup.
</task>

<output_contract>
Four sections A, B, C, D in that order. Be concrete and terse. In A and B give the exact Lean-level
identity/object to target and the key lemma or the obstruction. In C give a ranked list (1 line each
with a value/cost verdict). In D name ONE trap and how to detect it. Do not pad. No code dumps longer
than a few lines.
</output_contract>

<grounding_rules>
You do not have the repo. Reason from the setup I gave; where you must guess Mathlib API names or
internal structure, FLAG it as inference, not fact. Distinguish "I can see this is reachable from what
you described" from "this likely needs X which you didn't confirm exists". Do not invent banked lemmas.
</grounding_rules>
