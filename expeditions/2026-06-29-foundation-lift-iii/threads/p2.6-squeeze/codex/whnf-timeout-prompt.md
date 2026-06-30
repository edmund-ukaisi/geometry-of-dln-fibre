<task>
Lean 4 (Mathlib v4.29) elaboration: a `(deterministic) timeout at whnf` (200000 heartbeats, also fails
at 1,000,000) when applying ONE lemma. Diagnose the likely cause and give the cheapest fixes (ranked).

CONTEXT. I have an abstract theorem (builds fine standalone, sorry-free, axiom-clean):

```
namespace AlgebraicGeometry.Group.Orbit
theorem varietyDim_eq_finrank_range_δ
    [CharZero k] [PerfectField k]
    (G : AffineGVarietyDeformation k) [Finite G.ρ]
    (δAdj : G.C1 →ₗ[k] G.C0)
    (L : (FractionRing G.R ⊗[k] G.C0) →ₗ[FractionRing G.R] KaehlerDifferential k (FractionRing G.R))
    (hMC : G.DifferentialFactors δAdj L)
    (hRank : finrank k (LinearMap.range δAdj) = finrank k (LinearMap.range G.δ))
    (hcrit : DiffIndepCriterion k G.R)
    {I : Ideal (MvPolynomial G.ρ k)}
    (H : G.InfinitesimalAction I)
    [FiniteDimensional k (H.basePtIdeal).Cotangent]
    [hI : I.IsPrime] [hm : (H.basePtIdeal).IsMaximal] [Algebra.IsSmoothAt k (H.basePtIdeal)]
    (hrat : Ideal.ResidueField (H.basePtIdeal) ≃ₐ[k] k)
    {Z : Set (G.ρ → k)}
    (hZ : MvPolynomial.vanishingIdeal k Z = I)
    (hIker : I = RingHom.ker G.toAffineGVariety.pullback.toRingHom) :
    varietyDim Z = (finrank k (LinearMap.range G.δ) : ℕ∞)
```

`AffineGVarietyDeformation` is a `structure ... extends AffineGVariety` carrying `(C0 C1 : Type u)`,
`δ : C0 →ₗ[k] C1`, with `ρ : Type`, `R : Type u` an integral-domain `k`-algebra, `fρ : ρ → R`.
`H.basePtIdeal : Ideal (MvPolynomial G.ρ k ⧸ I)` is defined as `RingHom.ker (basePtA)` where
`basePtA := Ideal.Quotient.liftₐ I H.basePt _`.

I want to re-derive the concrete DLN squeeze by applying this lemma at a concrete instance
`dlnOrbitDef M : AffineGVarietyDeformation k` (whose `.ρ = RepCoord d`, `.R = groupRing d`,
`.δ = deformationδ M M` all by `rfl`), `H := dlnInfinitesimalAction M : (dlnOrbitDef M).InfinitesimalAction (orbitIdeal M)`.
The goal is `varietyDim (canonicalCoord d '' orbitRankLocus M) = (finrank k (range (deformationδ M M)) : ℕ∞)`.

I provide (as `haveI`/`have`) the instances keyed SYNTACTICALLY on `(dlnInfinitesimalAction M).basePtIdeal`:
maximality (= `orbitPointIdeal_isMaximal M 1`, where `normalFormIdeal M := orbitPointIdeal M 1` and the
defeq `(dlnInfinitesimalAction M).basePtIdeal = normalFormIdeal M` holds because `basePt = aeval (...)` is
syntactically the map defining `orbitEval M 1`), smoothness, `FiniteDimensional ... .Cotangent`, `IsPrime`.
Then:

```
exact varietyDim_eq_finrank_range_δ (dlnOrbitDef M) (deltaT M) ((pairMC M).liftBaseChange K)
  (dlnOrbitDef_differentialFactors M) (finrank_range_deltaT M) diffIndepCriterion_groupRing
  (dlnInfinitesimalAction M) hrat (Z := canonicalCoord d '' orbitRankLocus M)
  (vanishingIdeal_orbitRankLocus_eq_orbitSet M) hIker
```

This times out at `whnf`. The TWO sibling re-derivations that go through the SAME defeq
`(dlnInfinitesimalAction M).basePtIdeal = normalFormIdeal M` SEPARATELY each build fast:
- R5: `exact (dlnInfinitesimalAction M).finrank_range_δ_le_finrank_cotangent` (B3),
- R6: `exact finrank_cotangent_eq_varietyDim (orbitIdeal M) (normalFormIdeal M) (residueField...) (...)` (B4),
where R6 passes `m := normalFormIdeal M` EXPLICITLY (not `H.basePtIdeal`).

A repo memory note says: "a whnf timeout can MASK a universe mismatch — composing theorems must match Type
level". Both the abstract lemma and the DLN code use `variable {k : Type u}`.
</task>

<output_contract>
1. RANKED list of the most likely root causes of the whnf blowup (≤4), each one line, flagging which is
   inference vs. certain.
2. For the top cause, the CHEAPEST concrete fix as a Lean tactic snippet (e.g. `set`/`change`/explicit
   `@`-application with instance args / proving the equation with `m` explicit then `exact`/`convert`).
   Give 2–3 alternative fixes ranked by likelihood-of-working, each ≤4 lines.
3. Whether providing instances keyed on `H.basePtIdeal` (vs the reduced `normalFormIdeal M`) could itself be
   the trigger (instance search exploring a defeq), and how to sidestep.
4. One sentence: is bumping `maxHeartbeats` an acceptable fix here or a band-aid masking a real mismatch?
</output_contract>

<grounding_rules>
This is a design/diagnosis consult: clearly mark each claim as (CERTAIN from Lean semantics) vs (INFERENCE
about my specific code). Do not assume you can see the files; reason from the elaboration model. The fix I
adopt will be built+verified locally before trusting it.
</grounding_rules>
