1. **B.** Use `endpointGauge` over `SchurLoc`: `SchurLoc → Away gF` is a clean `IsLocalization.Away.mapₐ`, while A would require new CommRing-level `L/H/chartGauge` plumbing because `Lmatk/Hmatk/chartGauge` are still concrete `[Field k]` definitions.

2. **The Ψ Substitution.** Let
`q := d 0`, `p := d (Fin.last (N+1))`,
`OF := sweepFibreRing k d r hp hq`,
`PF := MvPolynomial (SchurVar q p r) OF`,
`T := Localization.Away (chartGfib k d r hp hq)`,
`SL := SchurLoc (k := k) q p r`,
`P := endpointGauge (k := k) d r hp hq`.

Define the fibre-coordinate evaluator
```lean
fibCoordT : RepCoord d → T
| x => algebraMap OF T
    (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (MvPolynomial.X x))
```

Then for `x = ⟨i, (rr, cc)⟩`,
```lean
X x ↦
  MvPolynomial.aeval (R := SL) fibCoordT
    (gaugeSub d (P⁻¹) x)
```

Equivalently:
```lean
RepCoord d
  -- gaugeSub d (endpointGauge⁻¹)
  → MvPolynomial (RepCoord d) SL
  -- aeval fibCoordT, coefficients via SL → T
  → T
```

So:
```lean
chartPsiAeval : MvPolynomial (RepCoord d) k →ₐ[k] T :=
  MvPolynomial.aeval (R := k) psiSub
```
with `psiSub x` as above. The inverse is correct: `Ψ(M,B) = chartGauge(M)⁻¹ • B`.

3. **Connecting Algebra Map.** It exists cleanly:
```lean
schurToGfib : SL →ₐ[k] T :=
  IsLocalization.Away.mapₐ SL T
    (MvPolynomial.mapAlgHom (σ := SchurVar q p r) (Algebra.ofId k OF))
    (detSchurS (k := k) q p r)
```

Load-bearing named API, present in v4.29/local tree:
`MvPolynomial.mapAlgHom`, `IsLocalization.Away.mapₐ`, `IsLocalization.Away.mapₐ_apply`, `IsLocalization.map_eq`, `MvPolynomial.aeval`, `MvPolynomial.aeval_X`, `MvPolynomial.comp_aeval_apply`.

The key definitional fact is:
```lean
MvPolynomial.map (algebraMap k OF) (detSchurS q p r)
= chartGfib k d r hp hq
```
by the definition of `chartGfib`.

4. **Single Biggest Wall.** Not the coefficient map. The wall is proving the inverse-gauge substitution descends and round-trips: you need a tailored `Ψ` product reconstruction lemma, essentially
```lean
aeval fibCoordT (gaugeEquiv d P⁻¹ (multPoly d rr cc))
  = (forced Schur chart matrix entry rr cc in T)
```
using `gaugeEquiv_multPoly` at `P⁻¹`, `endpointGauge_zero/last`, the fibre relation `mult B = normalForm`, and a generic `L * E * H` Schur-factorization over the localized target.

5. **Third Construction.** Not needed. B is clean; A is the one that reopens the `L/H` construction.