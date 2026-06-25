**Verdict:** build `chartPhiLoc` as an independent `aevalTower`, but make its fibre/coefficient leg use the same landed `gaugeSub d endpointGauge`. Do not try to make the whole chart equivalence a direct descent of the single `gaugeEquiv`; use `gaugeEquiv` only as the round-trip engine.

**A. Recommended Φ Shape**

Introduce two Φ-side legs, not one:

```lean
-- source coordinate in O(Σ)[1/dsig]
def sigmaCoordT : RepCoord d → Localization.Away (chartDsig k d r hp hq) :=
  fun x ↦ algebraMap _ _ (Ideal.Quotient.mk _ (X x))

-- Schur variables read from the product matrix M = mult(A)
def chartPhiVarSub : SchurVar q p r → Localization.Away (chartDsig k d r hp hq)
```

Your current `chartPhiVarSub` skeleton is the right definition.

Then add the Schur-localized coefficient map:

```lean
def chartPhiSchurAeval :
    MvPolynomial (SchurVar q p r) k →ₐ[k] Localization.Away (chartDsig k d r hp hq) :=
  MvPolynomial.aeval (chartPhiVarSub k d r hp hq)

theorem chartPhiSchurAeval_detSchurS :
    chartPhiSchurAeval k d r hp hq (detSchurS q p r)
      = algebraMap _ _ (chartDsig k d r hp hq)

def schurToDsig :
    SchurLoc q p r →ₐ[k] Localization.Away (chartDsig k d r hp hq) :=
  IsLocalization.liftAlgHom
    (M := Submonoid.powers (detSchurS q p r))
    (f := chartPhiSchurAeval k d r hp hq)
    ...
```

Now define the forward-gauged fibre coordinate map:

```lean
def chartPhiTower :
    MvPolynomial (RepCoord d) (SchurLoc q p r) →ₐ[k]
      Localization.Away (chartDsig k d r hp hq) :=
  MvPolynomial.aevalTower (schurToDsig k d r hp hq) (sigmaCoordT k d r hp hq)

def chartPhiFibSub : RepCoord d → Localization.Away (chartDsig k d r hp hq) :=
  fun x ↦ chartPhiTower k d r hp hq
    (gaugeSub d (endpointGauge (k := k) d r hp hq) x)

def chartPhiFibAeval :
    MvPolynomial (RepCoord d) k →ₐ[k] Localization.Away (chartDsig k d r hp hq) :=
  MvPolynomial.aeval (chartPhiFibSub k d r hp hq)
```

Descend this through the fibre vanishing ideal:

```lean
def chartPhiCoeff :
    sweepFibreRing k d r hp hq →ₐ[k] Localization.Away (chartDsig k d r hp hq) :=
  Ideal.Quotient.liftₐ _ (chartPhiFibAeval k d r hp hq) ...
```

Then the actual Φ map on `P = MvPolynomial SchurVar O(F)` is:

```lean
def chartPhiAeval :
    MvPolynomial (SchurVar q p r) (sweepFibreRing k d r hp hq) →ₐ[k]
      Localization.Away (chartDsig k d r hp hq) :=
  MvPolynomial.aevalTower
    (chartPhiCoeff k d r hp hq)
    (chartPhiVarSub k d r hp hq)
```

Finally localize at `gF`; prove

```lean
chartPhiAeval k d r hp hq (chartGfib k d r hp hq)
  = algebraMap _ _ (chartDsig k d r hp hq)
```

so the image is a unit, and define `chartPhiLoc` by `IsLocalization.liftAlgHom`.

**B. Round-Trip Strategy**

Do not do fraction algebra by hand. Use localization extensionality to reduce to generators, then use one gauge identity.

The load-bearing lemma should be a transported version of landed `aeval_gaugeSub_gaugeSub`:

```lean
-- schematic
theorem aevalTower_gaugeSub_gaugeSub
    (χ : SchurLoc q p r →ₐ[k] T) (v : RepCoord d → T)
    (P Q : BaseChangeGroup (k := SchurLoc q p r) d) (x : RepCoord d) :
    MvPolynomial.aevalTower χ
        (fun y ↦ MvPolynomial.aevalTower χ v (gaugeSub d P y))
        (gaugeSub d Q x)
      =
    MvPolynomial.aevalTower χ v (gaugeSub d (Q * P) x)
```

Specialize to `Q = P⁻¹` or `P = Q⁻¹`; then `Q * P = 1` and the result is `v x`.

Minimal seam-E generator checks:

```lean
-- h2: Φ ∘ Ψ = id on Away dsig
∀ x : RepCoord d,
  chartPhiLoc (chartPsiSub k d r hp hq x) = sigmaCoordT k d r hp hq x

-- h1, Schur variables
∀ s : SchurVar q p r,
  chartPsiLoc (chartPhiVarSub k d r hp hq s)
    = algebraMap _ _ (X s)

-- h1, O(F)-coefficients; quotient/MvPolynomial ext reduces to:
∀ x : RepCoord d,
  chartPsiLoc (chartPhiCoeff k d r hp hq
    (Ideal.Quotient.mk _ (X x))) = fibCoordT k d r hp hq x
```

The Schur-variable identity comes from the already-landed `map_chartPsiAeval_multPoly_eq`: the Ψ-image of the product matrix is `L * E * H`, whose `Δ`, `B12`, and `B21` blocks are exactly the Schur generators.

**C. About “Descend The Single gaugeEquiv”**

Not preferable as the main construction. `gaugeEquiv d endpointGauge` lives on

```lean
MvPolynomial (RepCoord d) (SchurLoc q p r)
```

and only changes `RepCoord` variables. The chart equivalence also has to expose the base Schur coordinates and quotient by the fibre/Σ vanishing ideals. So descending the single `gaugeEquiv` would require proving the same ideal-transport and base-coordinate reconstruction facts anyway.

Use `gaugeEquiv` as the algebraic engine, not as the whole chart.

**D. Most Likely Break Point**

The brittle step is Φ descent of `chartPhiFibAeval` through `vanishingIdeal F`: proving the symbolic `endpointGauge` evaluated via `schurToDsig` is the pointwise `chartGauge (mult A)` on the open set. Isolate this as an evaluation lemma before the descent proof.

API-wise, the relevant names are already used in this repo at the v4.29 pin: `IsLocalization.liftAlgHom`, `Localization.algHom_ext`, `MvPolynomial.aevalTower`, `MvPolynomial.algHom_ext'`, `MvPolynomial.map_aeval`, `IsLocalization.mk'_surjective`, `IsLocalization.lift_mk'_spec`, and `AlgEquiv.ofAlgHom`.
