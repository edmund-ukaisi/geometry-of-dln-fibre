Short answer: yes for h2, your suspected intermediate lemma is the right one. The clean route is to turn the cross-ring problem into two ordinary tower-composition lemmas, proved by `MvPolynomial.algHom_ext'`. Do not open localization fractions.

**A. Mechanism**

Prove leg lemmas first:

```lean
chartPhiLoc_algebraMap :
  chartPhiLoc k d r hp hq (algebraMap _ (Localization.Away (chartGfib k d r hp hq)) p)
    = chartPhiAeval k d r hp hq p

chartPhiLoc_comp_schurToGfib :
  (chartPhiLoc k d r hp hq).comp (schurToGfib k d r hp hq)
    = schurToDsig k d r hp hq

chartPhiLoc_fibCoordT :
  chartPhiLoc k d r hp hq (fibCoordT k d r hp hq x)
    = chartPhiFibSub k d r hp hq x
```

Then the tower lemma:

```lean
theorem chartPhiLoc_comp_chartPsiTower [Infinite k] :
    (chartPhiLoc k d r hp hq).comp (chartPsiTower k d r hp hq)
      =
    MvPolynomial.aevalTower
      (schurToDsig k d r hp hq)
      (chartPhiFibSub k d r hp hq) := by
  apply MvPolynomial.algHom_ext'
  · rw [AlgHom.comp_assoc]
    rw [show (chartPsiTower k d r hp hq).comp
          (IsScalarTower.toAlgHom k _ _) = schurToGfib k d r hp hq by
        rw [chartPsiTower]
        exact MvPolynomial.aevalTower_comp_toAlgHom _ _]
    rw [chartPhiLoc_comp_schurToGfib,
        MvPolynomial.aevalTower_comp_toAlgHom]
  · intro x
    rw [AlgHom.comp_apply, chartPsiTower, MvPolynomial.aevalTower_X,
        chartPhiLoc_fibCoordT, MvPolynomial.aevalTower_X]
```

`chartPhiLoc_comp_schurToGfib` is proved by `Localization.algHom_ext` on `SchurLoc`; on structure-map elements it is:

```lean
schurToGfib_algebraMap
chartPhiLoc_algebraMap
chartPhiAeval_map_algebraMap
schurToDsig_algebraMap
```

So yes: `liftAlgHom` collapses cleanly, but only after you isolate the coefficient/variable legs.

**B. Gauge Tower Identity**

The shape is right, but for h2 the order is:

```lean
P = endpointGauge
Q = endpointGauge⁻¹
Q * P = endpointGauge⁻¹ * endpointGauge
```

not the other way around. The tower identity should be stated as:

```lean
theorem aevalTower_gaugeSub_gaugeSub
    {T : Type*} [CommRing T] [Algebra k T]
    (χ : SchurLoc (k := k) (d 0) (d (Fin.last (N+1))) r →ₐ[k] T)
    (v : RepCoord d → T)
    (P Q : BaseChangeGroup
      (k := SchurLoc (k := k) (d 0) (d (Fin.last (N+1))) r) d)
    (x : RepCoord d) :
    MvPolynomial.aevalTower χ
      (fun y ↦ MvPolynomial.aevalTower χ v (gaugeSub d P y))
      (gaugeSub d Q x)
      =
    MvPolynomial.aevalTower χ v (gaugeSub d (Q * P) x)
```

Proof idea: use `MvPolynomial.map_aeval` to identify the left side with

```lean
MvPolynomial.aevalTower χ v
  (MvPolynomial.aeval (gaugeSub d P) (gaugeSub d Q x))
```

then rewrite by landed:

```lean
aeval_gaugeSub_gaugeSub d P Q x
```

and fold `gaugeSub d (Q * P) x`.

The different Ψ/Φ legs are not present inside this lemma. For h2, after `chartPhiLoc_comp_chartPsiTower`, everything lands in `Away dsig` with

```lean
χ = schurToDsig k d r hp hq
v = sigmaCoordT k d r hp hq
```

For the h1 coefficient leg, the symmetric version lands in `Away gF` with

```lean
χ = schurToGfib k d r hp hq
v = fibCoordT k d r hp hq
```

**C. h2 Generator Trace**

For `x : RepCoord d`:

```lean
chartPhiLoc (chartPsiSub x)
= chartPhiLoc (chartPsiTower (gaugeSub d eg⁻¹ x))
= aevalTower schurToDsig chartPhiFibSub (gaugeSub d eg⁻¹ x)
= aevalTower schurToDsig
    (fun y ↦ aevalTower schurToDsig sigmaCoordT (gaugeSub d eg y))
    (gaugeSub d eg⁻¹ x)
= aevalTower schurToDsig sigmaCoordT (gaugeSub d (eg⁻¹ * eg) x)
= aevalTower schurToDsig sigmaCoordT (gaugeSub d 1 x)
= sigmaCoordT x
```

Lean ending:

```lean
rw [aevalTower_gaugeSub_gaugeSub]
rw [inv_mul_cancel, gaugeSub_one, MvPolynomial.aevalTower_X]
```

possibly with a local `let eg := endpointGauge ...` to control rewriting.

**D. Likely Breakpoints**

For h2, the fragile step is `chartPhiLoc_comp_schurToGfib`: it mixes `SchurLoc`, `Away gF`, `Away dsig`, `Away.mapₐ`, and `liftAlgHom`. Use `Localization.algHom_ext`; do not use `mk'_surjective`.

For h1, the SchurVar half is the real extra work. It is not a gauge-coordinate round-trip. Prove:

```lean
chartPsiLoc (chartPhiVarSub k d r hp hq s)
  = algebraMap _ (Localization.Away (chartGfib k d r hp hq)) (X s)
```

by cases on `s`, using `map_chartPsiAeval_multPoly_eq`. The top-left case is essentially `submatrix_map_chartPsiAeval_eq_schurΔ`; you likely need analogous `B12` and `B21` block read-off lemmas.

Best API list: `Localization.algHom_ext`, `IsLocalization.liftAlgHom_apply`, `IsLocalization.lift_eq`, `Ideal.Quotient.liftₐ_apply`, `Ideal.Quotient.lift_mk`, `MvPolynomial.algHom_ext'`, `MvPolynomial.map_aeval`, `MvPolynomial.aevalTower_comp_toAlgHom`, `MvPolynomial.aevalTower_comp_algebraMap`, `MvPolynomial.aevalTower_C`, `MvPolynomial.aevalTower_X`.
