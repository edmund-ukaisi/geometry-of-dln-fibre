**1. Verdict**

ROUTE-3: package ROUTE-1 as a thin reusable localized-poly-extension lemma. Do not pursue ROUTE-2.

**2. ROUTE-2**

No: in general `O(Σ^r)` is not an unlocalized free polynomial extension over `O(F)`. The Schur/gauge coordinates are regular only after inverting `detΔ`; globally `B22 = B21 Δ⁻¹ B12` needs division and the exact-rank closure is glued from charts. One-chart density gives dimension no-drop, not a global product-coordinate-ring isomorphism.

**3. Intermediate Lemma Chain**

Let:
```lean
IΣ := MvPolynomial.vanishingIdeal k Σ
IF := MvPolynomial.vanishingIdeal k F
OΣ := MvPolynomial τ k ⧸ IΣ
OF := MvPolynomial σ k ⧸ IF
P  := MvPolynomial SchurVar OF
dΣ : OΣ := Ideal.Quotient.mk IΣ detΔ
gF : P := algebraMap (MvPolynomial SchurVar k) P detSchurS
```

1. **Localized chart equivalence**
```lean
noncomputable def chartLocalizedAlgEquiv :
    Localization.Away dΣ ≃ₐ[k] Localization.Away gF
```
Build denominator-valued substitutions with `MvPolynomial.aeval`; descend from `MvPolynomial τ k` by:
```lean
Ideal.Quotient.liftₐ IΣ f
  (by intro p hp; -- p ∈ IΣ -> f p = 0)
```
Use `Ideal.quotientMapₐ J f H` only when the target is explicitly `B ⧸ J`, with obligation:
```lean
H : I ≤ J.comap f
```
not `Ideal.quotientMap`, unless you only want a ring hom. For maps out of an away localization use:
```lean
IsLocalization.liftAlgHom
```
with obligation `∀ y : Submonoid.powers dΣ, IsUnit (f y)`.

2. **Variable-gauge descent**
```lean
theorem chart_aeval_vanishingIdeal_le :
    IΣ ≤ RingHom.ker chartAeval.toRingHom
```
or the equivalent pointwise `Ideal.Quotient.liftₐ` obligation. `FibreNormalForm.vanishingIdeal_image_smul` is not directly reusable: it is for fixed `k`-gauges. Here the gauge is Schur/det-variable and lives after localization. Reuse its proof pattern, but do the comorphism at `IsLocalization` level.

3. **Submonoid-localized equivalence API**
If you have a denominator-free `AlgEquiv h : R ≃ₐ[A] P`, localize it with:
```lean
IsLocalization.algEquivOfAlgEquiv
  (S := S) (Q := Q) h
  (H : Submonoid.map h M = T)
```
For away localizations the obligation is usually:
```lean
H : Submonoid.map h (Submonoid.powers f) = Submonoid.powers g
by
  rw [Submonoid.map_powers, h_f]
```
Useful simp/API: `IsLocalization.algEquivOfAlgEquiv_eq`,
`IsLocalization.algEquivOfAlgEquiv_mk'`.

4. **No-drop twice**
```lean
theorem source_noDrop :
    ringKrullDim (Localization.Away dΣ) = ringKrullDim OΣ :=
  ringKrullDim_localizationAway_eq_of_avoids_top_minimalPrime ...

theorem schur_noDrop :
    ringKrullDim (Localization.Away gF) = ringKrullDim P :=
  ringKrullDim_localizationAway_eq_of_avoids_top_minimalPrime ...
```
Schur side needs a local lemma producing a top minimal prime of `P` avoided by `gF`; use that `detSchurS` has a unit `k`-coefficient monomial. `MvPolynomial.quotientEquivQuotientMvPolynomial` is the right quotient-polynomial API if you lift a top component of `OF`.

5. **Packaged Route-3 lemma**
```lean
theorem ringKrullDim_eq_of_localized_polyExtensionAlgEquiv
    [Finite SchurVar] [IsNoetherianRing OF]
    (e : Localization.Away dΣ ≃ₐ[k] Localization.Away gF)
    (hΣ : ringKrullDim (Localization.Away dΣ) = ringKrullDim OΣ)
    (hP : ringKrullDim (Localization.Away gF) = ringKrullDim P) :
    ringKrullDim OΣ = ringKrullDim OF + Nat.card SchurVar := by
  rw [← hΣ, ringKrullDim_eq_of_ringEquiv e.toRingEquiv, hP,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]
```
Then convert through `varietyDim`/`unbotD 0`.

**4. Most Likely Wall**

The dangerous wall is trying to prove the localized chart equivalence through `sigmaIdeal`/`IadDeep`/`fibreGenIdeal` strict generator equalities. Mitigation: formulate every descent against `vanishingIdeal` membership and point-evaluation on the principal open; use radical-insensitivity only for dimensions, never generator-ideal equality.

**5. Module Count**

About 5 new modules: localized poly-dim wrapper, Schur-side no-drop/component lift, variable-gauge comorphism descent, localized chart `AlgEquiv`, final `hSweep` wiring. Add one more if the `detΔ` top-component avoidance certificate is not yet formalized in Lean.