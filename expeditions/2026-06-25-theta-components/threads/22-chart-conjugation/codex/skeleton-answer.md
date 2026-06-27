**1. Transport Status**

- `vanishingIdeal(sweepSigma)`: **genuinely invariant**, hence equal after `map` by `baseChangeAlgEquiv P`. Reason: `mult (P • A) = P_last * mult A * P_0⁻¹`, so rank `≤ r` and rank `= r` loci are stable under endpoint units.

- `ΔPdeep`: **carried to the `(s,t)` deep minor**, provided the endpoint permutations are oriented so that the first `r` rows/cols of `mult (P • A)` are exactly rows `s` and cols `t` of `mult A`, in that order. Otherwise expect a unit/sign multiple. This is a cheap determinant identity.

- `chartDsig`: **carried to the `(s,t)` chart element after quotient descent**, not definitionally in the same raw expression. You need the induced equiv
  `sweepSigmaRing ≃ₐ[k] sweepSigmaRing`, using ideal invariance, and then:
  `EΣ (mk I Δ_top) = mk I Δ_st`.

- `chartGfib / SchurVar / detSchurS / sweepFibreRing`: **not literally transported by `baseChangeAlgEquiv P`**. That equiv acts on the tuple coordinate ring. The Schur side is a separate top-left model ring. Also, `sweepFibreRing` is the fibre over the fixed top-left normal form; endpoint permutation generally sends that fibre to a conjugate fibre, not itself.

- `chartLocalizedAlgEquiv`: **not carried as a whole-chain equality** unless you build extra Schur/fibre conjugation isos. The naive failure is exactly here: the source denominator transports cheaply, but the target Schur construction is top-left typed and is not acted on by `baseChangeAlgEquiv P`.

**2. Clean Formulation**

Use option **(a)**.

Define:
```lean
deepMinorAt s t := det ((Matrix.of (multPoly d)).submatrix s t)
chartDsigAt s t := Ideal.Quotient.mk I (deepMinorAt s t)
```

Let `E := baseChangeAlgEquiv P` and descend it:
```lean
EΣ : sweepSigmaRing k d r ≃ₐ[k] sweepSigmaRing k d r
```

Prove:
```lean
EΣ (chartDsig top) = chartDsigAt s t
```

Then get the localization equiv:
```lean
L_st : Localization.Away (chartDsigAt s t)
       ≃ₐ[k] Localization.Away (chartDsig top)
```
using `EΣ.symm`.

Finally:
```lean
e_st :=
  L_st.trans (chartLocalizedAlgEquiv k d r hp hq)
```

Cheap parts: ideal invariance, determinant identity, quotient descent, localization-away transport.

Expensive part, avoid unless needed: proving a separately defined per-pivot Schur chart equals this transported one generator-by-generator.

**3. Same Schur Side**

Using the same `Away chartGfib` for every pivot is a **feature**, not a bug.

It means every pivot chart is first moved to the standard top-left base chart, then trivialized against the same fixed fibre model. That is a standard atlas choice: local bases differ, but their coordinate rings are all identified with the same standard Schur chart by permutations.

This delivers a coherent atlas if the local data records the source chart denominator and the base-coordinate change. The transitions are then:
```lean
e_st ∘ e_uv.symm
=
eβ ∘ L_st ∘ L_uv.symm ∘ eβ.symm
```
on the appropriate double localization. The cocycle law is formal from composition; identifying it with your “ambient cocycle” is still a proof obligation.

**4. Minimal Deliverables**

1. **Determinant/ideal conjugation lemmas.**  
   Best first module. Dependencies: `mult_smul`, `eval_baseChangePullback`, quotient descent, localization-away transport. Rough size: 200-500 LoC, depending on permutation-unit infrastructure.

2. **One non-top-left pivot as `LocalTrivializationDatum`.**  
   Depends on (i) plus the existing top-left `chartLocalizedAlgEquiv`. Rough size: another 200-500 LoC if the datum API is already clean.

3. **Full per-pivot family + cocycle => `locallyTrivial`.**  
   Depends on cover indexing, overlap localizations, transition restrictions, and cocycle comparison. Rough size: 600-1500+ LoC. This is probably not one tide.

Right stopping point for one module: **(i), plus the reusable `e_st` definition skeleton**. If time remains, instantiate one concrete non-top-left pivot.

**5. Likely Hidden Rung**

The likely extra rung is **overlap restriction/cocycle identification**.

Even if `e_st` is easy to define, the transition lives on a double localization where both pivot minors are inverted. Showing that the transported transition equals the pre-existing ambient cocycle will require denominator bookkeeping and compatibility of the localization maps. That is more than “we have the ambient cocycle already.”