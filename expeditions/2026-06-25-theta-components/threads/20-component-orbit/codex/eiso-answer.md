**Adjudication**

Target **(ii)**. The chart transport gives a **principal-open component identification**, not a global component-ring isomorphism.

The clean statement is:

```text
Away( image of detSchurS in MvPolynomial SchurVar (R_F ⧸ I) )
  ≃ₐ[k]
Away( image of ΔPdeep in orbitRing (realizerD m) )
```

for some full-`d`, corner-`r` Kostant label `m`.

Equivalently:

```text
(MvPolynomial SchurVar (R_F ⧸ I))[1/g_I]
  ≃ₐ[k]
(orbitRing (realizerD m))[1/Δ_m]
```

This is the strongest thing directly supported by the built chart pieces.

**Answers To The Fork**

1. The shape before remembering denominators is indeed “poly wrapper on the fibre side, full-`d` orbit side,” not the consumer’s shifted-orbit shape. But the actual chart theorem is explicitly localized:
`Away chartDsig ≃ Away chartGfib` in [ChartLocalizedAlgEquiv.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/lean/DLNFibre/Core/ChartLocalizedAlgEquiv.lean:87). The localization survival lemmas preserve top components by avoidance/no-drop; they do not remove the localization. See the explicit non-unit localization setup in [TopDimMinPrimesLocalization.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/lean/DLNFibre/Core/TopDimMinPrimesLocalization.lean:12).

2. The consumer target
```text
R_F ⧸ I ≃ₐ[k] MvPolynomial η (orbitRing M_shifted)
```
is not reachable from this chart transport, and I would treat it as globally false in general unless proved by a separate denominator-free fibre normal form theorem. The Schur coordinates are pivot-chart coordinates. On the Schur side, `gF` is `detSchurS` in a polynomial ring over `O(F)` [ChartLocalizedCoordinates.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/lean/DLNFibre/Core/ChartLocalizedCoordinates.lean:45); modulo `I`, this is still a nonconstant determinant polynomial over the domain `R_F ⧸ I`, hence not a unit in nondegenerate cases. So the chart only sees `D(g_I)`, not the whole `fibre component × A^δ`.

3. The clean target to build is:

```text
exists_localized_schurComponent_fullOrbitEquiv
```

with content:

```text
∃ m hm,
  Localization.Away g_I
    (MvPolynomial SchurVar (sweepFibreRing k d r hp hq ⧸ I))
    ≃ₐ[k]
  Localization.Away Δ_m
    (orbitRing (realizerD (k := k) hm))
```

Here `m` is a full-`d` corner-`r` label coming from the sigma top component, not a shifted `d-r` orbit. The sigma endpoint already gives the global unlocalized quotient
`O(Σ̄^r) ⧸ q ≃ orbitRing (realizerD m)` [FibreComponentOrbit.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/lean/DLNFibre/Core/FibreComponentOrbit.lean:210), but the passage through the chart localizes at `Δ`.

4. The global version of (i),
```text
MvPolynomial SchurVar (R_F ⧸ I) ≃ orbitRing (realizerD m)
```
is not the right deliverable. The localized version is valuable and non-vacuous: it is the honest dense chart identification, labels the fibre component by a full-`d` orbit component, and gives the birational/stable geometric content. But stating it without `Away` would overclaim.

I would not spend 500 lines trying to feed `isSmoothAt_sweepFibre_of_component_orbitPolyEquiv`. That interface encodes a stronger global product theorem than the chart transport supplies. Build the localized full-`d` orbit statement instead, and treat any shifted-orbit product iso as a separate theorem requiring new global geometry/gluing.