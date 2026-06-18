**1. (a) Verdict**

Lean-pragmatic rank: **(iii) > (ii) > (i)**. Standard literature claim: the Ringel 2-term sequence is the textbook Ext¹ computation for hereditary quivers/path algebras, not a bespoke shortcut. Use (iii) first: define `Ext1Ringel M N := C¹(M,N) ⧸ LinearMap.range δ`, prove interval formulas and additivity concretely. Keep (ii) as the clean derived bridge: build the path category/functor category, standard projective resolution, then prove `CategoryTheory.Ext M N 1 ≃ Ext1Ringel M N`. Put (i) last for this pin: algebraically standard, but Mathlib has no path algebra, and verified `ModuleCat.finite_ext` assumes `[CommRing R]`, so it does not apply to noncommutative `kQ`.

**2. (b) Verdict**

The finrank route is mathematically honest **only after** citing/proving the AG bridge. Pure linear algebra proves the normal-space identity
`Rep_d ⧸ LinearMap.range δ ≃ Ext1Ringel M M`.
To call this genuine `codim (orbit closure)`, you still need: orbit locally closed; `dim closure = dim orbit`; `dim orbit = dim G - dim Stab`; `Stab = Aut(M)` open in `End(M)` and smooth; tangent image equals orbit tangent space. Standard AG/Voigt claim: citable in exposition. Lean theorem claim: must be proved or assumed; Mathlib does not currently supply this orbit-dimension package.

**3. Build On**

1. Verified: `LinearMap.range`, `LinearMap.ker`, `Submodule.Quotient`, `(LinearMap.range f).mkQ` for Ringel cokernels and normal quotients.

2. Verified: `LinearMap.finrank_range_add_finrank_ker`, `Submodule.finrank_quotient_add_finrank`, `Module.finrank_linearMap` for all dimension arithmetic.

3. Verified: `CategoryTheory.Ext`, `CategoryTheory.ProjectiveResolution`, `CategoryTheory.functorCategoryAbelian`, plus `Ext.biprodAddEquiv` / `Ext.biproductAddEquiv` for the later derived-Ext bridge.

**4. Biggest Risk**

The main risk is scope drift: proving a clean finrank Voigt-normal-space theorem, then accidentally presenting it as genuine orbit-closure codimension in Lean. Keep the AG bridge as an explicit theorem/assumption boundary.