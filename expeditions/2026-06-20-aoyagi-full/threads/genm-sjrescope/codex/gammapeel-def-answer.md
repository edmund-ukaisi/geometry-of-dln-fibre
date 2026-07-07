**VERDICT:** B for the definition this tide.

**FAITHFULNESS CHECK:** Candidate B is faithful: it is exactly the per-`(t,ρ,κ)` chart contribution of the original integrand, with no Schur/block-coordinate distortion.  
For `sjBoundaryPeel`, B gives the honest inequality from front split + pivot-chart cover; no extra analytic constant is needed for the raw chart cover, so take `C = 1` unless later reindexing conventions force a harmless finite-count constant.  
The box integral is over `{rank ≥ 1}` up to the null `{0}` locus; the `t=1` charts already cover it, and summing over `t=1..min` only adds nonnegative terms.  
Main false-statement risk for B: forgetting the `matBox ∩ pivotChart ρ κ` restriction, or claiming equality with the full box after summing all `t` without correcting for multiple chart overlap. It is a cover inequality, not a disjoint decomposition.

**WELL-FOUNDEDNESS:** With `t ≥ 1`, `sjJointResolution` is not the old circular statement: each chart has an invertible `t×t` pivot, so the Schur/Gram reduction has positive peeled rank.  
No `t ≥ 1` pivot chart equals the whole box, since it imposes invertibility of a specific minor.  
The only circular case is `t=0`, whose pivot condition is vacuous and recovers the whole box contribution.

**RISK on A:** Biggest risk is baking the sheared coordinate domain into the definition: the `Γ` domain depends on `A,B,C`, invertibility, complement subtypes, and box reindexing. A tiny mismatch in the coordinate map or domain makes `sjBoundaryPeel` false or unusably hard to state.

**Downstream Lemma for B:** Pin a named sorry of the form:

```lean
gammaPeelIntegral_eq_shearedSchur :
  gammaPeelIntegral M t ρ κ c'
    =
  ∫ A' in tailBox,
    ∫ A in pivotBlockBox ∩ IsUnit,
    ∫ B in blockBox,
    ∫ C in blockBox,
    ∫ Γ in {Γ | Γ + C * A⁻¹ * B ∈ DBox},
      (frobSq (A * Qtilde_p) + frobSq (C * Qtilde_p + Γ * Q_b)) ^ (-c')
```

where all row/column splits are via the `ρ,κ` complement equivalences, and `Qtilde_p = Q_p + A⁻¹ * B * Q_b`. This lemma is the honest bridge from raw chart contribution to the cross-coupled Schur form consumed by `sjJointResolution`.