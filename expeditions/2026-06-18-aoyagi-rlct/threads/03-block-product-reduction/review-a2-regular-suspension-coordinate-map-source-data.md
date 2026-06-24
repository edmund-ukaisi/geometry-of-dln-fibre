# Review - A2 regular-suspension coordinate map source data

Date: 2026-06-24.

Reviewer: xhigh `Halley the 4th`.

Verdict: pass.

## Scope Checked

The reviewer checked the current `expedition/aoyagi-rlct` worktree read-only
and confirmed that `RegularSuspensionCoordinates.lean` compiles with the
Pi-valued coordinate map slice present.

## API Shape

The compiling coordinate maps are:

```text
paperEndpointFixedBaseRegularBlockCoordinateMap
paperEndpointFixedBaseResidualBlockCoordinateMap
paperEndpointFixedBaseProductDifferenceCoordinateMap
```

They have the intended shape:

```text
(U0 : Submodule K (reverseVertex W 0))
(hU0 : IsCompl U0 (LinearMap.ker (paperTotalMap W B)))
(Cedge : alpha -> forall p : Fin N,
  reverseVertex W p.castSucc ->L[K] reverseVertex W p.succ)
(x : alpha)
  -> CoordinateIndex ... -> K
```

The compiling source-data theorems are:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_centered_continuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData.residualBlockCoordinateMap_centered_continuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_centered_continuousAt
```

Each theorem proves:

```text
map x0 = 0 /\ ContinuousAt map x0
```

## Fidelity Notes

The reviewer found the wording safe at the current scope.  These are
source-side Pi-valued coordinate families only.

Naming caution: keep "regular block coordinate map" distinct from "regular
coordinate chart."  The residual map is not part of the regular-coordinate
index; only the product-difference map combines regular block coordinates with
`D`.

## Lean Notes

The proof pattern is appropriate:

```text
funext c
simpa [mapDef, scalarPredicateDef] using (sourceData.scalarField c).1

refine continuousAt_pi.2 ?_
intro c
simpa [mapDef, scalarPredicateDef] using (sourceData.scalarField c).2
```

No `Fintype` assumption is needed for `continuousAt_pi`.  The current `simpa`
works because the map definitions duplicate the same `let E`/`let S` shape as
the scalar predicates.  If these maps are later refactored through helper
definitions, add unfold/simp lemmas or the current proof may stop closing.

## Nonclaims Confirmed

No analytic chart, local inverse, source-rank openness, analytic ideal
transport, chart coverage, Jacobian compatibility, normal crossings, pole
order, or RLCT extraction is asserted.
