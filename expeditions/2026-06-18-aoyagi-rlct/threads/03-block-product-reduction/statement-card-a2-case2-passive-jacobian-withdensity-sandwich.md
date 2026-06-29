# Statement Card - A2 Case 2 Passive Jacobian WithDensity Sandwich

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Lean Names

```text
withDensity_ofReal_sandwich_of_ae_bounds
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
```

## Reproduction

```text
reproduction-a2-case2-passive-jacobian-withdensity-sandwich.md
```

## Claim

For the concrete passive product-domain measure, after restricting to a small
open neighborhood of a determinant-chart basepoint, weighting by the
retained-passive solved-`A1` product raw-order Jacobian factor gives a measure
bounded above and below by positive scalar multiples of the restricted passive
product-domain measure.

## Proved

There exist `epsilon > 0`, `K > 0`, and an open set `U` with `z0 in U` such
that

```text
ofReal epsilon • sourceMeasure.restrict U
  <= (sourceMeasure.restrict U).withDensity (fun z => ofReal (J z))

(sourceMeasure.restrict U).withDensity (fun z => ofReal (J z))
  <= ofReal K • sourceMeasure.restrict U.
```

The generic helper proves the same sandwich for any measure and any real
density satisfying the corresponding a.e. bounds.

## Assumed

The Case 2 theorem assumes the hypotheses of the prior passive a.e.
bounded-unit handoff: passive field continuity, basepoint determinant-unit
hypotheses for `Ctop z0.1` and `A1passive z0.1`, and the measurable/open-
measurable structure needed for the restricted measure.

## Cited

None.

## Deferred

Determinant-chart Haar transport, raw/source Haar transport, external or
original source-prior comparison, source-prior Jacobian accounting,
selected-entry image coverage, source-rank coverage, local inverse/coverage,
normal crossings, pole order, and RLCT extraction.

## Status

Proved in Lean.  Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.  `git diff
--check` passed.  `scripts/sorries` reports
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.  Direct axiom probes for the
generic helper and the Case 2 theorem report
`[propext, Classical.choice, Quot.sound]`.  Aristotle the 3rd xhigh read-only
review returned PASS in
`review-a2-case2-passive-jacobian-withdensity-and-residual-finite-mass.md`.
