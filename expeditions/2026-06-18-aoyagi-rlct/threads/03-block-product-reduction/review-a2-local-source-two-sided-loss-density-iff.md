# Review - A2 local-source two-sided loss-density iff

Date: 2026-06-29.

Reviewers: xhigh read-only scouts `Jason the 2nd` and `Mendel the 2nd`;
xhigh read-only final reviewer `Ohm the 2nd`.

## Verdict

PASS as a supplied-bound local integrability equivalence.

Jason recommended proceeding with the theorem provided the residual
measurability, positivity, `<= R^2`, constant positivity, Haar/SFinite, and
four source-filter comparison hypotheses remain explicit.  He also confirmed
that no separate loss positivity or density nonnegativity hypotheses are
needed: the imported two-sided comparison iff obtains these from the lower
loss and lower density bounds together with the positive constants.

Mendel confirmed the Lean proof skeleton: choose `U` from the local-source
two-sided a.e. handoff, transport residual hypotheses to `U inter source`, and
apply the p.13 two-sided comparison iff with
`mu := mu.restrict (U inter source)`.

Ohm checked the final diff and found the Lean theorem scoped correctly: it gets
`U` from the local-source handoff, restricts residual hypotheses to `U inter
source`, and then calls the p.13 two-sided iff.  The final review confirmed
that the statement keeps all required hypotheses explicit and that the docs do
not overclaim comparison/residual proofs, chart construction, transport,
original-loss identification, normal crossings, pole order, or RLCT.

## Checks

The theorem exposes the residual side as

```text
residualNegPowerIntegrableOn Cedge (U inter source) mu t
```

and does not claim chart construction, source coverage, comparison proof,
transport, normal crossings, pole order, or RLCT.

## Verification

The controller ran:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

It passed.
