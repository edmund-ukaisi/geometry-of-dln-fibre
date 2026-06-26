# Review - A2 p.13 left-step raw tuple measurability

Date: 2026-06-26.

Reviewer: xhigh read-only scout `Leibniz the 2nd`.

Verdict: no blocking findings.

## Scope Checked

The reviewer checked the uncommitted measurability slice in:

```text
lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean
lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean
```

The review focused on source/math boundary and Lean/API soundness for the new
p.13 raw tuple measurability statements.

## Findings

No blocking findings.

The new p.13 tuple statements derive only `Measurable` and `AEMeasurable`
from the fixed-base edge-matrix measurability hypothesis.  The raw-Haar/source
pushforward remains an explicit `hraw_map` hypothesis in

```text
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map_of_measurable_edgeMatrix.
```

The residual-product and residual-block lemmas are scoped to the real
measurability section and match the suffix recursion: `residualProduct` is
routed through the suffix-state `D` field, and `residualBlock` uses the
transformed edge at `suffixState ... p.succ hpj`.

## Verification Reported by Reviewer

From the `lean/` project root:

```text
lake env lean DLNFibre/DLN/Aoyagi/ChartTopology.lean
lake env lean DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean
git diff --check -- ...
```

passed.  The reviewer made no file edits.

## Nonclaims Reconfirmed

This review does not change the mathematical boundary: the raw pushforward is
not proved.  The checkpoint proves finite Borel measurability only.
