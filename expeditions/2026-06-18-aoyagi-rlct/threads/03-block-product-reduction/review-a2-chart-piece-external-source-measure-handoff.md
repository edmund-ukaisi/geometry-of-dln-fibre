# Review - A2 chart-piece external-source measure handoff

Date: 2026-06-30.

Reviewer: xhigh `Nietzsche the 2nd`.

Status: PASS.

## Scope

Reviewed the new measurable-piece handoff in:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
```

and the accompanying reproduction and statement-card files.

## Findings

No blocking formalization or mathematical issue found.

The helper `restrict_withDensity_le_smul_restrict_of_ae_le_of_subset` uses the
correct a.e. measure, `mu.restrict s`, and only enlarges the reference measure
by the explicit subset hypothesis `s subset t`.

The chart-piece theorem explicitly requires:

```text
MeasurableSet chartPiece
chartPiece subset sourceLocal
externalSourceMeasure.restrict chartPiece =
  (sourceImageMeasure.withDensity externalDensity).restrict chartPiece
externalDensity <= Cext
  a.e. with respect to sourceImageMeasure.restrict chartPiece
```

The derived domination has the right shape:

```text
externalSourceMeasure.restrict chartPiece
  <= Cext • sourceImageMeasure.restrict sourceLocal
```

and the proof productizes it using the existing `[SFinite nu]` requirement
before feeding the full-product domination socket.

The documentation states the correct nonclaims: no chart-image measurability,
no source-image equality, no original/source-prior transport, no source-rank
coverage, no Haar transport, no normal crossings, no pole-order claim, and no
RLCT extraction.

## Reviewer Verification

The reviewer independently ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
lake build DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge
git diff --check
```

No target-file `sorry`, `admit`, `axiom`, `#exit`, `native_decide`, or `unsafe`
hits were found.
