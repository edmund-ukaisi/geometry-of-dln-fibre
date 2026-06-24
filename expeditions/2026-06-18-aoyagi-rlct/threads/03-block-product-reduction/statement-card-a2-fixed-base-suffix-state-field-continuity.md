# Statement card - A2 fixed-base suffix-state field continuity

Status: Lean implementation landed and reviewed.

Reproduction:
`reproduction-a2-fixed-base-suffix-state-field-continuity.md`.

Review:
`review-a2-fixed-base-suffix-state-field-continuity.md`.

## Target

Add a fixed-base endpoint-coordinate handoff from the continuous edge family
`Cedge` to the generic suffix-state field continuity theorem.

## Expected Lean Artifact

Expected declaration in `lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`:

```text
paperEndpointFixedBaseContinuousEdges_recursiveSuffixState_fields_continuousAt
```

The theorem should assume:

```text
Cedge : alpha -> forall p,
  reverseVertex W p.castSucc ->L[K] reverseVertex W p.succ
ContinuousAt Cedge x0
recursive transformed determinant-chart hypotheses at x0
```

and return the bundled suffix-state conclusion for the fixed-base coordinate
family:

```text
let E := fun x p =>
  LinearMap.toMatrix
    (paperEndpointFixedBaseBasis W B U0 hU0 p.castSucc)
    (paperEndpointFixedBaseBasis W B U0 hU0 p.succ)
    (Cedge x p : reverseVertex W p.castSucc ->_l[K] reverseVertex W p.succ)
forall i (hi : i <= Fin.last N),
  IsUnit ((ChartLocalSuffixState.suffixState (E x0) (Fin.last N) i hi).Ctop.det) /\
  ContinuousAt (fun x => (ChartLocalSuffixState.suffixState (E x) (Fin.last N) i hi).L) x0 /\
  ContinuousAt (fun x => (ChartLocalSuffixState.suffixState (E x) (Fin.last N) i hi).B) x0 /\
  ContinuousAt (fun x => (ChartLocalSuffixState.suffixState (E x) (Fin.last N) i hi).Ctop) x0 /\
  ContinuousAt (fun x => (ChartLocalSuffixState.suffixState (E x) (Fin.last N) i hi).D) x0
```

Use actual Lean arrows/symbols in the implementation; this card uses ASCII in
the code block for portability.

## Expected Proof

Define the fixed-base matrix family `E`.  Prove `ContinuousAt E x0` by
`continuousAt_pi`, continuity of `Cedge`, and `continuous_linearMap_toMatrix`.
Rewrite the source-facing recursive determinant-chart hypotheses to the
generic `hchartE`.  Then apply
`continuousAt_chartLocalSuffixState_suffixState_fields`.

## Kill Conditions

- Do not weaken away the recursive determinant-chart hypotheses.
- Do not assert exact-rank or source-rank strata are open.
- Do not assert analytic regularity.
- Do not create a boundary certificate with existential triangular witnesses.
- Do not infer normal crossings, pole order, or RLCT.

## Verification

Controller verification passed:

```text
cd lean && LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean
cd lean && LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.FixedBasepointChart
```

The preferred `scripts/lb` route was attempted first, but the environment
rejected unsandboxed writes to the shared `~/.lake-shared` lock pool.  The
fallback checks used one Lean worker and the already-linked shared packages.
