# Review - A2 retained-passive selected-entry chart-produced determinant residual

Reviewer: Arendt, xhigh read-only subagent.

Verdict: PASS.

The reviewer found the generic chart-produced support wrapper mathematically
sound.  The proof shape matches the existing Lean surface:

1. lift `AEMeasurable chart signedBox` to the weighted signed-box measure using
   absolute continuity of `withDensity`;
2. combine `MeasurableSet S` and pointwise support `chart y ∈ S` through
   `ae_map_iff`;
3. prove

   ```text
   (Measure.map chart weightedBox).restrict S = Measure.map chart weightedBox;
   ```

4. call the existing supplied-map theorem with
   `m := Measure.map chart weightedBox`.

The reviewer noted that `MeasurableSet S` is sufficient for the generic theorem;
`BorelSpace` is needed only by consumers that derive `S` measurability from
openness or derive chart a.e. measurability from continuity.  Pointwise support
is stronger than necessary but appropriate for this API.

The notes correctly avoid overclaiming: this is chart-produced only, not an
arbitrary-measure theorem, Haar/source-prior transport, full determinant-chart
coverage, source-rank coverage, normal crossings, pole order, or RLCT.
