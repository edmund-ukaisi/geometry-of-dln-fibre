# Reproduction - A2 fixed-base suffix-state field continuity

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean implementation.

## Question

The generic chart-local suffix-state theorem now proves fieldwise continuity
for the deterministic product-reduction fields

```text
L, B, Ctop, D
```

for an abstract edge-matrix family `E(x)`.  The fixed-base endpoint chart
theory in `FixedBasepointChart.lean` uses a more source-facing family:

```text
E(x,p) =
  toMatrix (paperEndpointFixedBaseBasis ... p.castSucc)
           (paperEndpointFixedBaseBasis ... p.succ)
           (Cedge x p).
```

The handoff needed here is to show that the generic suffix-state field
continuity applies to this fixed-base matrix family.

## Source Anchor

Aoyagi PDF pp. 11-13 performs the product reduction in fixed endpoint-style
coordinates by recursively applying block elimination on determinant charts.
The matrices `L`, `B`, `Ctop`, and `D` are deterministic functions of the edge
matrices once the determinant charts are chosen.

This slice only transports the already-proved continuity of those deterministic
functions to the endpoint bases fixed from a base chain.  It does not prove
analytic regularity, exact-rank openness, source-rank openness, chart coverage,
regular suspension, normal crossings, pole order, or RLCT.

## Fixed-Base Matrix Family

Let `Cedge : alpha -> forall p, reverseVertex p.castSucc ->L reverseVertex
p.succ` be continuous at `x0`.  The endpoint bases are fixed from the base
paper chain `B`, so they do not vary with `x`.  For each edge `p`, the map

```text
f |-> LinearMap.toMatrix fixedSourceBasis fixedTargetBasis f
```

is continuous.  Hence the coordinate family

```text
E(x,p) = toMatrix fixedSourceBasis fixedTargetBasis (Cedge x p)
```

is continuous at `x0` in the product topology.  This is exactly the `hE`
hypothesis of
`continuousAt_chartLocalSuffixState_suffixState_fields`.

## Recursive Chart Hypotheses

The fixed-base theorem keeps the same recursive determinant-chart hypotheses
already used by the existing `Bprev` neighborhood theorem:

```text
identityCornerDetChart
  (ChartLocalSuffixState.transformedEdge (E x0) p
    (ChartLocalSuffixState.suffixState (E x0) (Fin.last N)
      p.succ p.succ.le_last)).
```

These hypotheses are source-facing only because `E` is unfolded into
fixed-base coordinates.  After defining `E`, they are definitionally the
generic recursive chart hypotheses required by the suffix-state theorem.

## Conclusion

Applying the generic suffix-state theorem at `j = Fin.last N` gives, for every
`i <= Fin.last N`,

```text
IsUnit ((suffixState (E x0) (Fin.last N) i hi).Ctop.det)
ContinuousAt (fun x => (suffixState (E x) (Fin.last N) i hi).L) x0
ContinuousAt (fun x => (suffixState (E x) (Fin.last N) i hi).B) x0
ContinuousAt (fun x => (suffixState (E x) (Fin.last N) i hi).Ctop) x0
ContinuousAt (fun x => (suffixState (E x) (Fin.last N) i hi).D) x0
```

The theorem is a fixed-base handoff, not a new product-reduction identity.
It should reuse the local `E`, `hE`, and `hchartE` construction already present
in the `recursiveBprev` theorem.

## Guardrails

This slice must not:

- assert exact-rank strata are open;
- state a neighborhood where the recursive chart hypotheses hold unless using
  the separately proved determinant-chart neighborhood theorem;
- claim continuity is analytic regularity;
- claim canonical continuous triangular witnesses beyond the deterministic
  suffix-state fields;
- infer regular suspension, ideal transport, normal crossings, pole order, or
  RLCT.
