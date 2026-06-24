# Statement card - A6 Definition 3 `L=2` triangle formula package

Status: Lean implementation landed and reviewed.

Reproduction:
`reproduction-definition3-l-eq-two-triangle-formula-a6.md`.

Review:
`review-definition3-l-eq-two-triangle-formula-a6.md`.

## Target

Add an explicit finite formula package for the all-source triangle branch of
Definition 3 at `L=2`.

## Expected Lean Artifact

Expected declaration in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_remainder_rankWidth
```

The theorem should assume:

```text
aoyagiReducedWidthInt H r 1 = w1
aoyagiReducedWidthInt H r 2 = w2
aoyagiReducedWidthInt H r 3 = w3
2*w_i < w1+w2+w3              for i=1,2,3
w1+w2+w3 = 2*ceilPred + a
0 < a <= 2
rank-width: forall s, 1 <= s -> s <= 3 -> r <= H s
```

and return consecutive all-source cutpoints, source data, selected reduced
widths `m`, an explicit positive-remainder ceiling datum, and formula
projections:

```text
data.ceilWidth = ceilPred + 1
data.aParam = a
data.theorem2OrderFormula = a*(2-a)+1
aoyagiSelectedWidthPairSum 2 m = w1*w2 + w1*w3 + w2*w3
aoyagiTheorem2Lambda_fromCeilData 2 2 H r m data =
  aoyagiTheorem2RegularTerm 2 H r
  + a*(2-a)/8
  - (ceilPred + a/2)^2/2
  + (w1*w2 + w1*w3 + w2*w3)/2
```

Use actual Lean casts in the implementation.

## Expected Proof

Use the all-source triangle strict inequalities to construct consecutive
source data.  Let `m = aoyagiSelectedReducedWidths H r C`.  Use the
rank-width hypothesis to keep the existing Nat-width/nonnegativity provenance.
Construct `data` explicitly with
`AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder`.

Then prove the three formula projections by expanding the `Fin 3` sums and
unfolding `aoyagiTheorem2Lambda_fromCeilData`.

## Kill Conditions

- Do not generalize to the repeated-positive `ell=1` branch.
- Do not claim arbitrary source-data existence.
- Do not add source-rank or final-socket wrappers without a concrete consumer.
- Do not claim Eq5 construction, charts, normal crossings, pole order, or
  RLCT.

## Verification

Controller verification passed:

```text
cd lean && LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
cd lean && LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
```

The preferred `scripts/lb` path remains unavailable in this sandbox because
the environment rejects unsandboxed writes to the shared `~/.lake-shared`
lock pool.  The fallback checks used one Lean worker and the already-linked
shared packages.
