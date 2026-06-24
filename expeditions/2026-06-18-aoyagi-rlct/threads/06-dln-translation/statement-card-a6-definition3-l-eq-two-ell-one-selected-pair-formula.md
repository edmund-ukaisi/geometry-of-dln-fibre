# Statement card - A6 Definition 3 `L=2`, `ell=1` selected-pair formula package

Status: Lean implementation landed and reviewed.

Reproduction:
`reproduction-definition3-l-eq-two-ell-one-selected-pair-formula-a6.md`.

Review:
`review-definition3-l-eq-two-ell-one-selected-pair-formula-a6.md`.

## Target

Add an explicit finite formula package for an exposed `ell=1` selected pair in
the `L=2` repeated-positive branch.

## Expected Lean Artifact

Expected declaration in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_remainder_rankWidth
```

The theorem should assume:

```text
C : AoyagiSelectedCutpoints 1
C.cut j <= 3
aoyagiReducedWidthInt H r (C.cut 0) = u
aoyagiReducedWidthInt H r (C.cut 1) = v
0 < u, 0 < v
all source-range reduced widths lie in the selected value set of C
u + v = ceilPred + 1
rank-width: forall s, 1 <= s -> s <= 3 -> r <= H s
```

and return source data, selected widths, an explicit ceiling datum, and formula
projections:

```text
data.ceilWidth = ceilPred + 1
data.aParam = 1
data.theorem2OrderFormula = 1
aoyagiSelectedWidthPairSum 1 m = u*v
aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data =
  aoyagiTheorem2RegularTerm 2 H r + u*v/2
```

Include Nat-width, nonnegativity, strictness, selected-width upper-bound, and
`m 0 = u`, `m 1 = v` provenance.

## Kill Conditions

- Do not hide the selected pair behind a bare repeated-width disjunction.
- Do not claim this is a canonical repeated-positive branch formula.
- Do not add source-rank or final-socket wrappers without a concrete consumer.
- Do not claim Eq5 construction, charts, normal crossings, pole order, or
  RLCT.

## Verification

Controller verification passed:

```text
cd lean && LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
cd lean && LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
```

As before, the preferred `scripts/lb` route is unavailable in this sandbox
because the environment rejects unsandboxed writes to the shared
`~/.lake-shared` lock pool.  The fallback checks used one Lean worker and the
already-linked shared packages.
