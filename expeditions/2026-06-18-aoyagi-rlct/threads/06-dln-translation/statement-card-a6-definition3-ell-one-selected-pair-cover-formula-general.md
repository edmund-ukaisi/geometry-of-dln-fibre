# Statement card - A6 Definition 3 general `L`, `ell=1` selected-pair formula package

Status: Lean implementation landed and reviewed.

Reproduction:
`reproduction-definition3-ell-one-selected-pair-cover-formula-general-a6.md`.

Review:
`review-definition3-ell-one-selected-pair-cover-formula-general-a6.md`.

## Target

Generalize the exposed `ell=1` selected-pair formula package from `L = 2` to
arbitrary depth `L`, without adding any branch-selection convention.

## Lean Artifact

Declaration in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth_general
```

The theorem assumes:

```text
L : Nat
C : AoyagiSelectedCutpoints 1
C.cut j <= L + 1
aoyagiReducedWidthInt H r (C.cut 0) = u
aoyagiReducedWidthInt H r (C.cut 1) = v
0 < u, 0 < v
all source-range reduced widths lie in the selected value set of C
rank-width: forall s, 1 <= s -> s <= L + 1 -> r <= H s
```

and returns source data, selected widths, an explicit `ell=1` ceiling datum,
and formula projections:

```text
AoyagiDefinition3SourceData L 1 H r C
data.ceilWidth = u + v
data.aParam = 1
data.theorem2OrderFormula = 1
aoyagiSelectedWidthPairSum 1 m = u*v
aoyagiTheorem2Lambda_fromCeilData L 1 H r m data =
  aoyagiTheorem2RegularTerm L H r + u*v/2
```

It also returns Nat-width provenance, nonnegativity, strict selected
inequalities, selected-width upper bounds, natural-indexed nonnegativity, and
the endpoint identities `m 0 = u`, `m 1 = v`.

## Boundaries

- The selected pair is supplied, not chosen.
- The cover is value-level, matching Aoyagi Definition 3's selected value set.
- The theorem is finite formula bookkeeping only.
- The only `L`-dependence is the source range and regular term.

## Kill Conditions

- Do not claim a canonical repeated branch.
- Do not claim branch-independent finite lambda or order data for arbitrary
  Definition 3 source-data choices.
- Do not use the `L = 2` repeated-positive branch theorem as source evidence.
- Do not add source-rank or final-socket wrappers without a downstream
  consumer.
- Do not claim Eq5 construction, charts, normal crossings, pole order, or
  RLCT.

## Verification

Controller focused elaboration passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

Focused module build passed:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
```

Independent xhigh review passed with no findings.
