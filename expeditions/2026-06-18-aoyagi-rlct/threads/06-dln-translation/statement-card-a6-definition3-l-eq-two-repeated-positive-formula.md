# Statement card - A6 Definition 3 `L=2` repeated-positive formula package

Date: 2026-06-24.

## Lean declarations

File:
`lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`

New preferred theorems:

```text
AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth
AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_rankWidth
```

Compatibility theorem retained:

```text
AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_remainder_rankWidth
```

Follow-up no-`hr` wrapper:

```text
AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated
```

See
`statement-card-a6-definition3-l-eq-two-branch-formula-rankwidth-removal.md`.

## Statement

For `L=2`, suppose the source-range reduced widths are natural values
`w1,w2,w3`, all positive, and suppose one repeated-equality branch is supplied:

```text
w1 = w2, or
w1 = w3, or
w2 = w3.
```

Under the usual source-range rank-width hypothesis, Lean constructs:

- selected cutpoints `C : AoyagiSelectedCutpoints 1`;
- selected values `u,v`;
- selected reduced widths `m`;
- ceiling data `data : AoyagiDefinition3CeilData 1 m`;
- `AoyagiDefinition3SourceData 2 1 H r C`;
- `ceilWidth = u+v`, `aParam = 1`, and order formula `1`;
- selected-width Nat/nonnegativity/strictness provenance;
- `aoyagiSelectedWidthPairSum 1 m = u*v`;
- the finite lambda formula

```text
aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data
  = aoyagiTheorem2RegularTerm 2 H r + u*v/2.
```

## Source reproduction

`threads/06-dln-translation/reproduction-definition3-ell-one-automatic-ceil-formula-a6.md`

`threads/06-dln-translation/reproduction-definition3-l-eq-two-repeated-positive-formula-a6.md`

The branch choices are:

```text
w1=w2 -> select (1,3), so (u,v)=(w1,w3)
w1=w3 -> select (1,2), so (u,v)=(w1,w2)
w2=w3 -> select (1,2), so (u,v)=(w1,w2)
```

Each branch covers all three source-range width values by the selected value
set, then delegates to the automatic `ell=1` selected-pair formula package.
The compatibility theorem with branch-compatible `ceilPred` equations is kept
for callers that already use that form, but it is no longer the preferred API.

The later no-`hr` wrapper derives the usual source-range rank-width hypothesis
from the Nat-valued reduced-width identities before delegating to the
`_rankWidth` theorem recorded here.

## Verification

Focused elaboration passed:

```text
cd lean
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

Focused module build passed:

```text
cd lean
LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
```

## Nonclaims

This theorem does not claim a unique canonical selected pair, derive
general quotient/remainder data, add source-rank wrappers or final sockets,
construct Eq5 payloads or charts, prove normal crossings, identify pole order,
or extract RLCT.
