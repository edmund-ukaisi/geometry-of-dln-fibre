# Reproduction - Definition 3 nonconstant `(1,2,2)` example

Status: xhigh checked; formalisation-ready.

## Source Shape

This is a diagnostic example for the all-source selected constructor.  It
shows that the all-source lane is not only the equal-width example.

Take:

```text
L = 2,    r = 0,
M^(1) = 1,    M^(2) = 2,    M^(3) = 2.
```

In Lean this is encoded by

```text
H(s) = if s=1 then 1 else if s=2 then 2 else if s=3 then 2 else 0.
```

Since `r=0`, the reduced widths are exactly those values on the source range
`1,2,3`.

## Definition 3 Check

Select every source layer:

```text
ell = L = 2,
C.cut j = j.val + 1      for j : Fin 3.
```

The selected sum is:

```text
1 + 2 + 2 = 5.
```

The strict selected inequalities use the coefficient `ell=2`:

```text
2*1 < 5,
2*2 < 5,
2*2 < 5.
```

The nonselected clauses are vacuous because every source-range value is
selected.  Source-range rank-width is immediate from `r=0`.

Therefore the all-source strict/rank-width ceiling-data theorem produces
consecutive cutpoints, `AoyagiDefinition3SourceData 2 2 H 0 C`, selected
widths `m`, and a Definition 3 ceiling datum.  The selected widths satisfy

```text
m 0 = 1,    m 1 = 2,    m 2 = 2,
```

so the example is nonconstant.

## Lean Target

Add to `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_consecutive_nonconstant_widths_one_two_two_selectedReducedWidthCeilData
```

It should return the standard selected reduced-width ceiling package plus
the three concrete `m` values and `m 0 != m 1`.

## Nonclaims

- This is not arbitrary selected-cutpoint/source-data existence.
- This is not a classification of Definition 3 profiles.
- This is not a uniqueness theorem for cutpoints or ceiling data.
- This does not claim all nonconstant profiles work.
- This does not compute closed-form `ceilWidth` or `aParam`.
- This does not construct Eq5 payloads, finite exponent formula facts, charts,
  pole order, or RLCT.

## Check

xhigh reviewer `Mencius the 3rd` approved this as a useful diagnostic/example
theorem complementing the negative `(1,2,100)` guardrail.
