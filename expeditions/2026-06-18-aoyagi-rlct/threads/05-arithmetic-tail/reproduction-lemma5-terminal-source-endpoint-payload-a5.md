# Reproduction - Lemma 5 terminal source endpoint payload

Date: 2026-06-21.

Scope: terminal endpoint assembly for a supplied Lemma 5 branch whose terminal
chain value is explicitly realised by the source coordinate.

This does not construct the terminal branch or prove the source-realisation
equality.

## Source Inventory

Aoyagi Lemma 5 uses terminal data at the last selected coordinate.  In the
formalised notation this coordinate is

```text
S = C.point ell - 1.
```

The existing terminal Eq5 checkpoint records that, at `p=ell`, the strict Eq5
offset set is empty and the same-coordinate interval is the singleton `{0}`
under the selected-width sum.  Therefore a supplied terminal source value

```text
T(C.point ell - 1) = 0
```

fills the terminal same-coordinate interval.

The existing terminal source-label checkpoint records that, under explicit
source-range and width-positivity hypotheses,

```text
(C.point ell - 1, 1)
```

is a legal introduced label, and if the terminal source value is zero then

```text
T(C.point ell - 1) = 1 - 1.
```

The existing supplied-family terminal bridge records terminal chain zero for
each supplied full branch `x`:

```text
F.fullH x (Fin.last ell) = 0.
```

It still needs the explicit source-realisation equality

```text
T(C.point ell - 1) = F.fullH x (Fin.last ell).
```

## Pen-And-Paper Derivation

Fix a supplied full-family branch `x`.

Assume:

```text
x in F.fullBranches,
T(C.point ell - 1) = F.fullH x (Fin.last ell).
```

In the admissible-family case, also assume `a<=ell` and the selected-width
sum

```text
sum_i m_i = ell*(M-1)+a.
```

The supplied-family terminal theorem gives

```text
F.fullH x (Fin.last ell) = 0.
```

Substitution gives

```text
T(C.point ell - 1) = 0.
```

The existing terminal Eq5 theorem then gives

```text
insert (T(C.point ell - 1)) Eq5Offsets(ell)
  = HtildeInterval(ell).
```

The existing terminal source-label theorem, with hypotheses

```text
1<=ell,
C.point ell <= L+1,
1<=n(C.point ell),
```

also gives

```text
T(C.point ell - 1) in HtildeInterval(ell),
T(C.point ell - 1) = 1-1,
(C.point ell - 1,1) in introducedLabelFinset L n (C.point ell - 1) 1.
```

The binary-family case is identical after replacing the admissible terminal
chain-zero theorem by the binary one.  The binary terminal chain-zero field
does not need the selected-width sum, but the terminal Eq5 singleton and
terminal source-label interval membership still use it.

## Lean Targets

```text
aoyagiLemma5TerminalSourceEndpointPayload
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_terminalEndpointPayload
AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_terminalEndpointPayload
```

## Kill Conditions

- Do not remove the explicit source-realisation hypothesis.
- Do not claim that a terminal source branch has been constructed.
- Do not claim source-backed terminal exactness, classifier coverage,
  branch-label injectivity, or back-to-label coverage.
- Do not claim pole order, normal crossings, or RLCT extraction.
