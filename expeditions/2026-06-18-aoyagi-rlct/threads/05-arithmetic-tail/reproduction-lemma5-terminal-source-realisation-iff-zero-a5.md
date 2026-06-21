# Reproduction - Lemma 5 terminal source realisation iff zero

Date: 2026-06-21.

Scope: terminal source-realisation bookkeeping for supplied branch families.
Once a supplied branch has terminal chain value zero, the source-realisation
equality at the terminal coordinate is equivalent to supplying terminal source
zero directly.

This does not construct a terminal source branch or prove terminal source zero.

## Source Inventory

The terminal source bridge currently uses the explicit hypothesis

```text
T(C.point ell - 1) = F.fullH x (Fin.last ell).
```

The supplied-family terminal chain-zero theorem proves

```text
F.fullH x (Fin.last ell) = 0.
```

For admissible supplied families this uses `a<=ell` and the selected-width
sum.  For binary supplied families it follows from the supplied `Hlast` and
`baseHlast` fields.

## Pen-And-Paper Derivation

Fix a supplied full-family branch `x`.

In the admissible case, assume

```text
a <= ell,
sum_i m_i = ell*(M-1)+a,
x in F.fullBranches.
```

Then

```text
F.fullH x (Fin.last ell) = 0.
```

Substituting this into the terminal source-realisation equality gives

```text
T(C.point ell - 1) = F.fullH x (Fin.last ell)
  iff
T(C.point ell - 1) = 0.
```

The binary case is identical, except the terminal chain-zero theorem has no
selected-width-sum hypothesis.

## Lean Targets

```text
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_realisation_iff_terminalZero
AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_realisation_iff_terminalZero
```

## Kill Conditions

- Do not claim `T(C.point ell-1)=0` is proved.
- Do not claim the source-realisation equality is proved from supplied family
  data alone.
- Do not construct terminal source branches, terminal-label exactness,
  classifier coverage, pole order, normal crossings, or RLCT extraction.
