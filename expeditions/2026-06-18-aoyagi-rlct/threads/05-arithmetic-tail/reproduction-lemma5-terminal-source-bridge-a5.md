# Reproduction - Lemma 5 Terminal Source Bridge

Status: supplied source-realisation bridge; ready for a narrow Lean theorem.

This note packages the exact extra hypothesis needed to turn terminal
chain-zero data for a supplied branch into the terminal Eq5 finite-set
coverage theorem.

## Boundary

The terminal chain-zero slice proves that supplied branch chains have

```text
H_ell = 0.
```

The terminal Eq5 gap slice proves that at `p=ell`,

```text
Eq5Offsets_ell = empty,
Interval_ell = {0},
```

under the selected-width sum.  It also proves that inserting a separately
supplied source-coordinate zero fills the terminal singleton:

```text
T(C.point ell - 1) = 0
  implies
insert T(C.point ell - 1) Eq5Offsets_ell = Interval_ell.
```

These two facts do not compose without an extra source-realisation statement:

```text
T(C.point ell - 1) = H_ell.
```

That equality is not automatic.  The left side is a source-vector coordinate;
the right side is a selected-chain coordinate.

## Admissible Full Family

Let `F` be a supplied admissible full family and let `x in F.fullBranches`.
Assume:

```text
a <= ell,
sum_i m_i = ell*(M-1)+a,
T(C.point ell - 1) = F.fullH(x)(Fin.last ell).
```

The supplied-family terminal chain theorem gives

```text
F.fullH(x)(Fin.last ell) = 0.
```

Therefore

```text
T(C.point ell - 1) = 0.
```

The terminal Eq5 supplied-zero wrapper then gives

```text
insert T(C.point ell - 1) Eq5Offsets_ell = Interval_ell.
```

## Binary Full Family

The same argument works for a supplied binary full family.  In that case the
terminal chain value comes directly from the supplied `Hlast`/`baseHlast`
fields through the binary full-branch terminal theorem.  The selected-width sum
and `a<=ell` are still needed by the terminal Eq5 interval singleton theorem.

## Lean Targets

```text
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_Eq5Coverage
AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_Eq5Coverage
```

## Kill Conditions

- Do not remove the source-realisation hypothesis
  `T(C.point ell - 1)=fullH x (Fin.last ell)`.
- Do not claim the supplied family constructs a terminal source branch.
- Do not claim source-label legality, terminal-label exactness, classifier
  coverage, injection, back-to-label coverage, pole order, normal crossings,
  or RLCT extraction.

## Nonclaims

- No source vector is constructed.
- No printed Aoyagi equation is proved to supply the terminal branch.
- No exact terminal-minimizer count is proved.
