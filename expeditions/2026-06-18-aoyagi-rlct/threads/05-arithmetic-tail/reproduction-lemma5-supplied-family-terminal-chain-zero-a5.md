# Reproduction - Lemma 5 Supplied Family Terminal Chain Zero

Status: supplied-data chain endpoint wrapper; ready for a narrow Lean theorem.

This note records the terminal-chain consequence used at the current Lemma 5
frontier.  It is deliberately weaker than a terminal source-vector statement.

## Source Boundary

Aoyagi's Lemma 4/Lemma 5 discussion has two displayed extremal chains
`Htilde` and `Htilde'`.  Under the selected-width sum, their terminal values
are

```text
Htilde_ell = Htilde'_ell = 0.
```

This is chain endpoint data.  It does not by itself construct a source branch
whose source coordinate satisfies

```text
T(C.point ell - 1) = 0.
```

The previous terminal Eq5 gap slice showed why this distinction matters:
Eq5 has no strict offset values at `p=ell`, so terminal same-coordinate
coverage needs a separately supplied terminal source-coordinate value.

## Admissible Branch Calculation

Let `H` be a supplied branch chain satisfying the already-proved chain bounds

```text
Htilde <= H <= Htilde'.
```

At the terminal coordinate `ell`, both endpoints of the interval are zero.
Therefore

```text
0 <= H_ell <= 0,
```

and hence `H_ell = 0`.

The supplied admissible nonbase family has these bounds branchwise:

```text
Htilde <= H(b) <= Htilde'
```

for each supplied nonbase branch `b` at an interior coordinate.  Applying the
terminal squeeze gives

```text
H(b)_ell = 0.
```

The supplied admissible full family adds a supplied base chain `baseH` with the
same bounds.  Hence

```text
baseH_ell = 0.
```

For a tagged full branch,

```text
fullH(none) = baseH,
fullH(some b) = H(b).
```

The previous membership lemma for `fullBranches` reduces the `some b` case to
a nonbase branch at some interior coordinate.  Thus every tagged branch in the
supplied admissible full family has terminal chain value zero.

## Binary Branch Calculation

The supplied binary nonbase family carries terminal chain zero directly as its
field

```text
Hlast : H(b)_ell = 0.
```

The supplied binary full family carries the base analogue

```text
baseHlast : baseH_ell = 0.
```

Therefore every tagged branch in a supplied binary full family has terminal
chain value zero by case analysis on `none` versus `some b`.

## Lean Targets

```text
AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_terminalH_zero
AoyagiLemma5SuppliedAdmissibleFamily.base_terminalH_zero
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalH_zero
AoyagiLemma5SuppliedBinaryNonbaseFamily.branch_terminalH_zero
AoyagiLemma5SuppliedBinaryFamily.base_terminalH_zero
AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalH_zero
```

## Kill Conditions

- Do not rewrite this as a theorem about `T(C.point ell - 1)`.
- Do not claim this constructs the terminal/base source branch.
- Do not claim source-label legality, terminal-label exactness, classifier
  coverage, injection, or back-to-label coverage.
- Do not use this as a pole-order, normal-crossing, or RLCT theorem.

## Nonclaims

- No displayed source vector is constructed.
- No Eq5 terminal coverage is proved from branch-chain data alone.
- No terminal minimizer exactness theorem is proved.
- No source-backed Lemma 5 chart family is constructed.
