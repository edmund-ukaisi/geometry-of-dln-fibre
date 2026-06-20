# A4 Case 2 Source Old-Top/Suffix Specialization

Status: reproduced the source-shaped old-top specialization of the stopped
displayed Case 2 terminal product.  This removes arbitrary old-top multiplier
and old-top block parameters from one terminal theorem, but the suffix remains
supplied.

## Source Anchor

On PDF pp. 20-22 Aoyagi works only on the active lower block

```text
C_J^(S+1),
```

whose rows start at `J+1`.  The rows `1,...,J` remain the old top rows in the
terminal display.  The terminal product is written with

```text
diag(b_1,...,b_J,b'_(J+1),...) C'^(S+1) prod_{s=S+2}^L C^(s).
```

## Pen-And-Paper Reproduction

Let the old top row index set be

```text
I_top = {1,...,J}.
```

The old top diagonal multiplier is therefore

```text
diag(pre.weight i)_{i in I_top}.
```

For a supplied source-coordinate following matrix `C`, the old top block is
the row restriction

```text
Ctop(i,t) = C(i,t),    i in I_top.
```

The active residual following block remains the existing source restriction

```text
C_J^(S+1)(j,t) = C(j,t),    J+1 <= j <= n(S+1).
```

The previously proved stopped terminal theorem accepted arbitrary supplied
old-top data `Atop` and `Ctop`.  Specialising it to

```text
Atop = diag(pre.weight i)_{i=1..J},
Ctop(i,t) = C(i,t)
```

gives the same entry-ideal equality, with the same supplied suffix

```text
F = prod_{s=S+2}^L C^(s)
```

left abstract as a matrix parameter.

## Lean Shape

New source-shaped constructors:

```text
case2SourceOldTopRowIndex
case2DisplayedSourceOldTopWeight
case2DisplayedSourceOldTopBlock
```

Specialized theorem:

```text
Case2DisplayedSuppliedChartFamilyBoundary.
  exists_sourceDisplayedOldTopSuffixTerminalProduct_entryIdeal_eq_of_not_next_cont
```

## Boundaries

- The suffix `F` remains supplied.
- The theorem does not construct the matrix chain
  `prod_{s=S+2}^L C^(s)`.
- The theorem does not prove `[Ctop; C0]` is Aoyagi's full source-produced
  `C'^(S+1)`.
- The theorem does not construct chart-produced recurrence or exponent data.
- No chart coverage, coordinate regularity, Jacobian arithmetic, normal
  crossings, RLCT extraction, termination, transition invariant, automatic
  Case 2 gap/tail transport, or printed-vector repair is proved.

## Kill Conditions

- Do not treat the supplied suffix `F` as a quiver-produced or chart-produced
  product.
- Do not infer source-produced `C'^(S+1)` from the old-top row restriction
  alone.
