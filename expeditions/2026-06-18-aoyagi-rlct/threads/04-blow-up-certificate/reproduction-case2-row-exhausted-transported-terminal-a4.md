# A4 Case 2 Row-Exhausted Transported Terminal

Status: reproduced the row-exhausted terminal-prefix branch and the
transported-row terminal matrix.  This is not an original-row bridge.

## Source Anchor

On Aoyagi PDF pp. 21-22, the stopped displayed Case 2 branch occurs when the
next continuation bound fails.  The cleared block is then displayed as
`(1,0,...)` or its transpose, and the product is moved to the advanced
terminal source order.

## Pen-And-Paper Reproduction

The current displayed residual row range is

```text
J+1 <= i <= M(S).
```

If the current prefix is exhausted,

```text
M(S) = J+1,
```

then the next prefix minimum satisfies

```text
M(S+1) <= M(S) = J+1.
```

So the next continuation inequality `J+2 <= M(S+1)` is impossible.  This is
the row-exhausted stopped branch.

The terminal prefix row range is still `1..M(S+1)`.  Under the displayed
continuation hypothesis `J+1 <= M(S+1)`, row exhaustion gives

```text
M(S+1) = J+1.
```

Thus the terminal prefix rows are `1..J+1`.  The old rows are

```text
Cterm(i,-) = C(i,-),          i=1,...,J.
```

The last row is not generally the original source row.  It is the transported
top row

```text
Cterm(J+1,-) = (Q^-1 C)_top.
```

Entrywise,

```text
(Q^-1 C)_J+1,a =
  C_J+1,a + sum_{r=J+2}^{M^(S+1)} d'_(J+1,r) C_r,a.
```

If `M^(S+1)>J+1`, this correction sum is a genuine part of Aoyagi's
transported following factor.  Therefore current-prefix row exhaustion cannot
be used as an original-row bridge or as the `(S+1,0)` recurrence relabel.

## Lean Shape

The finite arithmetic checkpoint is:

```text
case2_not_next_cont_of_prefixMin_current_eq
```

The explicit transported-row terminal matrix and bridge are:

```text
case2DisplayedSourceTerminalTransportedRows
case2DisplayedSourceTerminalCprimeCandidate_eq_transportedRows
SuppliedTerminalCprimeBridge.of_transportedRows
```

The row-exhausted source old-top/source suffix wrappers are:

```text
exists_sourceOldTopSuffix_entryIdeal_eq_prefixProduct_of_rowExhausted
exists_sourceOldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
```

## Boundaries

- This is the current-prefix row-exhausted branch.
- It does not assert actual next-width exhaustion `M^(S+1)=J+1`.
- It does not identify the transported pivot row with the original row
  `C(J+1,-)`.
- It does not relabel recurrence or exponent data to `(S+1,0)`.
- It does not prove chart production, chart coverage, Jacobian arithmetic,
  normal crossings, RLCT extraction, termination, transition invariance,
  automatic Case 2 gap/tail transport, or printed-vector repair.

## Kill Conditions

- Do not weaken actual-width exhaustion in
  `SuppliedTerminalCprimeBridge.of_originalRows_width_next_eq` to
  current-prefix row exhaustion.
- Do not drop the `Q^-1 C` correction sum in row-exhausted wide-next cases.
