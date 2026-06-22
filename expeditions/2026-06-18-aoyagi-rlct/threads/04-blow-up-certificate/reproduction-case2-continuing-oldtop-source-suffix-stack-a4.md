# Pen-and-paper reproduction - A4 Case 2 continuing old-top/source-suffix stack

Status: reproduced and formalised; xhigh review pending.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  After the displayed `Q` and `P` operations,
the paper obtains

```text
P diag(b_{J+1},...,b_{M(S)}) D_J C_J^(S+1)
  = u_{S,J+1} diag(b'_{J+1},...,b'_{M(S)}) D'''_J C'_J^(S+1).
```

When the next same-stage residual block is nonempty,

```text
J+2 <= prefixMinNat n (S+1),
```

this is the local source for the `J`-increment continuing branch.  This
checkpoint records the full pivot-first stack with the old top rows and the
raw source suffix; it does not construct a source-ordered successor following
object.

## Reproduction

The existing paper `Q/P` identity gives a tail equality

```text
Ltail * Csrc =
  (weightedPivotDiagonal(post.weight(J+1), post lower weights) * D''') * C',
```

where:

- `Ltail` is the displayed source-chart `P`-operated substituted residual
  block;
- `Csrc` is the current pivot-first source following factor;
- `C' = Q^-1 C` is Aoyagi's transported following factor in pivot-first order.

The old source rows `1,...,J` are unchanged in this local calculation.  Hence
the elementary block identity

```text
fromBlocks Wold 0 0 Ltail * verticalBlock Cold Csrc
  =
fromBlocks Wold 0 0 (weightedPivotDiagonal * D''') * verticalBlock Cold C'
```

follows from the tail equality by block multiplication.  Taking

```text
Wold = diag(pre.weight 1,...,pre.weight J),
Cold = source rows 1,...,J of C,
```

and multiplying both sides on the right by Aoyagi's raw suffix

```text
sourceSuffixProduct = product_{s=S+2}^L C^(s)
```

gives the formalised stack boundary.

The theorem also packages the already-established continuing-branch finite
payload:

- the next residual center is nonempty under `J+2 <= prefixMinNat n (S+1)`;
- corrected exponent certificates and level invariants for `(S,J+1)`;
- the successor least-value gap and Case 2 recurrence gap;
- finite current-center principalization by the selected chart variable `u`.

## Lean Name

```text
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData
```

## Boundary Checks

- The right side keeps paper `C' = Q^-1 C` in pivot-first order.
- The theorem is stronger than the lower-row `F := sourceSuffixProduct`
  wrapper because it includes old top rows and the transported pivot row.
- It stays below source-ordered successor production: no row equivalence to a
  full `C'^(S+1)` object is asserted.
- The suffix is carried explicitly as `sourceSuffixProduct`; it is not
  produced by the local chart.

## Kill Conditions

- Do not rename this as production of `Csucc`, full `C'^(S+1)`, or a transition
  invariant.
- Do not infer source production of the suffix, chart coverage, Jacobian
  arithmetic, normal crossings, pole order, termination, RLCT extraction, or
  repair of the printed Case 2 vector mismatch.
- Do not replace terminal branch distinctions with the continuing hypothesis;
  this theorem uses `hnext`, not `hstop`, `hrow`, or `hwidth`.
