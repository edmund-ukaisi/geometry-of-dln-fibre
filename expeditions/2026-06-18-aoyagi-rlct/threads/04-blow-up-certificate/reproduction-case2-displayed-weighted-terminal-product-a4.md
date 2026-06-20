# A4 Case 2 Displayed Weighted Terminal Product

Status: reproduced the finite matrix/entry-ideal algebra that keeps supplied
diagonal row weights and a supplied remaining following product before
dropping zero rows.  This is not a construction of Aoyagi's next-stage
`C'^(S+1)`.

## Source Anchor

On Aoyagi PDF pp. 21-22, after the displayed Case 2 `Q/P` calculation, the
terminal paragraph rewrites a product containing diagonal monomial row factors,
the terminal cleared block, and the remaining following product

```text
F = product_{s=S+2}^L C^(s).
```

The previous checkpoints proved the raw pivot-first absorption and then
stacked a supplied old top block over it.  They deliberately did not include
the diagonal row weights or the remaining following product.

## Pen-And-Paper Reproduction

Let

```text
C' = [C0; Ctail]
D''' = [1 0; 0 0]
Wtail = diag(b0, b)
```

in pivot-first coordinates after failed next continuation.  Let `Cold` be a
supplied old top block, `Wold` a supplied old top row-weight matrix, and `F`
a supplied remaining following product.  Before removing any zero rows, there
is a matrix equality

```text
( blockdiag(Wold, Wtail) * [ Cold ; D''' * C' ] ) * F
  = [ (Wold * Cold) * F ;
      [ (b0 * C0) * F ;
        0 ] ].
```

The bottom zero block contributes no entry-ideal generators, so

```text
< entries((blockdiag(Wold,Wtail) * [Cold;D'''*C']) * F) >
  =
< entries([ (Wold*Cold)*F ; (b0*C0)*F ]) >.
```

This proof incorporates `F` before the zero-row deletion.  That matters:
entry-ideal equality is not preserved by arbitrary right multiplication.

## Boundaries

- `Cold`, `Wold`, `b0`, `b`, and `F` are supplied finite data.
- `b0` is not assumed to be a unit; the surviving row is `b0*C0`, not `C0`.
- `F` is included before the final entry-ideal zero-row drop.
- The theorem is still in displayed pivot-first coordinates.
- This does not identify `Cold` with Aoyagi's actual old top rows, identify
  `[Cold;C0]` or the weighted right hand side with `C'^(S+1)`, choose the
  row-vs-column terminal presentation, prove chart-produced post-data,
  compute Jacobians, prove chart coverage or regularity, prove normal
  crossings, extract RLCT, prove termination or transition invariance, or
  repair the printed Case 2 vector mismatch.
