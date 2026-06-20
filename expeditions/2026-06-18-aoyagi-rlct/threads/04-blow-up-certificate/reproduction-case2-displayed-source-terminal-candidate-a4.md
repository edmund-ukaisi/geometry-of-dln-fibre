# A4 Case 2 Displayed Source-Terminal Candidate

Status: reproduced the finite terminal-product assembly that keeps Aoyagi's
next diagonal weights outside the candidate next following matrix.  This is
not a construction of the full `S+1` transition.

## Source Anchor

Aoyagi PDF pp. 14-15 state the inductive product with a diagonal row-weight
factor and a block `[E_J 0; 0 D_J]`.  PDF pp. 20-22 perform the displayed Case
2 `Q/P` calculation and then, at the terminal stop, display

```text
< prod_s C^(s) >
  =
< diag(b_1,...,b_J,b'_(J+1),...,b'_(M(S+1)))
    C'^(S+1) prod_{s=S+2}^L C^(s) >.
```

The source also says that in the terminal branch `D'''_J` is either
`(1,0,...,0)` or its transpose.

## Pen-And-Paper Reproduction

Let

```text
F = prod_{s=S+2}^L C^(s),
C^(S+1) = [Cold; C_J],
Wold = diag(b_1,...,b_J).
```

Here `Cold` is the old top block in the current induction coordinates, not an
original source-coordinate block.  In displayed Case 2 the transported
following factor is

```text
C'_J^(S+1) = Q^-1 C_J^(S+1) = [C0; Ctail].
```

At failed next continuation, the stopped cleared block has the uniform
pivot-first effect

```text
D''' * C' = [C0; 0].
```

With residual successor weights `b0,b`, the previous checkpoint gives

```text
< entries((blockdiag(Wold, diag(b0,b)) * [Cold; D'''*C']) * F) >
  =
< entries([ (Wold*Cold)*F ; (b0*C0)*F ]) >.
```

The source-order terminal display should instead be read as keeping the next
weight matrix outside the candidate next following matrix:

```text
Cnext = [Cold; C0],
Wnext = blockdiag(Wold, [b0]),

< entries([ (Wold*Cold)*F ; (b0*C0)*F ]) >
  =
< entries((Wnext * Cnext) * F) >.
```

This is the finite matrix shape now named in Lean by
`case2DisplayedPaperTerminalCprimeCandidate`.

## Boundaries

- `Cold`, `Wold`, and `F` are still supplied.
- The residual weights are sourced from the supplied displayed boundary's
  successor recurrence state, as `post.weight`.
- The selected weight `b0 = post.weight (J+1)` is retained outside `Cnext`.
- The theorem incorporates the suffix `F` before entry-ideal zero-row
  deletion.
- This does not prove that `[Cold; C0]` is Aoyagi's source-produced
  `C'^(S+1)`.
- This does not choose the row-vs-column terminal branch beyond the uniform
  displayed pivot-first stopped block already formalised.
- This does not prove chart production, chart coverage or regularity,
  Jacobians, normal crossings, RLCT extraction, termination, transition
  invariance, or repair of the printed Case 2 vector mismatch.
