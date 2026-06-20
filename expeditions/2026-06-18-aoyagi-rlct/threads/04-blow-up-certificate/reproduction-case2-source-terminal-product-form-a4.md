# A4 Case 2 Source Terminal Product Form

Status: reproduced the elementary product-form equality for the stopped
displayed Case 2 source-row terminal product candidate.

## Source Anchor

On PDF pp. 21-22, Aoyagi's stopped Case 2 terminal display is in source order:

```text
diag(b_1,...,b_J,b'_(J+1),...) C'^(S+1) prod_{s=S+2}^L C^(s).
```

The present checkpoint does not construct the source-produced matrix
`C'^(S+1)`.  It only proves that the already named source-row candidate is
the product of the already named source-row terminal weight and source-row
terminal next-factor candidate.

## Pen-And-Paper Reproduction

Let

```text
e : I_old ⊕ {*} ≃ I_term
```

be the row equivalence sending old rows `1..J` to themselves and the surviving
pivot row to `J+1`.  Put

```text
W      = blockdiag(Wold,[b0]),
Cnext  = [Cold; C0],
F      = remaining suffix.
```

The row-reindexed source terminal product candidate is

```text
((W Cnext) F).submatrix e^{-1} id.
```

Because reindexing by an equivalence commutes with matrix multiplication,

```text
((W Cnext) F).submatrix e^{-1} id
  = ((W Cnext).submatrix e^{-1} id) (F.submatrix id id)
  = ((W.submatrix e^{-1} e^{-1}) (Cnext.submatrix e^{-1} id)) F.
```

The first reindexed factor is exactly the source terminal weight candidate,
and the second is exactly the source terminal `C'` candidate.  Therefore the
source-row terminal product candidate equals

```text
(sourceTerminalWeight * sourceTerminalCprimeCandidate) * F.
```

## Lean Shape

The Lean theorem is:

```text
case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_cprimeCandidate_mul
```

It is proved by unfolding the source-row candidates and applying
`Matrix.submatrix_mul_equiv` twice: first across the final multiplication by
`F`, then across the inner terminal weight times terminal next-factor product.

## Boundaries

- This is pure matrix-reindexing algebra.
- It does not prove that the source-row terminal `C'` candidate is
  chart-produced.
- It does not prove Aoyagi's full source-produced `C'^(S+1)`.
- It does not prove chart coverage, coordinate regularity, Jacobian
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariance, automatic Case 2 gap/tail transport, or printed-vector repair.

## Kill Conditions

- Do not use this equality as evidence that the supplied terminal data are
  source-produced by the blow-up chart.
- Do not cite Aoyagi for this equality as a source theorem; Aoyagi supplies
  the terminal display orientation, while the equality is definitional
  reindexing of the repo's candidate objects.
