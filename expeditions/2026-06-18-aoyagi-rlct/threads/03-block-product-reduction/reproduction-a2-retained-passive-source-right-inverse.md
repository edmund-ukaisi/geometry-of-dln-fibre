# Reproduction - A2 Retained-Passive Source Right Inverse

Date: 2026-06-26.

Status: reproduced and formalised the finite right-inverse algebra for the
retained-passive source readback on the recursive determinant chart.

## Question

For an arbitrary retained-passive-shaped edge family

```text
E p : Matrix (rho plus kappa' p.succ) (rho plus kappa' p.castSucc) K
```

satisfying the source-recursive determinant predicate, prove the finite
right-inverse theorem

```text
(sourceReadback E).edgeMatrix = E.
```

The previous rung already reconstructed the solved `A1` family from the
top-left blocks of the transformed source edges.  This rung supplies the
missing solved-`A3` reconstruction and then performs the final Schur
reassembly and upper-unitriangular cancellation.

## Notation

Write

```text
S_i(E) = sourceReadbackSuffixState E i,
T_p(E) = sourceReadbackTransformedEdge E p.
```

Thus

```text
T_p(E) = [I, S_{p.succ}.B; 0, I] * E p.
```

The source readback stores

```text
A1 p = topLeftCorner T_p(E)
F2 p.castSucc = -(topLeftCorner T_p(E))^-1 * upperRightBlock T_p(E)
A3 p = lowerLeftBlock T_p(E)     except the final component is solved
C p  = schurResidualBlock T_p(E).
```

The determinant hypothesis gives an inverse for every top-left block of
`T_p(E)`, and the preceding spine gives

```text
solvedA1 p = topLeftCorner T_p(E).
```

## Product Formulas

The solved full `A1` products of `sourceReadback E` reproduce source suffix
`Ctop` blocks:

```text
residualFactorProduct solvedA1 last i = S_i(E).Ctop.
```

This is a backward induction from the terminal state.  The step is exactly the
suffix recurrence

```text
S_{p.castSucc}.Ctop = S_{p.succ}.Ctop * topLeftCorner T_p(E),
```

combined with the already proved solved-`A1` readback.

The source suffix `D` blocks similarly reproduce products of stored Schur
residual coordinates:

```text
S_i(E).D = residualFactorProduct C last i.
```

This uses the generic `residualProduct` API: the residual block of the source
family at edge `p` is definitionally the stored readback field `C p`.

## Lower-Left Tail

The lower-left block of the suffix left multiplier satisfies the same
backward recurrence as the explicit retained-passive lower-left product-tail
sum:

```text
lowerLeftBlock S_i(E).L
  = retainedPassiveLowerLeftProductTailSum solvedA1
      (fun p => lowerLeftBlock T_p(E)) C i.
```

The one-step calculation is

```text
lowerLeftBlock (step E p S).L
  = -(S.D * lowerLeftBlock T_p(E) * (step E p S).Ctop^-1)
      + lowerLeftBlock S.L.
```

This follows from lower-unitriangularity of the suffix `L` multiplier.  After
substituting the `D` product and the solved-`A1` product for the new `Ctop`,
the recurrence is exactly the retained-passive tail-sum recurrence.

At `i = 0`, the source-readback definition has

```text
F3 = lowerLeftBlock S_0(E).L,
```

so the full lower-left product tail built from the actual transformed
lower-left blocks is `F3`.

## Final A3 Cancellation

For non-final `p`, the solved `A3` component is just the passive seed, hence
the readback lower-left block directly.  The only real case is the final edge.

Let `A3actual p = lowerLeftBlock T_p(E)`.  The explicit tail split gives

```text
earlyTail + lastTail = F3,
```

where `earlyTail` is the product tail with the final `A3` block zeroed and

```text
lastTail = -(A3actual last * CtopLast^-1)
```

up to the identity matrix on the lower-left index.  Therefore

```text
F3 - earlyTail = -(A3actual last * CtopLast^-1).
```

The retained-passive final solver is

```text
solvedA3 last = -(F3 - earlyTail) * CtopLast.
```

Substitution reduces it to

```text
(A3actual last * CtopLast^-1) * CtopLast = A3actual last,
```

which is matrix inverse cancellation under the determinant-unit hypothesis for
`CtopLast`.  This proves

```text
sourceReadback_solvedA3_eq_lowerLeftBlock.
```

## Edge Reassembly

For each edge `p`, the retained-passive transformed edge reconstructed from
the source readback has the Schur readbacks of `T_p(E)`:

```text
A1 = topLeftCorner T_p(E)
F2 = -(A1^-1 * upperRightBlock T_p(E))
A3 = lowerLeftBlock T_p(E)
C  = schurResidualBlock T_p(E).
```

The generic Schur lemma `fromBlocks_schurReadbacks_eq` therefore gives

```text
retainedPassiveTransformedEdge (sourceReadback E) p = T_p(E).
```

Finally, the fixed-base edge matrix formula multiplies `T_p(E)` on the left by
the upper-unitriangular matrix with right block `F2full p.succ`.  The previous
spine proved

```text
F2full p.succ = -S_{p.succ}(E).B,
```

so the two upper-unitriangular matrices cancel:

```text
[I, -S.B; 0, I] * [I, S.B; 0, I] = I.
```

Thus each edge is recovered:

```text
(sourceReadback E).edgeMatrix p = E p.
```

## Nonclaims

This proves a finite right inverse on the recursive determinant chart.  It is
an algebraic image-membership theorem only for edge families satisfying
`sourceRecursiveDetChart`.  It does not prove that this chart is open, that it
equals the whole source image, a local homeomorphism, source-rank coverage,
measure pushforward, density/Jacobian transport, normal crossings, pole order,
or RLCT extraction.

