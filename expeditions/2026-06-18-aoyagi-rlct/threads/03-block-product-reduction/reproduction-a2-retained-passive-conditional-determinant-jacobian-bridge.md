# Reproduction - A2 retained-passive conditional determinant/Jacobian bridge

## Claim

This note reproduces the elementary determinant bridge needed after the
retained-passive formal raw-order determinant calculation.

Let

- `E` be the retained-passive raw topology tuple vector space;
- `Phi` be the retained-passive raw-order coordinate map
  `topologyTupleEdgeRawOrder`;
- `D = D Phi_z : E -> E` be its Frechet derivative at a determinant-chart
  point `z`;
- `F_z = retainedPassiveFormalRawOrderJacobianAt z` be the point-specialized
  formal raw-order linear map;
- `T : E ~= E` be a target-side linear equivalence.

Assume

```text
T (D v) = F_z v      for every tangent v in E,
|det T| = 1.
```

Then

```text
topologyTupleEdgeRawOrderFDerivAbsDet z
  = retainedPassiveFormalRawOrderJacobianAbsDetAt z.
```

Composing this with the already-proved formal product determinant formula gives
the explicit product expression in the solved retained-passive blocks.

## Pen-and-paper derivation

The pointwise identity `T (D v) = F_z v` says exactly that, as linear maps,

```text
F_z = T o D.
```

Taking determinants over the finite-dimensional real vector space `E` gives

```text
det(F_z) = det(T o D) = det(T) det(D).
```

Taking absolute values gives

```text
|det(F_z)| = |det(T)| |det(D)|.
```

By the determinant-one target-normalization hypothesis, `|det(T)| = 1`.
Therefore

```text
|det(F_z)| = |det(D)|.
```

The two sides are precisely the local Lean definitions:

```text
topologyTupleEdgeRawOrderFDerivAbsDet z = |det(D)|,
retainedPassiveFormalRawOrderJacobianAbsDetAt z = |det(F_z)|.
```

Hence the two absolute Jacobian determinants are equal.

## Product determinant dependency

The product-form corollary uses no further analytic input.  It substitutes the
formal determinant formula

```text
retainedPassiveFormalRawOrderJacobianAbsDetAt_eq
```

which expands the formal determinant as

```text
|Tail^-1.det| ^ card rho
  * prod_p |solvedA1(p).det| ^ card(kappa'(p.castSucc))
  * |solvedA1(last M).det| ^ card(kappa'(last (M+1))).
```

Here `Tail` is
`ChartLocalSuffixState.retainedPassiveA1TailAfterFirst data.A1seed`, and
`data`/`coord` are the retained-passive coordinate data read from `z`.

## Source and scope

This is Aoyagi-product-reduction coordinate algebra around PDF pp. 11-13, but
the determinant bridge itself is an elementary finite-dimensional linear
algebra step.  It packages existing Lean facts; it does not add a new source
claim about the original DLN prior or normal-crossing extraction.

## Kill conditions

- If the supplied map `T` is not a genuine linear equivalence on the same
  retained-passive raw tuple vector space, the determinant equation does not
  apply.
- If the pointwise identity is only componentwise after source-dependent
  nonlinear substitutions rather than a single linear target-side map at `z`,
  the theorem must remain conditional and must not be used as determinant
  equality for the actual derivative.
- If `|det T|` is not proved to be `1`, the conclusion changes by the factor
  `|det T|`.
- This bridge does not prove source-prior transport, inverse-density
  pushforward, chart coverage, normal crossings, pole order, or RLCT.

## Lean target

```text
topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_of_target_linearEquiv
```

and a product-form corollary obtained by rewriting with
`retainedPassiveFormalRawOrderJacobianAbsDetAt_eq`.
