# Pen-and-paper reproduction - A4 Case 2 successor following weighted handoff

Status: reproduced, xhigh-checked, and formalised.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The source displays the local pivot chart,
forms the transported following factor `C' = Q^-1 C`, clears the lower-right
block to `D'''`, and continues with `J` increased when the post-pivot block is
still present.

Existing artifacts already prove the paper-`C'` lower-row handoff and the
formula-level source successor following factor.  This checkpoint only rewrites
the lower-row handoff in the successor-factor notation.

## Reproduction

Let

```text
Csucc(j,a) =
  if j = J+1 then top row of (Q^-1 C) at a
  else C(j,a).
```

The next same-stage following factor at `(S,J+1)` is indexed by the post-pivot
source rows

```text
J+2 <= j <= n(S+1).
```

Thus every row in this restriction is different from the replaced row `J+1`.
Therefore, pointwise,

```text
case2SourceFollowingFactor(S,J+1,Csucc)
  =
case2SourceFollowingFactor(S,J+1,C).
```

The existing displayed paper-`C'` lower-row theorem gives

```text
source lower rows
  =
successor lower diagonal *
  (post-pivot residual block *
   case2SourceFollowingFactor(S,J+1,C)),
```

with the corrected Case 2 exponent, level, least-value-gap, and recurrence-gap
post-data carried as projections from the supplied boundary.  Substituting the
restriction equality gives the same theorem with

```text
case2SourceFollowingFactor(S,J+1,Csucc)
```

on the right.

Right-multiplying both sides by an arbitrary supplied following product `F`
gives the supplied-`F` variant.  The matrix `F` is not produced here.

## Lean Names

```text
sourceChartMap_paperCprimeWeightedLowerRows_withSuccFollowingFactorAndCorrectedData
sourceChartMap_paperCprimeWeightedLowerRows_mul_F_withSuccFollowingFactorAndCorrectedData
```

## Boundary Checks

- This is lower-row formula algebra only.
- No nonempty next-center hypothesis `J+2 <= prefixMinNat n (S+1)` is used.
- The optional following product `F` remains supplied.
- The theorem does not include the pivot row, old top rows, old top
  multiplier, or suffix product.
- Corrected post-data are carried from the supplied boundary, not derived from
  chart coordinates.
- Row exhaustion and actual next-width exhaustion remain separate; only actual
  next-width exhaustion can collapse `Csucc` to `C`.

## Kill Conditions

- Do not call this chart production.
- Do not call it a full successor `C'^(S+1)` construction.
- Do not infer source production of `F`, a successor chart family, transition
  invariance, chart coverage, arbitrary-pivot coverage, Jacobian arithmetic,
  normal crossings, pole order, termination, RLCT, or repair of Aoyagi's
  printed Case 2 vector mismatch.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.
