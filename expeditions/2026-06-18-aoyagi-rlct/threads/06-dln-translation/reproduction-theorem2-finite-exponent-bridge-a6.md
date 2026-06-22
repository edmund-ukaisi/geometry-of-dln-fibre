# Reproduction - A6/A0 finite exponent bridge for Theorem 2

Source: Aoyagi 2023 PDF pp. 5-9, with the analytic extraction boundary fixed
by A0 and the formula notation fixed by the existing A6 cards.

## Goal

This slice is a conditional bridge.  It does not construct
normal-crossing charts and does not prove the finite exponent equalities from
Aoyagi's blow-up recursion.  It records the exact final algebra once those
finite equalities and the cited A0 extraction hypothesis are supplied.

## Data

Let `D` be finite normal-crossing exponent data.  Let `data` be a supplied
`AoyagiDefinition3CeilData ell m`.  The finite certificate still to be proved
in A4/A5 must eventually supply:

```text
D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData L ell H r m data,
D.exponentOrder   = data.theorem2OrderFormula.
```

These are packaged as `AoyagiTheorem2FiniteExponentFormulaHypothesis`.

Separately, A0 supplies only the cited extraction interface:

```text
AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder,
```

which states:

```text
lambda    = D.exponentMinimum,
poleOrder = D.exponentOrder.
```

## Calculation

Combining the two displayed pairs gives:

```text
lambda
  = D.exponentMinimum
  = aoyagiTheorem2Lambda_fromCeilData L ell H r m data,
```

and

```text
poleOrder
  = D.exponentOrder
  = data.theorem2OrderFormula.
```

The already-proved A6 formula rewrites then give the average and expanded
forms of the displayed `lambda` formula:

```text
aoyagiTheorem2Lambda_average
  = aoyagiTheorem2Lambda_fromCeilData
  = aoyagiTheorem2Lambda_expanded.
```

## Nonclaims

This slice does not prove:

- finite exponent equality from a chart certificate;
- source parameter provenance `m = H(S_j)-r`;
- Definition 3 selected-cutpoint inequalities or existence;
- rank-width hypotheses;
- chart production;
- unit factors;
- Jacobian/prior exponent correctness;
- normal crossings;
- Aoyagi Lemma 5 no-extra coverage;
- the Lemma 5 order count;
- order identification without the A0 hypothesis;
- the analytic normal-crossing extraction theorem.

The value of this slice is that future A4/A5 work has a precise final socket:
prove the two finite exponent equalities, then A0 and A6 assemble the displayed
formula without any hidden analytic step.
