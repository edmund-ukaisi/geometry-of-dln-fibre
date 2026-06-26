# Reproduction - Lemma 5 first-nonbase order-formula bound

Status: finite notation handoff; formalised; reviewed.

Statement card:
`statement-card-a5-lemma5-first-nonbase-order-formula-bound.md`.

Review:
`review-lemma5-first-nonbase-order-formula-bound-a5.md`.

## Source Position

Aoyagi Lemma 5, PDF p. 25, gives the displayed order count

```text
theta = a*(ell-a)+1.
```

Aoyagi Theorem 2, PDF pp. 8-9, uses the same expression after Definition 3's
ceiling data.  In Lean this expression is named

```text
data.theorem2OrderFormula.
```

The previous first-nonbase cardinal-bound artifact proved the finite
cardinality estimate

```text
candidates.card <= a*(ell-a)+1
```

under supplied terminal binary-prefix-delta chains and supplied injectivity of
the deterministic first-nonbase-or-base selector.  This slice only rewrites
that result in Theorem 2 order notation.

## Pen-and-Paper Check

Let

```text
data : AoyagiDefinition3CeilData ell m.
```

By definition,

```text
data.theorem2OrderFormula
  = data.aParam * (ell - data.aParam) + 1.
```

The previous theorem applies with

```text
a = data.aParam,
M = data.ceilWidth.
```

The needed hypotheses are supplied by `data` or passed through unchanged:

```text
1 <= ell                         from data.ell_pos,
data.aParam <= ell               from data.aParam_le,
sum_i m_i = ell*(ceilWidth-1)+a  from data.selectedSum_eq.
```

Thus the existing first-nonbase bound gives

```text
candidates.card
  <= data.aParam * (ell - data.aParam) + 1
  = data.theorem2OrderFormula.
```

No new source claim is added.

## Lean Theorem

File:

```text
lean/DLNFibre/DLN/Aoyagi/Lemma5FirstNonbaseOrderBridge.lean
```

Theorem:

```text
aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le_theorem2OrderFormula
```

The proof applies

```text
aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le
```

with `data.aParam`, `data.ceilWidth`, and `data.selectedSum_eq`, then rewrites
`AoyagiDefinition3CeilData.theorem2OrderFormula`.

## Boundary

This slice does not prove:

- construction of Aoyagi's source vectors;
- that the first-nonbase selector is source-canonical;
- injectivity of the selector;
- a counted-datum back-to-label bridge;
- exact terminal-minimum label count;
- finite minimum-to-`lambda` equality;
- pole order, normal crossings, or RLCT extraction.
