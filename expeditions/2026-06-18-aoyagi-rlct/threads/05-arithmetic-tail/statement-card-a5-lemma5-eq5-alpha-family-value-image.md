# Statement card - A5 Lemma 5 equation (5) alpha-family value image

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaFamily_value_image_eq_offsetValueSet`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5AlphaDomain`

## Claim

The strict equation `(5)` alpha-family value image

```text
(aoyagiLemma5Eq5AlphaDomain ell a p).image
  (alpha |-> aoyagiHtildeUpperNat ell a M m p - alpha)
```

is exactly

```text
aoyagiLemma5Eq5OffsetValueSet ell a p M m.
```

## Proved

Lean proves the equality by unfolding `aoyagiLemma5Eq5AlphaDomain` and
`aoyagiLemma5Eq5OffsetValueSet`.

## Assumed

No mathematical hypotheses.  The theorem is finite-set API naming.

## Cited

None in Lean.  Source fidelity is to Aoyagi PDF p. 27 equation `(5)` and the
displayed `Htilde` chains on PDF pp. 25-26, already represented by the
existing Eq5 offset definitions.

## Deferred

Displayed-vector construction, source-label legality for `k`, selected-span
coverage, terminal `tilde t=0`, chart sequence, Lemma 5 order count, pole
order, normal crossings, and RLCT extraction.

## Review

- xhigh source/scope scout `Meitner` accepted this as finite bookkeeping only.
- xhigh Lean API scout `Kuhn` confirmed the exact theorem checks by `rfl` and
  recommended no separate image definition.
