# Review - Lemma 5 equation (5) alpha-family value image

Status: reviewed and formalised.

## Scope

The theorem names the definitional equality between the strict alpha-family
image over `aoyagiLemma5Eq5AlphaDomain` and the existing
`aoyagiLemma5Eq5OffsetValueSet`.

## Verdict

No findings.  This is safe as a finite-set API theorem provided the alpha
family has exactly the strict offset domain

```text
1 <= alpha <= min(excess(ell,a,p), p-1)
```

and value map

```text
alpha |-> Htilde'_p - alpha.
```

## Xhigh Checks

Source/scope scout `Meitner` accepted the statement as source-faithful finite
bookkeeping from Aoyagi PDF p. 27 equation `(5)`, with the displayed chains
from PDF pp. 25-26.

Lean API scout `Kuhn` confirmed the theorem is a pure wrapper around the
existing definition.  The later branch-image slice added the standalone
alpha-domain API because downstream statements now need that domain as a
named hypothesis target.

## Nonclaims

This theorem does not construct equation `(5)`'s displayed vector, prove
source-label legality for `k`, prove selected-span coverage, terminal
`tilde t=0`, chart sequence, Lemma 5 order count, pole order, normal crossings,
or RLCT extraction.
