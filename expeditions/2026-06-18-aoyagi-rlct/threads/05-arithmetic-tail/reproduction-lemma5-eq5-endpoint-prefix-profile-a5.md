# Reproduction - Lemma 5 Eq5 endpoint prefix profile

Status: reproduced; Lean checked.

## Source

Aoyagi's equation `(5)` gives a piecewise formula for source-layer values.
For a supplied endpoint chain `H`, assume that every interior endpoint
coordinate is read from the left endpoint of the corresponding selected block:

```text
H_b = T(C.point b - 1),  1 <= b < ell.
```

This slice records the Lemma 4 prefix value at those endpoints branch by
branch.

## Calculation

Let

```text
D_b = aoyagiLemma4IncrementPrefix ell M m H b.
```

The generic prefix-profile computations give:

```text
H_b = Htilde'_b - r  ->  D_b = upperHighCount_b + r
H_b = Htilde_b      ->  D_b = lowerHighCount_b.
```

For equation `(5)` at a left endpoint:

- pre-alpha branch:
  `T = Htilde'_b - b`, and alpha-domain bounds force
  `upperHighCount_b = 0`, so `D_b = b`;
- alpha-to-`p` branch:
  `T = Htilde'_b - (alpha-1)`, and terminal-room bounds force
  `upperHighCount_b = 0`, so `D_b = alpha-1`;
- post-`p` branch:
  `T = Htilde'_b - (alpha+b-p)`, and terminal-room bounds force
  `upperHighCount_b = 0`, so `D_b = alpha+b-p`;
- tail branch:
  `T = Htilde_b`, and the tail guard plus `alpha<p` force
  `lowerHighCount_b = a`, so `D_b = a`.

## Lean Targets

```text
aoyagiLemma5Eq5_endpointChain_incrementPrefix_preAlpha
aoyagiLemma5Eq5_endpointChain_incrementPrefix_alphaToP
aoyagiLemma5Eq5_endpointChain_incrementPrefix_postP
aoyagiLemma5Eq5_endpointChain_incrementPrefix_tail
```

## Use

These are the branchwise endpoint-profile facts needed for a later binary
prefix-delta proof.  They deliberately do not combine adjacent branches or
prove that every successive prefix difference is `0` or `1`.

## Nonclaims

- No binary prefix-delta theorem is proved.
- No Lemma 4 two-value increment theorem is proved.
- No Eq5 vector construction, endpoint realisation, terminality,
  classifier/injection/back-to-label coverage, order count, pole order, normal
  crossings, or RLCT extraction is proved.
