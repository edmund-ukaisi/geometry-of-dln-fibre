# Reproduction - Lemma 5 Eq5 binary endpoint prefix deltas

Status: reproduced; Lean checked.

## Source

This slice is the finite adjacent-difference calculation for the endpoint
chain attached to a supplied equation `(5)` branch.  It uses:

- the supplied Eq5 piecewise branch equalities;
- the supplied endpoint-chain correspondence
  `H_b = T(C.point b - 1)` for `1 <= b < ell`;
- the source convention `H_0=m_0`;
- the terminal convention `H_ell=0`;
- the selected-width sum, so the terminal Lemma 4 prefix is `a`;
- the terminal-room inequality `p+2*a-alpha <= ell`.

It is independent of the quiver-based paper.

## Calculation

Let

```text
D_b = aoyagiLemma4IncrementPrefix ell M m H b
q   = p + (a - alpha).
```

The previous endpoint-profile slice gives, for `1 <= b < ell`,

```text
pre-alpha:  D_b = b               if b+2 <= alpha
alpha-p:    D_b = alpha-1         if alpha <= b+1 <= p
post-p:     D_b = alpha+b-p       if p <= b <= q
tail:       D_b = a               if q+1 <= b.
```

The endpoint hypotheses add

```text
D_0   = 0
D_ell = a.
```

The adjacent differences split as follows.

```text
0 <= b < alpha-1:  D_(b+1)-D_b = 1
alpha-1 <= b < p-1:  D_(b+1)-D_b = 0
p-1 <= b < q:  D_(b+1)-D_b = 1
q <= b < ell:  D_(b+1)-D_b = 0
```

The first boundary covers `alpha=1`: then the first rising range is empty and
`D_1-D_0=0`.  The `p=alpha+1` case gives a one-step alpha-to-`p` flat delta
at `b=alpha-1`, followed by a rise at `b=p-1`.  If `alpha=a`, then `q=p`,
so the post-`p` branch has only the endpoint `b=p` and the final plateau
starts immediately after.  If `b+1=ell`, the successor prefix is the terminal
value `a`, not a selected-block endpoint value.

## Lean Targets

```text
aoyagiLemma5Eq5_endpointChain_incrementPrefix_profile_of_terminalRoom
aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefixDelta_of_terminalRoom
```

## Use

The binary-delta theorem supplies the hypothesis required by the existing
Lemma 4 bridges from binary prefix deltas to two-value increments, chain
bounds, and finite counts.

## Nonclaims

- No Eq5 vector is constructed.
- No endpoint-chain realisation from source labels is proved.
- No terminality is constructed; `H_ell=0` is supplied.
- No classifier, injection, back-to-label coverage, order count, pole order,
  normal crossings, or RLCT extraction is proved.
