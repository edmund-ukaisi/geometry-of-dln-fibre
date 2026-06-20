# A4 Case 2 Identity-Following Actual-Width Boundary

Status: reproduced the identity-following specialization of the displayed
source-chart actual-width terminal boundary.

## Source Anchor

Aoyagi's stopped terminal expression on PDF pp. 21-22 has a remaining right
product after the terminal `C'^(S+1)` factor.  The preceding checkpoint proves
that this source suffix is the identity in the terminal-last case `S+1=L`.

This checkpoint is the algebraic boundary after that right factor has already
been identified with the identity matrix.

## Pen-And-Paper Reproduction

The arbitrary-following actual-width theorem gives, for any supplied following
matrix `F`,

```text
ideal((blockdiag(oldTopWeight, transformed residual block)
        * [old source rows ; source following factor]) * F)
  =
ideal((terminalWeight(post.stageRelabelSuccZero)
        * originalRows(1..J+1)) * F),
```

with the relabelled `(S+1,0)` level and exponent certificates.

Taking `F=1` and using associativity/unit laws gives

```text
ideal(blockdiag(oldTopWeight, transformed residual block)
        * [old source rows ; source following factor])
  =
ideal(terminalWeight(post.stageRelabelSuccZero)
        * originalRows(1..J+1)).
```

The original-row branch still uses actual-width exhaustion

```text
n(S+1)=J+1.
```

## Boundaries

- This theorem specializes a supplied following matrix to `1`.
- It does not prove that a source suffix is empty; that is the separate
  `sourceSuffixProduct_terminalLast_eq_cast_one` theorem.
- It does not apply to row-exhausted wide-next cases.
- It does not prove chart coverage, source production of `C'^(S+1)`,
  chart-produced following products, Jacobian arithmetic, normal
  crossings/RLCT extraction, termination, transition invariance, or repair of
  the printed Case 2 vector mismatch.
