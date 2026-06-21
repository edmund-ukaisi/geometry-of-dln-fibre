# Pen-and-paper reproduction - Lemma 5 equation (5) piecewise certificate

Status: checked supplied branch certificate.

This note records a conservative formalisation boundary for Aoyagi Lemma 5
equation `(5)`: selected cutpoints and a supplied piecewise branch
certificate.  It does not construct the displayed vector or prove terminal
`tilde t=0`.

## Source

Aoyagi PDF p. 27, equation `(5)`, is for

```text
alpha = Htilde'_(j0)+1-k,
S_(j0+1)-1 <= s < S_(j0+2)-1,
Htilde_(j0)+1 <= k < Htilde'_(j0)+1,
j0 > alpha.
```

The displayed branches are

```text
T(S) = M(S+1)                         if S < S_2-1,
T(S) = Htilde'_(j-1)-j+1              if 2 <= j <= alpha-1,
T(S) = Htilde'_(j-1)-alpha+1          if alpha <= j <= j0,
T(S) = Htilde'_(j-1)-alpha+1-(j-j0)   if j0 < j <= j0+(a-alpha)+1,
T(S) = Htilde_(j-1)                   if S >= S_(j0+(a-alpha)+2)-1.
```

Each branch after the first is restricted to the selected block

```text
S_j-1 <= S < S_(j+1)-1.
```

## Zero-Based Translation

Lean uses

```text
C.point b = S_(b+1),
C.block b S iff S_(b+1)-1 <= S < S_(b+2)-1.
```

Thus paper block `j` corresponds to Lean block `b=j-1`, and the paper
parameter `j0` is Lean coordinate `p`.  The source guard on `s` is exactly
`C.block p s`.

The branches become:

```text
first:
  S < C.point 1 - 1,
  T(S) = layerWidth(S+1).

preAlpha:
  1 <= b and b+2 <= alpha,
  T(S) = Htilde'_b - b.

alphaToP:
  1 <= b, alpha <= b+1, and b+1 <= p,
  T(S) = Htilde'_b - alpha + 1.

postP:
  p <= b and b <= p+(a-alpha),
  T(S) = Htilde'_b - alpha + p - b.

tail:
  p+(a-alpha)+1 <= b and C.point(p+(a-alpha)+1)-1 <= S,
  T(S) = Htilde_b.
```

The final cutoff guard

```text
p+(a-alpha)+1 <= ell
```

is stored in the supplied certificate because the source row mentions
`S_(j0+(a-alpha)+2)`.

## Classifier

Let `S` lie in selected block `b`.

If `b=0`, then `S<C.point 1-1`, so the first branch applies.

Assume `b!=0`, hence `1<=b`.

If `b+2<=alpha`, the pre-alpha branch applies.

Otherwise `alpha<=b+1`.  If `b+1<=p`, the alpha-to-`p` branch applies.

Otherwise `p<=b`.  If `b<=p+(a-alpha)`, the post-`p` branch applies.

Otherwise

```text
p+(a-alpha)+1 <= b.
```

For the tail source inequality, if `b=p+(a-alpha)+1`, it is just the lower
bound of the selected block.  If `p+(a-alpha)+1<b`, monotonicity of selected
cutpoints gives

```text
C.point(p+(a-alpha)+1)-1 < S.
```

So the tail branch applies.

The selected-span theorem then follows from the existing selected-block
coverage: every

```text
C.point 0 - 1 <= S < C.point ell - 1
```

lies in some selected block.

## Own Coordinate

At the own coordinate, `b=p`, so the post-`p` branch gives

```text
T(S) = Htilde'_p - alpha + p - p = Htilde'_p - alpha.
```

Therefore a supplied equation `(5)` piecewise certificate implies the
previously defined own-coordinate branch record.

## Lean Targets

```text
AoyagiLemma5Eq5PiecewiseSourceVector
AoyagiLemma5Eq5SelectedSpanBranchValue
aoyagiLemma5Eq5_branchValue_of_block
aoyagiLemma5Eq5_selectedSpan_branchValue
aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector
```

## Nonclaims

- No construction or existence proof for equation `(5)`'s displayed vector.
- No source-label legality proof for `k`.
- No terminal `tilde t=0` theorem.
- No coverage before `S_1-1`, at `S_(ell+1)-1`, or after the selected span.
- No vector admissibility or source-vector-to-chain correspondence.
- No Case 1(2) chart sequence.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
