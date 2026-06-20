# Pen-and-paper reproduction - Lemma 5 equation (3) piecewise certificate

Status: checked supplied branch certificate.

This note records a conservative formalisation boundary for Aoyagi Lemma 5
equation `(3)`: selected cutpoints and a supplied piecewise branch certificate.
It does not construct the displayed vector or prove terminal `tilde t=0`.

## Source

Aoyagi PDF p. 27, equation `(3)`, is for

```text
s = S_2-1,
k = Htilde'_1+1.
```

The displayed branches are

```text
T(S) = M(S+1)                if S < S_2-1,
T(S) = Htilde'_(j-1)         if S_j-1 <= S < S_(j+1)-1,
                              2 <= j <= ell-a+1,
T(S) = Htilde'_(ell-a+1)+1   if S = S_(ell-a+2)-1,
T(S) = Htilde'_(j-1)         if S > S_(ell-a+2)-1 and
                              S_j-1 <= S < S_(j+1)-1.
```

With zero-based selected blocks

```text
block C b S  <->  S_(b+1)-1 <= S < S_(b+2)-1,
```

the branches become:

```text
first:    S < C.point 1 - 1,
upper:    1 <= b <= ell-a,
boundary: S = C.point (ell-a+1) - 1,
tail:     ell-a+1 <= b and S is strictly after the boundary.
```

The strict tail condition is necessary.  The boundary point is the left
endpoint of block `ell-a+1` when that block exists, so it must not be absorbed
into the tail branch.

The supplied certificate also carries the guards

```text
a <= ell,
1 <= a.
```

These are part of the record because the boundary `S_(ell-a+2)` is a selected
source cutpoint only under the source range assumptions.  This avoids reading
the total Lean accessor `C.point` as a source-valid out-of-range convention.

## Classifier

Given a supplied certificate, every point in a selected block falls into one
of the four branch alternatives:

- block `b=0` is the first branch;
- blocks `1<=b<=ell-a` are upper branches;
- after that, the singleton boundary is handled separately;
- all remaining selected-block points strictly after the boundary are tail
  branch points.

The selected-span wrapper uses the already-proved fact that half-open selected
blocks cover exactly

```text
S_1-1 <= S < S_(ell+1)-1.
```

It deliberately does not cover the terminal selected endpoint
`S_(ell+1)-1`.

## Own Coordinate

Under `1<=a`, `a<ell`, Definition 3 selected-width hypotheses, and the
explicit slack `W_1+2<=M`, the source-shaped local arithmetic proves:

```text
(ell-a)+2 <= ell+1,
1 <= Htilde'_1+1 <= W_2.
```

Because `a<ell`, the block at `S_2-1` is in the upper branch (`1<=1<=ell-a`),
so a supplied equation `(3)` piecewise certificate gives

```text
T(S_2-1) = Htilde'_1.
```

This is the own-coordinate value `k-1`, but the Lean theorem states the
selected value and label bounds only; it does not claim introduced-label
status or terminality.

## Terminal Boundary

Equation `(3)` is not a terminal endpoint theorem.  If `a=1`, then
`ell-a+1=ell`, so the displayed special boundary is the terminal selected
endpoint `S_(ell+1)-1` and the printed value is `Htilde'_ell+1=1`, while
Definition 3 gives `Htilde'_ell=0`.

Thus any terminal-zero theorem must be conditional on a separate terminal
endpoint assignment, not derived from the equation `(3)` display.

## Lean Targets

```text
AoyagiLemma5Eq3PiecewiseSourceVector
AoyagiLemma5Eq3SelectedSpanBranchValue
aoyagiLemma5Eq3_branchValue_of_block
aoyagiLemma5Eq3_selectedSpan_branchValue
aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack
```

## Nonclaims

- No construction or existence proof for the equation `(3)` displayed vector.
- No claim that the selected-span classifier covers the terminal endpoint.
- No terminal `tilde t=0` theorem.
- No introduced-label theorem.
- No chart-family coverage, source vector-to-chain correspondence, Lemma 5
  order count, pole order, normal crossings, or RLCT extraction.
