# Review - Lemma 5 equation (4) boundary-coordinate window

Reviewer: Confucius, xhigh effort.

Status: no blocking findings.

## Findings

No blocking issues found.

## Mathematical Check

The boundary coordinate is correctly separated from the earlier classifier:
the previous classifier uses coordinate `p+(ell-a)`, while this slice uses the
boundary block's own coordinate

```text
r = p+(ell-a)+1.
```

The offset formula is correct.  The upper-chain successor rule gives

```text
U_r = U_(r-1) + W_r - M,
```

and the supplied equation `(4)` boundary branch gives

```text
B = U_(r-1) - p + 1.
```

Therefore

```text
B - U_r = M - W_r - p + 1.
```

The membership iff width window is correct:

```text
B in [L_r,U_r]
iff M-p+1 <= W_r <= M-p+1+excess(ell,a,r).
```

The reduced strict-boundary excess

```text
excess(ell,a,r) = min(ell-a,a-p-1)
```

is the right finite minimum simplification.

The `p=1` Definition 3 source corollary is not overclaimed: it remains
conditional on a supplied equation `(4)` certificate plus selected-width sum
and strict selected-width inequalities, and proves only above-upper and
nonmembership at the boundary coordinate.

## Scope Check

This slice remains finite supplied-branch and interval arithmetic only.  It
does not validate existence of the displayed vector, terminal `tilde t=0`,
Lemma 5 order count, normal crossings, or RLCT extraction.

## Verification

The reviewer independently ran:

```text
lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
scripts/sorries
git diff --check
```

and they passed.
