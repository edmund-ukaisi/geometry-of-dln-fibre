# Review - Definition 3 all-source strict rank-width

Date: 2026-06-24.

Reviewer: xhigh independent reviewer `Parfit the 3rd`.

## Verdict

PASS.  No required corrections.

## Source Fidelity

Aoyagi Definition 3 on PDF pp. 8-9 defines `M^(s)=H^(s)-r` and gives the
selected strict inequality

```text
sum_k M^(S_k) > ell * M^(s).
```

In the all-source specialization `ell=L`, `C.cut j=j+1`, this is exactly the
hypothesis used by the Lean theorem.

## Mathematical Check

The pen-and-paper argument is correct.  For a fixed source index, summing the
strict inequalities over the other `L` source indices gives

```text
L * sum_{t != s} M^(t) < L * sum_t M^(t).
```

Since `0<L`, cancellation gives `sum_{t != s} M^(t) < sum_t M^(t)`, hence
`0 < M^(s)`.  Therefore `r < H(s)`, and the required `r <= H(s)` follows.

## Lean/API Check

Focused Lean check passed:

```text
env LEAN_NUM_THREADS=1 lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

The wrapper theorem only composes the new rank-width consequence with the
existing `_rankWidth` all-source ceiling-data package.

## Scope Check

No overclaim found.  The docs restrict the result to the all-source branch and
do not assert arbitrary branch selection, branch-independent formula payloads,
chart production, normal crossings, pole order, RLCT extraction, or
quiver-based facts.
