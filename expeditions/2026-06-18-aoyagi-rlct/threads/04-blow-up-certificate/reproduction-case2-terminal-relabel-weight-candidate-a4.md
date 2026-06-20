# A4 Case 2 Terminal Relabel-Weight Candidate

Status: reproduced the elementary rewrite of the stopped displayed Case 2
terminal candidate using the relabelled `(S+1,0)` post-state pivot weight.
This is a supplied terminal-product wrapper, not a terminal transition theorem.

## Source Anchor

The previous terminal source-model checkpoints isolated Aoyagi's displayed
Case 2 terminal branch on PDF pp. 20-22.  The stopped candidate has source-order
shape

```text
(blockdiag(Atop, [b0]) * [Ctop; C0]) * F,
```

where `Atop`, `Ctop`, and `F` are supplied old-top/suffix data, and `C0` is the
top pivot row of the transported following factor `C' = Q^-1 C`.

The actual-width terminal relabel checkpoint then copied supplied post-state
recurrence maps from old `(S,J+1)` to `(S+1,0)` under

```text
n(S+1) = J+1.
```

## Pen-And-Paper Reproduction

The existing stopped terminal product theorem uses the old supplied post-state
pivot weight

```text
b0 = post.weight(J+1).
```

Under actual next-width exhaustion, the old introduced-label domain
`(S,J+1)` equals the relabelled stage domain `(S+1,0)`.  The relabelled
post-state copies the same `level` and `var` maps, so the finite product
`step` is the same.  Therefore every row weight is the same:

```text
terminalRelabelPost.weight(i) = post.weight(i).
```

In particular,

```text
terminalRelabelPost.weight(J+1) = post.weight(J+1).
```

Actual-width exhaustion also implies failed next continuation:

```text
not (J+2 <= prefixMinNat n (S+1)).
```

Thus the stopped terminal entry-ideal theorem can be restated with

```text
b0 = terminalRelabelPost.weight(J+1)
```

instead of `post.weight(J+1)`.

## Boundaries

- This only rewrites a scalar in an already supplied terminal-product
  candidate.
- `Atop`, `Ctop`, and `F` remain supplied.
- The source-model wrapper is specialized to a model whose `b0` parameter is
  `terminalRelabelPost.weight(J+1)`.
- The theorem does not prove `[Ctop;C0]` is source-produced `C'^(S+1)`.
- It does not prove chart production, chart coverage or regularity, Jacobian
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariance, automatic Case 2 gap/tail transport, or printed-vector repair.

## Kill Conditions

- Do not replace actual-width exhaustion by prefix exhaustion or failed
  continuation alone.
- Do not treat this rewrite as construction of a new following matrix.
- Do not pass a terminal source model whose `b0` is definitionally
  `post.weight(J+1)` to a theorem expecting `terminalRelabelPost.weight(J+1)`;
  the equality is propositional, while the model type depends on `b0`.
