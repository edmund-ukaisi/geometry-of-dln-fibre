# Reproduction - Lemma 5 Eq5 own-block common introduced domain

Status: reproduced; Lean checked; state-monotonicity adapter.

## Source Boundary

The Eq5 own-block payload introduces the branch label `(S,k)` at its local
state `(S,k)`.  Later classifier-facing structures often need membership in a
fixed later introduced-label domain.  This slice proves only the formal
monotonicity needed to move a label from its local state to an explicitly
supplied later/common state.

No terminal state, terminal source, or exhaustive branch coverage is inferred.

## Calculation

By definition,

```text
introducedLabel L n S J s k
```

means:

```text
actualWidthLabel L n s k
and
(s < S or (s = S and k <= J)).
```

Suppose the target state `(S',J')` is later in the lexicographic sense

```text
S < S' or (S = S' and J <= J').
```

Then an introduced label at `(S,J)` is introduced at `(S',J')`:

- if `s < S`, then either `s < S'` because `S < S'`, or `s < S'` after
  rewriting `S = S'`;
- if `s = S` and `k <= J`, then either `s < S'` because `S < S'`, or
  `s = S'` and `k <= J'` by transitivity.

This gives the finite-set subset

```text
introducedLabelFinset L n S J
  subset introducedLabelFinset L n S' J'.
```

For the Eq5 own-block payload, the local state is `(S,k)`, so the supplied
state comparison is

```text
S < Sfinal or (S = Sfinal and k <= Jfinal).
```

The existing one-branch counted/introduced payload gives

```text
some (p,T S) in aoyagiLemma5CountDatumSet
T S = k - 1
(S,k) in introducedLabelFinset L n S k.
```

The monotonicity subset lifts the last membership to

```text
(S,k) in introducedLabelFinset L n Sfinal Jfinal.
```

## Lean Targets

General introduced-label API:

```text
introducedLabel_mono_state
introducedLabelFinset_subset_of_state_le
```

Eq5 wrappers:

```text
aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_widthBound
aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_blockWidth
aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_leftEndpointMin
aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected
aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected_lt
```

## Kill Conditions

- Keep the target-state comparison explicit.
- Do not infer that the target state is terminal.
- Do not infer the nonbase inequality or Eq5 branch construction.
- Do not replace local payload hypotheses by classifier/no-extra coverage.

## Nonclaims

No terminal introduced-domain construction, no terminal source realisation, no
Eq5 branch construction, no classifier injectivity, no back-to-label map, no
no-extra terminal-minimum coverage, no Lemma 5 order count, no pole order, no
normal crossings, and no RLCT extraction is proved here.
