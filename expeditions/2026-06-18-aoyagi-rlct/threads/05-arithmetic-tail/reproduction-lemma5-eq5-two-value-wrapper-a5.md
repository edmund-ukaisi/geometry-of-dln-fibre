# Reproduction - Lemma 5 Eq5 two-value wrappers

Status: reproduced; Lean checked.

## Source

The previous slice proved that a supplied equation `(5)` endpoint chain under
terminal room has binary Lemma 4 increment-prefix deltas.  This slice is the
formal handoff from that binary-delta fact to existing Lemma 4 wrappers.

## Calculation

For a chain `H`, Lemma 4 already proves

```text
F_j = (M-1) + Delta_j
```

where `Delta_j` is `aoyagiLemma4IncrementPrefixDelta ell M m H j`.  Therefore
if every `Delta_j` is `0` or `1`, then every `F_j` is `M-1` or `M`.

With the source endpoint `H_0=m_0`, terminal endpoint `H_ell=0`, and selected
sum, the existing finite count wrappers give:

```text
#{j | F_j = M}     = a
#{j | F_j = M - 1} = ell - a
```

The existing binary-prefix count wrapper also gives:

```text
#{j | Delta_j = 1} = a
#{j | Delta_j = 0} = ell - a.
```

Finally, the existing binary-prefix bound wrapper gives

```text
Htilde_lower <= H <= Htilde_upper.
```

## Lean Targets

```text
aoyagiLemma5Eq5_endpointChain_F_twoValue_of_terminalRoom
aoyagiLemma5Eq5_endpointChain_twoValueCount_of_terminalRoom
aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefix_count_eq_of_terminalRoom
aoyagiLemma5Eq5_endpointChain_HtildeChainBounds_of_terminalRoom
```

## Use

These are API adapters: downstream code can consume Eq5 terminal-room endpoint
chains through the standard Lemma 4 two-value, count, and Htilde-bound
interfaces without restating the adjacent case split.

## Nonclaims

- No Eq5 vector is constructed.
- No endpoint-chain realisation or terminality is proved.
- No counted-datum membership, classifier, injection, back-to-label coverage,
  order count, pole order, normal crossings, or RLCT extraction is proved.
