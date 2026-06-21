# Reproduction - Lemma 4 prefix-profile computations

Status: reproduced; Lean checked.

## Source

Aoyagi Lemma 4 uses the increments

```text
F_j = H_{j-1} - H_j + m_j.
```

The existing Lean development packages this through a prefix normal form
`aoyagiLemma4IncrementPrefix`.  The successive difference of this prefix is
the additive correction from `M-1` to `F_j`.

This slice records two generic computations for later Eq5 endpoint-profile
work.

## Calculation

The prefix normal form is

```text
D_j = P_j - H_j - j*(M-1),
```

where `P_j` is the selected-width prefix sum.  The upper Htilde chain is

```text
Htilde'_j = P_j - (j*(M-1) + upperHighCount_j).
```

Therefore, if

```text
H_j = Htilde'_j - r,
```

then

```text
D_j
  = P_j - (Htilde'_j - r) - j*(M-1)
  = upperHighCount_j + r.
```

The lower Htilde chain is

```text
Htilde_j = P_j - (j*(M-1) + lowerHighCount_j).
```

Therefore, if

```text
H_j = Htilde_j,
```

then

```text
D_j = lowerHighCount_j.
```

The initial and terminal profile facts were already present in Lean:

```text
aoyagiLemma4IncrementPrefix_zero_of_H0
aoyagiLemma4IncrementPrefix_last_eq_a_of_terminalH
```

This slice adds only the upper-offset and lower-chain coordinate computations.

## Lean Targets

```text
aoyagiLemma4IncrementPrefix_eq_upperHighCount_add_of_eq_upperNat_sub
aoyagiLemma4IncrementPrefix_eq_lowerHighCount_of_eq_lowerNat
```

## Use

For a supplied Eq5 endpoint chain, these lemmas turn displayed endpoint values
of the form `Htilde'_b - r` or `Htilde_b` into explicit prefix-profile values.
That is a prerequisite for a later binary-delta proof, but it is not itself
the binary-delta theorem.

## Nonclaims

- No Eq5 endpoint profile is proved.
- No binary prefix-delta theorem is proved.
- No Eq5 vector construction, endpoint realisation, source-label legality,
  classifier, order count, pole order, normal crossings, or RLCT extraction is
  proved.
