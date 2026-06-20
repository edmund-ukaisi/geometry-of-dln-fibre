# Pen-and-paper reproduction - Lemma 4 binary prefix delta

Status: checked finite bridge.  This is only a conditional arithmetic bridge
for Aoyagi Lemma 4's two-value increment hypothesis.  It does not prove that
source exponent vectors, same-coordinate bounds, or admissible chains provide
binary prefix deltas.

## Index Convention

Lean uses zero-based selected widths and chain coordinates:

```text
m : Fin (ell+1) -> Z,
H : Fin (ell+1) -> Z,
P(j) = sum_{i=0}^j m_i,
F_j = H_j - H_(j+1) + m_(j+1),       j : Fin ell.
```

This `F_j` is the source `F_(j+1)`.  The source's special first increment is
handled elsewhere by the convention `H_0=m_0=M(S_1)`.

Define the prefix-delta normal form

```text
D_j = P(j) - H_j - j*(M-1),          j = 0,...,ell.
```

Since Lean's `P(j)` is source `P_(j+1)`, this is the source-facing expression

```text
D_j = P_(j+1) - H_j - j*(M-1).
```

Do not shift the prefix again.

## Derivation

For `j : Fin ell`,

```text
D_(j+1) - D_j
  = [P(j+1) - H_(j+1) - (j+1)*(M-1)]
    - [P(j) - H_j - j*(M-1)]
  = [P(j+1)-P(j)] + H_j - H_(j+1) - (M-1).
```

The inclusive prefix rule gives

```text
P(j+1)-P(j) = m_(j+1).
```

Therefore

```text
D_(j+1) - D_j
  = m_(j+1) + H_j - H_(j+1) - (M-1)
  = F_j - (M-1),
```

or equivalently

```text
F_j = (M-1) + (D_(j+1)-D_j).
```

The orientation is essential: the useful delta is `D_(j+1)-D_j`, not
`D_j-D_(j+1)`.

## Binary Delta Consequence

If every successive delta is binary,

```text
D_(j+1)-D_j in {0,1},
```

then

```text
F_j in {M-1,M}.
```

This supplies exactly the two-value increment hypothesis needed by the
existing Lemma 4 finite count wrappers.

## Endpoint Bookkeeping

The identity itself does not need `H_0=m_0`, `H_ell=0`, the selected-width sum,
or `a <= ell`.

Those hypotheses are needed only when feeding the two-value result into the
count theorem.  Under `H_0=m_0`, one has `D_0=0`.  Under additionally
`H_ell=0` and

```text
sum m = ell*(M-1)+a,
```

one has `D_ell=a`.

## Lean Boundary

Safe Lean targets:

- define `aoyagiLemma4IncrementPrefix`;
- prove `aoyagiLemma4F_eq_pred_add_incrementPrefixDelta`;
- prove binary prefix deltas imply the two-value increment hypothesis;
- feed binary prefix deltas into existing terminal-`H` and same-coordinate
  `Htilde`-chain-bound count wrappers.

Deferred:

- source exponent vectors imply binary prefix deltas;
- same-coordinate `Htilde <= H <= Htilde'` bounds imply binary prefix deltas;
- vector coordinates match chain coordinates;
- source feasibility/admissibility of the intermediate chain;
- Lemma 5 chart-family coverage/order count;
- pole order, normal crossings, and RLCT extraction.

## Independent Check

Xhigh checker `Einstein the 5th` independently derived the identity with the
same orientation and confirmed the boundary cautions above.
