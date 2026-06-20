# Pen-and-paper reproduction - Lemma 4 prefix-delta endpoint count

Status: checked finite bridge.  This extends the binary prefix-delta interface
by naming endpoint values and counting binary deltas.  It does not prove that
source exponent vectors or same-coordinate chain bounds provide binary deltas.

## Setup

Use zero-based selected widths and chain coordinates:

```text
m : Fin (ell+1) -> Z,
H : Fin (ell+1) -> Z,
P(j) = sum_{i=0}^j m_i,
D_j = P(j) - H_j - j*(M-1).
```

There are `ell` successive deltas

```text
Delta_j = D_(j+1)-D_j,       j=0,...,ell-1.
```

The orientation is `D_(j+1)-D_j`.

## Endpoint Values

If the source convention `H_0=m_0` holds, then

```text
D_0 = P(0)-H_0-0*(M-1)
    = m_0-H_0
    = 0.
```

If the terminal condition and selected-width sum hold,

```text
H_ell = 0,
sum_i m_i = ell*(M-1)+a,
```

then

```text
D_ell
  = P(ell)-H_ell-ell*(M-1)
  = (ell*(M-1)+a)-0-ell*(M-1)
  = a.
```

No separate `a <= ell` hypothesis is needed for this terminal endpoint
calculation.

## Telescoping

The finite sum of successive deltas telescopes:

```text
sum_{j=0}^{ell-1} Delta_j
  = sum_{j=0}^{ell-1} (D_(j+1)-D_j)
  = D_ell-D_0.
```

Combining with the endpoint values gives

```text
sum_j Delta_j = a.
```

## Binary Delta Count

If each delta is binary,

```text
Delta_j in {0,1},
```

then the finite two-step count lemma with low value `0` applies to the family
`Delta`.  Since the sum is `a`,

```text
#{j | Delta_j=1} = a,
#{j | Delta_j=0} = ell-a.
```

The same result can be stated with same-coordinate `Htilde`-chain bounds
instead of an explicit terminal condition, but only because those bounds
already give `H_ell=0`; the binary-delta hypothesis remains explicit.

## Deferred

- Source exponent vectors imply binary prefix deltas.
- Same-coordinate `Htilde <= H <= Htilde'` bounds imply binary prefix deltas.
- Source-defined vector-to-chain coordinate correspondence.
- Vector admissibility and correspondence to `lambda`.
- Lemma 5 chart-family admissibility, coverage, exclusions, and pole-order
  interpretation.
- Normal crossings and RLCT extraction.

## Independent Check

Xhigh checker `Linnaeus the 5th` independently verified the endpoint formulas,
the telescoping identity, the binary count, the indexing boundary, and the
absence of a source claim.
