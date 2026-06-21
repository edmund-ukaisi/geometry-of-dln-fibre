# Reproduction - Lemma 5 Eq5 Offsets as Interval With Endpoints Erased

Status: checked finite-set/API wrapper.

This note isolates the strict equation `(5)` offset values in the rising
region.  It is pure finite-set bookkeeping and does not construct any displayed
source vector.

## Source

Aoyagi Lemma 5, PDF pp. 26-27:

- The same-coordinate interval is
  `{H : Htilde_j0 <= H <= Htilde'_j0}`.
- Equation `(5)` uses strict offsets
  `alpha = Htilde'_j0 + 1 - k`, with `1 <= alpha < j0`.
- In the rising region already formalised here, the interval excess at
  coordinate `p` equals `p`, so Eq5 offsets run through the interval values
  strictly between the upper endpoint and the lower endpoint.

The existing Lean development uses zero-based coordinate `p` for the paper's
`j0`.

## Reproduction

Assume the rising-region hypotheses:

```text
a <= ell,
1 <= p,
p <= a,
p <= ell-a.
```

Lean already proves:

```text
insert Htilde_p Eq5OffsetValueSet_p
  = HtildeIntervalValueSet_p.erase Htilde'_p.
```

Lean also proves:

```text
Htilde_p notin Eq5OffsetValueSet_p.
```

Erase `Htilde_p` from both sides of the first equality.  Because the lower
endpoint is not a strict Eq5 offset, erasing it from the left side removes only
the inserted lower endpoint:

```text
Eq5OffsetValueSet_p
  = (HtildeIntervalValueSet_p.erase Htilde'_p).erase Htilde_p.
```

Equivalently, the strict Eq5 offsets are exactly the same-coordinate interval
with both endpoints removed.

## Lean Target

```text
aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min
```

## Kill Conditions

- Do not drop the rising-region hypotheses.
- Do not claim Eq3 or Eq4 realises the erased upper endpoint.
- Do not claim construction of displayed source vectors, terminal
  `tilde t=0`, vector admissibility, chart coverage, Lemma 5 order count,
  normal crossings, or RLCT extraction.
