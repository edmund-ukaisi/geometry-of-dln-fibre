# Reproduction - Lemma 5 Eq4 lower endpoint and Eq5 erase-upper set

Status: checked finite-set/API wrapper.

This note connects equation `(4)`'s supplied own-coordinate value with the
finite Eq5 lower-plus-offset set equality.  It does not construct any displayed
source vector.

## Source

Aoyagi Lemma 5, PDF pp. 26-27:

- Eq. `(4)` has own coordinate `s = S_(j0+1)-1` and label
  `k = Htilde_j0 + 1`.
- Eq. `(5)` has strict offsets
  `alpha = Htilde'_j0 + 1 - k`, with `j0 > alpha`.
- The same-coordinate interval is
  `{H : Htilde_j0 <= H <= Htilde'_j0}`.

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

Then the already-proved finite Eq5 equality is:

```text
insert Htilde_p Eq5OffsetValueSet_p
  = HtildeIntervalValueSet_p.erase Htilde'_p.
```

For a supplied Eq4 piecewise certificate, the repaired Eq4 own-coordinate
theorem gives:

```text
T(C.point p - 1) = Htilde_p.
```

Substituting this equality into the finite Eq5 equality yields:

```text
insert (T(C.point p - 1)) Eq5OffsetValueSet_p
  = HtildeIntervalValueSet_p.erase Htilde'_p.
```

This says only that the supplied Eq4 own-coordinate branch supplies the lower
endpoint in the already-counted lower-plus-strict-offset finite set.  It leaves
the upper endpoint erased.

## Lean Target

```text
aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_le_min
```

## Kill Conditions

- Do not drop the rising-region hypotheses `1<=p`, `p<=a`, `p<=ell-a`.
- Do not drop the repaired Eq4/source-selected hypotheses needed by the
  existing Eq4 own-coordinate theorem.
- Do not claim the upper endpoint is realised.
- Do not claim construction of the displayed source vectors, terminal
  `tilde t=0`, vector admissibility, chart coverage, Lemma 5 order count,
  normal crossings, or RLCT extraction.
