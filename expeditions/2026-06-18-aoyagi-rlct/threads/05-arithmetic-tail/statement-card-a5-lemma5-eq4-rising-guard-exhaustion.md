# Statement Card - A5 Lemma 5 Eq4 Rising-Guard Exhaustion

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_risingGuardFailure_iff_eq_a`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_selectedIndexGuardFailure_iff_eq_a`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_risingGuardFailure_eq_a_and_no_piecewiseSourceVector`

## Claim

In the rising-side range `p<=a`, failure of the repaired Eq4 guard `p+1<=a`
is exactly the boundary `p=a`.  In raw selected-index form, under `a<=ell`,
failure of `p+(ell-a)+2<=ell+1` is also exactly `p=a`.

## Inputs

- Pure guard exhaustion: `p<=a`.
- Raw selected-index form: `a<=ell` and `p<=a`.
- Eq4 certificate obstruction wrapper: `p<=a` and `not (p+1<=a)`.

## Proves

The pure theorem proves:

```text
not (p+1<=a) <-> p=a.
```

The raw selected-index theorem proves:

```text
not (p+(ell-a)+2<=ell+1) <-> p=a.
```

The Eq4 wrapper proves:

```text
p=a
and
not AoyagiLemma5Eq4PiecewiseSourceVector(...)
```

from guard failure in the rising-side range.

## Does Not Prove

- `not Eq4PiecewiseSourceVector(...) <-> p=a`.
- Eq4 source-vector construction or branch existence.
- Eq4 lower-endpoint coverage at `p=a`.
- Source-label legality, introduced-label status, injection, back-to-label
  coverage, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(4)`, PDF p. 27.  The source issue is the printed
condition `j0<=a` together with the displayed cutoff `S_(j0+ell-a+2)-1`; the
Lean repair records the selected-index guard as `p+1<=a`.
