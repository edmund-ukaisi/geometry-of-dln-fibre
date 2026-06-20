# Statement card - A5 Lemma 5 equation (4) guard arithmetic

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcess_eq_self_of_le_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_selectedIndexGuard_iff`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerNat_add_one_labelBounds_iff_prefixCrossing`

## Statement

Lean now records three guard facts for Aoyagi Lemma 5 equation `(4)`.

First, under

```text
p <= a,
p <= ell-a,
```

the interval excess at `p` is exactly `p`.

Second, the displayed selected-index cutoff `S_(p+ell-a+2)` lies inside the
source list `S_1,...,S_(ell+1)` exactly when

```text
p+1 <= a.
```

Third, under `p<=a`, the label bounds for `k=Htilde_p+1` are equivalent to
the prefix-crossing inequalities

```text
P_p < pM <= P_(p+1).
```

The Lean statement uses the zero-based inclusive prefix form
`P_(p+1) - W_(p+1) + 1 <= pM <= P_(p+1)`.

## Proved

- The interval-excess specialization used by the own-coordinate theorem.
- The exact selected-index guard for the equation `(4)` tail cutoff.
- The exact arithmetic reformulation of `1 <= Htilde_p+1 <= W_(p+1)`.

## Assumed

- For the interval-excess specialization: `a<=ell`, `p<=a`, and `p<=ell-a`.
- For the selected-index guard: `a<=ell`.
- For the label-bounds equivalence: `p<=a`.

## Cited

- None in Lean.  These are finite arithmetic consequences of the displayed
  Htilde definitions and Definition 3's selected-index range.

## Deferred

- Full equations `(3)` and `(4)` displayed-family realisation.
- Legal-label bounds from Definition 3 alone.
- `tilde t=0`.
- Source vector-to-chain correspondence and vector admissibility.
- Lemma 5 chart-family coverage/order count, pole order, normal crossings, and
  RLCT extraction.

## Review

- Source-convention scout: xhigh `Gauss`.
- Lean/API scout: xhigh `Dalton`.
- Pen-and-paper arithmetic scout: xhigh `Planck`.
- Landed-patch review passed by xhigh `Galileo`:
  `review-lemma5-eq4-guard-arithmetic-a5.md`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.Lemma5IntervalArithmetic`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre.lean`
- `lake build DLNFibre`
- `git diff --check`
- `./lean/scripts/sorries`
