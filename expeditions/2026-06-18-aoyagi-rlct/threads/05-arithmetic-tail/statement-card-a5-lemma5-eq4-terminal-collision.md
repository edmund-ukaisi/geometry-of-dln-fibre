# Statement card - A5 Lemma 5 equation (4) terminal collision

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperNat_pred_eq_sub_lastWidth_of_selectedSum`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_terminalEndpoint_value_of_predBoundary`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_terminalEndpoint_zero_iff_lastWidth_of_predBoundary`

## Statement

Lean now records the endpoint arithmetic when Aoyagi Lemma 5 equation `(4)`'s
special boundary collides with the terminal selected endpoint.

If `p+1=a`, then the boundary

```text
C.point (p + (ell-a) + 1) - 1
```

is `C.point ell - 1`.  Under Definition 3's selected-sum identity, a supplied
equation `(4)` branch certificate gives

```text
T(C.point ell - 1) = M - W_(ell+1) - p + 1.
```

Consequently this value is zero exactly when

```text
W_(ell+1) = M - p + 1.
```

## Proved

- The penultimate upper-chain value is `Htilde'_(ell-1)=M-W_(ell+1)` under the
  selected-sum identity.
- The supplied equation `(4)` branch value at the terminal-collision boundary.
- The exact compatibility condition for this supplied boundary value to be
  zero.

## Assumed

- A supplied equation `(4)` piecewise branch certificate, including
  `a<=ell` and `p+1<=a`.
- The terminal-collision equality `p+1=a`, which also gives `1<=a`.
- Definition 3's selected-sum identity.

## Cited

- None in Lean.  These are finite endpoint arithmetic and supplied-branch
  bookkeeping facts.

## Deferred

- Construction or existence of equation `(4)`'s displayed vector.
- Terminal `tilde t=0`.
- Source vector-to-chain correspondence, vector admissibility, Case 1(2) chart
  sequence, Lemma 5 order count, pole order, normal crossings, and RLCT
  extraction.

## Review

- Source/API audit: xhigh `Erdos`.
- Landed-patch review passed by xhigh `Hubble`:
  `review-lemma5-eq4-terminal-collision-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
