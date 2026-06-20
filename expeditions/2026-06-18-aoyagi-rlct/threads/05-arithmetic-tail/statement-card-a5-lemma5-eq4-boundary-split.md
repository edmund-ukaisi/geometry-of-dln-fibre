# Statement card - A5 Lemma 5 equation (4) boundary split

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryIndex_lt_ell_iff`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryIndex_eq_ell_iff`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryEndpoint_mem_block_of_strictGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryEndpoint_mem_selectedSpan_of_strictGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryEndpoint_eq_terminal_of_predBoundary`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryEndpoint_not_block_of_predBoundary`

## Statement

Lean now records the strict-versus-terminal split for Aoyagi Lemma 5 equation
`(4)`'s supplied boundary

```text
point C (p+(ell-a)+1)-1.
```

Under `a<=ell`, the boundary index is strictly before the terminal selected
index exactly when `p+1<a`, and it is terminal exactly when `p+1=a`.  For a
supplied equation `(4)` certificate, the strict case puts the boundary point in
the selected block `p+(ell-a)+1` and hence inside the half-open selected span.
The terminal case identifies it with `point C ell - 1`, which is not in any
half-open selected block.

## Proved

- Pure Nat arithmetic for the strict and terminal boundary-index cases.
- Strict boundary point membership in the next selected block.
- Strict boundary point membership in the half-open selected span.
- Terminal boundary equality with the terminal selected endpoint.
- Terminal boundary nonmembership in all half-open selected blocks.

## Assumed

- For the arithmetic iff lemmas: `a<=ell`.
- For the source-boundary endpoint facts: selected cutpoints and a supplied
  equation `(4)` certificate carrying `a<=ell` and `p+1<=a`.
- Strict case: `p+1<a`.
- Terminal case: `p+1=a`.

## Cited

- None in Lean.  This is finite source-index and half-open block bookkeeping.

## Deferred

- Construction or existence of equation `(4)`'s displayed vector.
- Terminal `tilde t=0`.
- Selected-span classification at the terminal endpoint.
- Source vector-to-chain correspondence, vector admissibility, Case 1(2) chart
  sequence, Lemma 5 order count, pole order, normal crossings, and RLCT
  extraction.

## Review

- Source/API review passed by xhigh `Cicero`:
  `review-lemma5-eq4-boundary-split-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5IntervalArithmetic`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector`
- `lake build DLNFibre`
- `git diff --check`
- `./lean/scripts/sorries`
