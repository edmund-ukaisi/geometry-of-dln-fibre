# Review - Lemma 5 Eq3 upper away from boundary

Date: 2026-06-21.

Reviewer: Maxwell, xhigh-effort read-only review.

Verdict: ACCEPT.

## Scope

Reviewed the Eq3 upper-component inventory and Eq5 non-rising coverage slice:

- `aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_ne_boundary`
- `aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_nonrising_ne_boundary`

The review checked the Lean proof, reproduction, statement card, and expedition
ledger/thread/synthesis updates.

## Findings

No blocking findings.

The Eq3 case split is sound.  The proof splits on `p <= ell-a`.  In the left
case it uses the existing Eq3 ordinary upper-component helper.  In the right
case, `not p <= ell-a` and `p != ell-a+1` imply `ell-a+1 < p`, so the
ordinary-tail helper applies.  The hypothesis `p < ell` is exactly the
terminal-endpoint exclusion needed for the selected-block left endpoint to lie
inside an ordinary half-open block.

The Eq5 wrapper is sound.  It assumes non-rising explicitly, derives
`aoyagiLemma5IntervalExcess ell a p <= p-1` from the existing non-rising excess
lemma, obtains the supplied upper endpoint from the Eq3 component-value
inventory, and applies the generic supplied-upper Eq5 erase-upper wrapper.

The notes avoid the listed overclaims.  The reproduction and statement card
keep the result as supplied component/finite-set bookkeeping and explicitly
exclude source-label legality, own-source-label status, all-coordinate endpoint
realisation, injection/back-to-label coverage, Lemma 5 order count, and RLCT
consequences.

The source-inventory table is accurate for the theorem's intended object: the
selected-block left endpoint `C.point p-1`.  The table header was tightened
after review so it cannot be read as a claim about every point of a selected
block.

Naming/API risk is low.  The `ne_boundary` name omits the terminal exclusion,
but the hypotheses include `p < ell`, and the docstrings and statement card
call out the terminal endpoint explicitly.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

from the Lean project root, and it passed.
