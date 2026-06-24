# Review - A6 Definition 3 `ell=1` ceiling-data simplification

Date: 2026-06-24.

Reviewer: xhigh independent reviewer `Dalton the 3rd`.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`;
- `reproduction-definition3-ell-one-ceil-data-simplification-a6.md`;
- `statement-card-a6-definition3-ell-one-ceil-data-simplification.md`.

Review questions:

- `aParam=1` from the source fields;
- selected-sum and ceiling-width orientation;
- order and lambda simplifications for arbitrary `AoyagiDefinition3CeilData 1 m`;
- pair-form nonclaim boundaries;
- whether the slice is useful finite arithmetic rather than final-socket
  wrapper churn.

## Findings

No findings.

The `ell=1` arithmetic is sound.  The equality `aParam=1` follows directly
from `aParam_pos : 0 < aParam` and `aParam_le : aParam <= ell` with
`ell=1`.  The selected-sum identity becomes

```text
sum_j m_j = 1 * (ceilWidth - 1) + 1 = ceilWidth.
```

Both rewrite orientations are named separately.  The order formula reduces
from `aParam * (ell - aParam) + 1`, and both lambda correction terms vanish at
`ell=aParam=1`.

The selected-pair lambda lemma assumes only `m 0 = u` and `m 1 = v`; it does
not construct selected cutpoints, choose a branch, or claim branch
independence.

The reproduction and statement card accurately frame the slice as finite
arithmetic for supplied `ell=1` ceiling data, not final-socket wrapper churn or
analytic/RLCT work.

## Verification

The reviewer did not rerun Lean because the assignment was read-only.  The
controller focused elaboration had already passed.

## Residual Boundary

No source-data or selected-cutpoint existence is constructed.  No final socket,
Eq5 payload, chart, pole-order theorem, normal-crossing theorem, or RLCT
extraction is claimed.
