# Review - A2 Case 2 with-following endpoint Y injectivity

Date: 2026-07-02.

Reviewer: xhigh `Carver the 2nd`.

Status: PASS.  No findings and no required fixes.

## Scope

Reviewed Lean declarations:

```text
case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_injOn_pivotNonzero
measurableSet_case2PassiveThetaWithFollowingFactorEndpointSectorSet_of_subset_pivotNonzero
```

Reviewed files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaCFieldReadout.lean
threads/03-block-product-reduction/reproduction-a2-case2-with-following-endpoint-y-injectivity.md
threads/03-block-product-reduction/statement-card-a2-case2-with-following-endpoint-y-injectivity.md
```

## Verdict

The Lean statements match the reproduced math.  The injectivity theorem is
exactly endpoint-coordinate injectivity on the selected-pivot-nonzero locus.
The measurable-image theorem is exactly for `Y '' Ω`, expressed through the
endpoint sector set, under the standard Lusin-Souslin source/target hypotheses.

The proof uses the active readout theorem, selected-entry chart injectivity off
the pivot hyperplane, and product extensionality.  It does not claim Haar
transport, Jacobians, normal crossings, pole order, RLCT extraction, or coverage
beyond actual images.

The reproduction and statement card are consistent with the formal statements
and nonclaims.

## Reviewer Verification

The reviewer ran:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaCFieldReadout.lean
```

from `lean/`; it passed.  The reviewer also checked the touched Lean file for
`sorry`, `axiom`, `native_decide`, and `#exit`, and ran `git diff --check`;
both checks were clean.
