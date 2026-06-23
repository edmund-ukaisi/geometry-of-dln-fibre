# Audit - Case 2 Branchwise Successor Production Recheck

Date: 2026-06-23.

Reviewers: Galileo, Wegener, Epicurus; all xhigh effort, read-only.

Status: independent branch re-audit.  No Lean theorem is claimed in this
slice.

## Verdict

Aoyagi PDF pp. 19-22 source-proves the local displayed Case 2 algebra: the
pivot chart at `(J+1,J+1)`, the `b'_r = u_{S,J+1} b_r` convention, regular
`Q` and `P`, the transported following factor
`C'_J^(S+1) = Q^-1 C_J^(S+1)`, the cleared `D'''_J` block, and the displayed
product identity.  It does not source-prove a successor chart family,
source-production of the full next `C'^(S+1)`, suffix production, chart
coverage, transition regularity, coordinate derivation of corrected post-data,
Jacobian/volume data, normal crossings, pole order, termination, or RLCT.

The existing Lean boundary is therefore correctly conservative: finite
formula-level adapters and consumers of a supplied
`SourceProductionObligation` are safe; any theorem named as source production
from the displayed Case 2 chart is not source-faithful at the present boundary.

## Branch Checks

### Continuing branch

The continuing branch needs the stronger guard

```text
J+2 <= prefixMinNat n (S+1),
```

not only Aoyagi's printed non-strict continuation sentence.  This guard is the
nonempty-next-center requirement after deleting the displayed pivot row and
column.  The source supports the formula-level successor following factor:
replace only row `J+1` of the old source following factor by the transported
top row of `Q^-1 C`, and leave the other rows unchanged.

Safe Lean payloads are the existing finite adapters, especially
`continuingWeightedSuccFollowingFrontierPayload_of_sourceFollowing` and
`SourceProductionObligation.continuing_sourceCurrentStack_suppliedCsucc`.
These consume formula equalities or supplied obligations.  They do not
construct `Csucc`, the full source-produced `C'^(S+1)`, successor charts, or
suffixes.

### Actual-width stopped branch

Under

```text
n(S+1) = J+1,
```

the post-pivot next-width row set is empty, so the correction sum in the
pivot row of `Q^-1 C` is empty.  In this branch the formula-level successor
following factor collapses rowwise to the old source following factor, and the
terminal rows can be written as original rows `1,...,J+1`.

Safe Lean payloads are existing finite original-row and supplied-`Cterm`
wrappers, including
`SourceProductionObligation.actualWidth_Cterm_eq_originalRows_Csucc` and
`SourceProductionObligation.actualWidth_frontier_suppliedCterm`.  They do not
produce the terminal following product from chart data, and the suffix remains
supplied.

### Row-exhausted stopped branch

Under

```text
prefixMinNat n S = J+1,
```

the terminal prefix stops at row `J+1`, but the actual next width `n(S+1)` may
still be larger.  In the wide-next subcase, the pivot row is

```text
C(J+1,a) + sum_{r=J+2}^{n(S+1)} d'_(J+1,r) C(r,a),
```

so it is transported, not the old source row.  It can be called an original
row only after replacing the old source following factor by the formula-level
successor factor `Csucc`.

Safe Lean payloads are transported-prefix and supplied-`Cterm` rewrites,
including `SourceProductionObligation.rowExhausted_Cterm_eq_originalRows_Csucc`
and `SourceProductionObligation.rowExhausted_frontier_suppliedCtermPrefix`.
They do not construct `Cterm`, `Csucc`, source suffixes, or chart data.

## Controller Action

Do not pursue an A4 theorem saying that Aoyagi pp. 19-22 source-produce the
successor following object.  The safe A4 finite target set has already been
covered by existing supplied-obligation consumers.  Further A4 progress must
either build an independent selected-entry atlas/transition construction or
remain explicitly below the source-production boundary.

