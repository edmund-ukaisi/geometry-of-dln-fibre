# Statement Card - A4 Case 2 Branchwise Successor Production Boundary

## Artifact

- `reproduction-case2-branchwise-successor-production-boundary-a4.md`

No Lean theorem is introduced in this slice.

## Claim

A future Case 2 source-production theorem must be branchwise under the
standing displayed-pivot hypotheses `1 <= S`, `S <= L`, and
`J+1 <= prefixMinNat n (S+1)`.  The Lean/A4 branch contract refines Aoyagi's
printed branch sentence: the continuing payload uses the stronger
nonempty-next-center condition `J+2 <= prefixMinNat n (S+1)`, while the
stopped payloads expose actual-width and row-exhausted hypotheses that are not
asserted to be mutually exclusive.  These branches have different domains and
different row meanings, so they cannot be collapsed into a single unqualified
statement that "`C'^(S+1)` is produced".

## Proved

The reproduction identifies which parts are already finite Lean data:
`Q/P` algebra, `Q^-1 C` row formulas, lower-row products, source-current stack
presentation, actual-width original-row collapse, row-exhausted transported
prefix rows, and current-center principalization.

## Assumed

The present Lean boundary still assumes supplied chart-family data, corrected
post-data interfaces, source following/suffix factors, and terminal following
matrices or bridge row equations where applicable.

## Deferred

Source production of the full successor object `C'^(S+1)`, successor chart
families, coverage, transition regularity, source production of suffixes and
following products, coordinate derivation of corrected post-data, Jacobian
arithmetic, normal crossings, pole order, termination, and RLCT.

## Cited

None at this A4 boundary.

## Verification

This is a reproduction/contract slice.  Xhigh review required three
source-fidelity clarifications; those fixes are applied.  See
`review-case2-branchwise-successor-production-boundary-a4.md`.
