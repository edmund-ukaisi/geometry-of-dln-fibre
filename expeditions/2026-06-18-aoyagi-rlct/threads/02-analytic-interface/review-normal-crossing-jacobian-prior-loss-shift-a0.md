# Review - Normal-crossing Jacobian-prior loss shift

Date: 2026-06-23.

Reviewer: xhigh reviewer `Banach`.

## Verdict

Pass, with a verification caveat.

## Findings

No blocking findings.

## Scope Check

The reviewer checked that `jacobianPriorLossShift` is a finite operation on
`AoyagiNormalCrossingExponentData`: it leaves `k` fixed and replaces `h` by
`h + m*k`.  The Lean and documentation disclaim chart construction, regular
coordinates, normal crossings, and RLCT additivity.

The active-coordinate guard is present on
`ratioAt_jacobianPriorLossShift_of_mem_activePairs`.  This is necessary because
`ratioAt` is totalized when `k = 0`.

The minimum and order preservation theorems are finite `Finset.min'`/`max'`
arithmetic using the active ratio shift and chart-count equality.  They do not
claim analytic regular-variable additivity.

## Source-Fidelity Check

The reproduction uses Aoyagi PDF pp. 5-6 for the finite normal-crossing formula
and p. 13 only as motivation for the regular-variable count.  The reviewer
accepted the documentation boundary: the slice does not prove analytic
regular-variable production, chart coverage, Jacobian/volume-form computation,
normal crossings, pole order, or RLCT extraction.

## Verification Caveat

The reviewer did not complete a Lean check in their spawned checkout because
the fresh VM lacked warm build/cache artifacts.  `lake env lean
DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean` failed before elaboration
with an `unknown module prefix` issue, and `lake build
DLNFibre.DLN.Aoyagi.NormalCrossingInterface` began rebuilding dependencies.

Controller verification is recorded in the statement card after the closeout
builds.
