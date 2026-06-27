# Review - A2 Retained-Passive Ctop Source-Staged Successor Shear

Date: 2026-06-27.

Reviewer: Kant, xhigh read-only explorer.

## Verdict

PASS.

## Boundary Check

The Lean theorem
`Ctop_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
only replaces the successor `F2` derivative and the left-multiplied successor
lower-left derivative in the existing `Ctop` bridge.  It leaves `dTailInv` as
the explicit Frechet derivative term.

The proof starts from
`Ctop_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
rewrites the successor `F2` term with
`fderiv_retainedPassive_toCoordinateData_F2_succ_apply`, and rewrites the
multiplied lower-left term with
`retainedPassive_F2_succ_mul_fderiv_solvedA3_eq_sourceStagedSuccessorA3`.
It does not introduce a tail-inverse product formula or a determinant,
measure, normal-crossing, pole-order, or RLCT claim.

## Endpoint Check

The endpoint handling is sound.  The staged successor families use terminal
zero conventions, and the lower-left derivative is identified only after
multiplication by the terminal extended `F2` slot.  The `M = 0` case is covered
by the same all-edge lemmas.

## Documentation Check

The reproduction and statement card are appropriately narrow.  They keep
`d(Tail^{-1})` unexpanded and list the nonclaims, including no determinant
equality, measure transport, normal crossings, pole order, or RLCT statement.

## Verification

The reviewer ran a focused Lean file check successfully.  The controller ran
the focused module build, full `DLNFibre` build, sorry scan, diff check, and
axiom audit separately.
