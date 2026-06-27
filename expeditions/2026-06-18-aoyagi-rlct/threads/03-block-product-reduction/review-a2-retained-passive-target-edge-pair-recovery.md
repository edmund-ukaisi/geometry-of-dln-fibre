# Review - A2 retained-passive target edge-pair recovery

Date: 2026-06-27.

Reviewer: xhigh read-only `Heisenberg`.

Status: PASS after documentation status repair.

## Finding

Initial review returned FAIL for documentation drift only:

- `statement-card-a2-retained-passive-target-edge-pair-recovery.md` said
  "implementation pending";
- `reproduction-a2-retained-passive-target-edge-pair-recovery.md` said
  "before Lean formalisation".

Both were stale after the Lean implementation landed.

## Lean Audit

The reviewer found no Lean fidelity issue.

- Terminal zero is used only at `Fin.last M`.
- Nonterminal branches use the recovered successor `F2` value.
- The dependent cast direction matches the existing source-staged successor
  convention using `(Fin.succ_castSucc p).symm`.
- The fderiv theorems prove only target-side `(F2,C)` recovery on actual
  derivative targets; they do not prove determinant equality or whole-tuple
  target normalization.
- The determinant-chart hypothesis
  `hz : z in topologyTupleDetChartSet` is exposed on the relevant theorem
  statements.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

and it passed.

Controller verification additionally ran:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

All passed.  Axiom audit for the new fderiv/recovery theorems reported only
`[propext, Classical.choice, Quot.sound]`.

## Nonclaims

This review does not certify a whole-tuple target-side normalization,
target-side determinant-one `LinearEquiv`, actual determinant equality,
measure transport, normal crossings, pole order, or RLCT.
