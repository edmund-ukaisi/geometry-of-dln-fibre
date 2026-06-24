# Review - A2 chart-local suffix-state field continuity

Date: 2026-06-24.

Reviewer: Arendt the 3rd, xhigh independent checker.

Verdict: PASS.

## Scope

Reviewed:

```text
lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean
reproduction-a2-chart-local-suffix-state-field-continuity.md
statement-card-a2-chart-local-suffix-state-field-continuity.md
```

## Findings

No soundness findings.

The determinant-unit hypotheses are sufficient for both inverse uses.  The
inverse of `topLeft(M x0)` uses the recursive determinant-chart hypothesis.
The inverse of `(S x0).Ctop * topLeft(M x0)` uses `Matrix.det_mul` together
with the carried `Ctop.det` unit and the determinant-chart hypothesis before
applying matrix-inverse continuity.

The suffix induction correctly carries `IsUnit Ctop.det`: the terminal case
establishes it, the induction step destructures it and passes it into the
one-step theorem, and the proof rewrites through `suffixState_castSucc`.

The Lean statements are fieldwise continuity plus the basepoint `Ctop.det`
unit invariant.  They do not assert analytic regularity, exact-rank openness,
neighborhood persistence, normal crossings, pole order, or RLCT consequences.

## Reviewer Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/ChartTopology.lean
```

No files were edited by the reviewer.

## Controller Verification

The controller ran:

```text
LEAN_NUM_THREADS=1 lake env lean DLNFibre/DLN/Aoyagi/ChartTopology.lean
LEAN_NUM_THREADS=1 lake build DLNFibre.DLN.Aoyagi.ChartTopology
LEAN_NUM_THREADS=1 lake build DLNFibre
scripts/sorries
git diff --check
```

The intended `scripts/lb` route was not used because the sandbox rejects the
unsandboxed shared-lock write to `~/.lake-shared`; the local single-worker
build path passed.
