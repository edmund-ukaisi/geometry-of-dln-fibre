# Review - A4 Case 2 transition-generated Q/P source-substitution package

Date: 2026-06-24.

Reviewer: `Aquinas the 2nd`, xhigh-effort independent subagent.

Status: pass.  No blocking findings.

## Scope

Reviewed the uncommitted finite `Q/P` source-substitution package:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-case2-transition-generated-qp-source-substitution-a4.md`;
- `statement-card-a4-case2-transition-generated-qp-source-substitution.md`.

The review checked statement fidelity, denominator hypothesis, the exact
scope of the source-side rewrite, and overclaim risks.

## Findings

No blocking formalisation or mathematical issues were found.

The denominator hypothesis is correctly the source-normalized target
coordinate `x_q != 0`; no `u != 0` or `(u*x_q) != 0` hypothesis is introduced.

The source-side rewrite is limited to the substituted residual block.  The
theorem separately records

```text
Sub_q(targetU,targetResidual) = Sub_p(u,residual),
```

and the `Q/P` conjunct replaces only that factor.  The normalized block,
transported following factor, successor weights, and denominator-cleared
Schur formula remain target-pivot/target-data objects.

The docs and ledger carry the same boundary: no analytic regularity, coverage,
source production, normal crossings, pole order, or RLCT is claimed.

## Review Limitation

The reviewer could not independently extract Aoyagi PDF pp. 20-22 in the
container because `pdftotext`/`pdfinfo` and Python PDF libraries were
unavailable.  The review used only the Aoyagi expedition context already in
the repository and did not use the quiver paper.

## Gates

Passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/sorries
git diff --check 43a32951 --
```

The sorry audit reports:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Full `DLNFibre` build was not run by the reviewer.  The controller's
post-review verification additionally ran:

```text
lean/scripts/lb DLNFibre
```

## Minimal Repair

None required.
