# Review - selected-entry analytic atlas/source-production frontier

Date: 2026-06-28.

Reviewer: xhigh `Popper the 2nd`.

Verdict: PASS.

## Scope

Reviewed:

- `reproduction-selected-entry-analytic-atlas-source-production-frontier-a4.md`;
- `statement-card-a4-selected-entry-analytic-atlas-source-production-frontier.md`;
- the corresponding entries in `priorities.md`, `synthesis.md`, `claims.md`,
  `theorem-ledger.md`, and `threads/04-blow-up-certificate/thread.md`.

Checked against Aoyagi PDF pp. 19-22 and the existing A4 guardrails:

- `audit-selected-entry-analytic-atlas-saturation-a4.md`;
- `statement-card-a4-selected-entry-analytic-atlas-boundary.md`;
- `audit-case2-source-production-pp19-22-insufficient-a4.md`.

## Findings

No source-fidelity or overclaim issue was found.

The new frontier note correctly limits Aoyagi pp. 19-22 to displayed Case 2
finite algebra and explicitly rejects promotion of the finite selected-entry
certificate to analytic-atlas data.

The guardrails are preserved:

- no Lean theorem is claimed;
- the forbidden constructor is mentioned only negatively;
- coverage, transition regularity, source production, analytic
  Jacobian/volume-form control, normal crossings, pole order, and RLCT are
  all kept as nonclaims.

The branch table is sound.  The continuing condition

```text
J+2 <= prefixMinNat n (S+1)
```

is the post-pivot next-center nonemptiness condition, while actual-width
stopped and row-exhausted stopped remain separate, noninterchangeable payloads.

## Required Edits

None.
