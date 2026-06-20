# Review - Lemma 5 equation (4) source-guarded piecewise certificate

Reviewer: xhigh `Lovelace`.

Scope:

- `AoyagiLemma5Eq4PiecewiseSourceVector`;
- `aoyagiLemma5Eq4_boundaryIndex_le_ell_of_piecewiseSourceVector`;
- theorem interfaces using the supplied equation `(4)` certificate;
- reproduction, statement-card, ledger, synthesis, and priority updates.

## Findings

None blocking.

## Verdict

Pass.

The equation `(4)` supplied piecewise certificate should carry exactly the
source-boundary guard fields

```text
a<=ell,
p+1<=a.
```

They are sufficient for the record-level source-index issue: the boundary
`point C (p+(ell-a)+1)-1` denotes Aoyagi's selected source
`S_(p+ell-a+2)-1` only when `p+(ell-a)+1<=ell`, and this follows from
`a<=ell` and `p+1<=a`.

Do not add `1<=p` as a record field.  It is needed only to use the prefix
branch at the own coordinate `S_(p+1)-1`; it is not a source-boundary guard
for the displayed equation `(4)` cutoff.  The own-coordinate theorem should
keep `1<=p` and `p<=ell-a` theorem-local.

Theorems that already assume a supplied equation `(4)` certificate should use
the new fields rather than duplicating `a<=ell` and `p+1<=a`.  Arithmetic-only
theorems independent of the supplied certificate should keep their explicit
guard hypotheses.

## Source-Fidelity Risk

This is a repaired API, not the literal printed guard.  Aoyagi prints only
`j0<=a`, but the displayed cutoff uses `S_(j0+ell-a+2)`.  At `j0=a`, that asks
for `S_(ell+2)` unless an extra convention is supplied.  The Lean API should
therefore continue to document `p+1<=a` as a source-index repair and should
not fold `p<=ell-a`, terminal `tilde t=0`, or full displayed-family
realisation into this record.

## Commands Run

- `git diff --check`

Lean verification was run by the controller after landing the patch.
