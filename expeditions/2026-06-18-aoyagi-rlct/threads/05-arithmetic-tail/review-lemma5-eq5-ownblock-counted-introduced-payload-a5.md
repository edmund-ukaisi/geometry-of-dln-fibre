# Review - Lemma 5 Eq5 own-block counted/introduced payload

Status: reviewed/formalised.

Reviewer: Popper, xhigh effort.

## Scope

This slice proves a one-branch conditional payload for a supplied equation
`(5)` own-block branch:

```text
aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound
```

It combines counted-datum membership with introduced-label membership under
explicit source-label and nonbase hypotheses.

## Checks

Focused Lean check passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean
```

The controller also ran:

```text
lake build DLNFibre.DLN.Aoyagi.Lemma5Eq5CountDatumBridge
lake env lean DLNFibre.lean
lake build DLNFibre
git diff --check
scripts/sorries
```

## Findings

No formal findings.

The theorem is scoped as a one-branch conditional payload.  It assumes a
supplied Eq `(5)` piecewise certificate, one block membership `C.block p S`,
source-label legality hypotheses, the label formula, and explicit nonbase
status.  The conclusion is only counted-datum membership, `T S = k - 1`, and
membership of `(S,k)` in `introducedLabelFinset`.

The proof uses the expected ingredients:

- `hp_pos` and `hS.1` to prove `p ∈ Finset.Icc 1 (ell - 1)`;
- the existing source-label/interval wrapper for `T S = k-1` and
  introduced-label membership;
- `aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat` with interval
  membership and the supplied nonbase inequality.

No hidden classifier, no-extra, back-to-label, injection, order-count, pole
order, normal-crossing, or RLCT claim was found.

The reproduction note is aligned with Aoyagi p. 27 equation `(5)`: it records
the strict-offset own-block value and label relation, and its nonclaims match
the theorem statement.

## Residual Boundary

This review covers only the conditional bridge.  It does not validate
construction or exhaustiveness of the supplied Eq `(5)` family, nonbase
production, global Lemma 5 counting, normal crossings, or RLCT extraction.
