# Review - Lemma 5 Eq5 Post-p Lower Obstruction

Reviewer: Pascal (xhigh read-only subagent).

Status: pass; no blocking findings and no high/medium/low severity findings.

## Scope Reviewed

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `reproduction-lemma5-eq5-postp-lower-obstruction-a5.md`
- `statement-card-a5-lemma5-eq5-postp-lower-obstruction.md`
- Expedition ledger updates in `priorities.md`, `thread.md`, `synthesis.md`,
  `theorem-ledger.md`, and `claims.md`.

## Findings

No findings.

## Audit Notes

The theorem
`aoyagiLemma5Eq5_postP_belowLower_of_intervalExcess_lt_offset` is
mathematically and type-theoretically sensible.  The proof uses the supplied
`hT.postP` branch value, the block-index bound from `C.block b S`, and the
existing `aoyagiHtildeUpper_sub_lower_eq_intervalExcess` identity.  The
reviewer found no hidden source-construction or source-legality dependency.

The natural-to-integer offset handling is valid: the proof has
`hp_le_b : p <= b` before proving

```text
((alpha + b - p : Nat) : Int) = alpha + b - p.
```

Thus the natural subtraction is not used past its truncation boundary.

The documentation and ledgers stay within the obstruction-only scope.  They
explicitly avoid displayed-vector construction, global Eq5 failure, corrected
Eq5 construction, source-label legality, terminality, chart/classifier
coverage, pole order, normal crossings, and RLCT extraction.

## Verification

The reviewer independently ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

from the `lean/` project root, and it passed.

## Residual Risk

This was a focused slice review, not a full project build or a fresh source-PDF
transcription audit.  The theorem is correct relative to the existing supplied
Eq5 `postP` certificate definition.
