# Review - Lemma 5 equation (3) terminal obstruction

Reviewer: xhigh `Boyle`.

Scope:

- `aoyagiLemma5Eq3_terminalEndpoint_one_of_one`;
- reproduction and statement-card updates;
- thread, ledger, synthesis, claims, and priorities updates.

## Findings

None.

## Verdict

Pass as-is.

The theorem is source-faithful to Aoyagi PDF p. 27 equation `(3)`.  When
`a=1`, the printed boundary `S_(ell-a+2)-1` becomes `S_(ell+1)-1`, represented
in Lean as `C.point ell - 1`.  The displayed value is `Htilde'_ell+1`, and the
selected-sum lemma gives `Htilde'_ell=0`, so the formal conclusion
`T(C.point ell - 1)=1` is correct.

The notes keep the claim conditional on a supplied equation `(3)` certificate
and do not overclaim construction, terminal `tilde t=0`, chart coverage,
order count, or RLCT content.

## Commands Run

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector`
- source PDF text extraction around pp. 24-28
- targeted inspections of Lean and expedition notes
