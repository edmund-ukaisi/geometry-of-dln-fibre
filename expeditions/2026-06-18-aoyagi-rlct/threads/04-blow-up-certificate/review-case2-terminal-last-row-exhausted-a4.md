# Review - A4 Case 2 terminal-last row-exhausted boundary

Reviewed objects:

- `exists_sourceOldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`
- `exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`
- `reproduction-case2-terminal-last-row-exhausted-a4.md`
- `statement-card-a4-case2-terminal-last-row-exhausted.md`

Verdict: no blocking source/math or overclaiming issue found.

The theorem follows the same matrix-entry-ideal suffix-removal pattern as the
actual-width terminal-last theorem, but starts from the existing row-exhausted
transported-prefix source-suffix theorem.  The statement keeps
`prefixMinNat n S=J+1` and `S+1=L` explicit, consumes
`sourceSuffixProduct κ Ctail S hSuffix`, keeps the RHS as weighted transported
prefix rows, and does not import original-row equality or `(S+1,0)` relabelled
certificates.

The reproduction note now distinguishes the weighted RHS product from the
underlying transported-row factor: row `J+1` of that factor is the top row of
`Q^-1 C`, possibly with post-pivot column corrections in wide-next cases.

The statement card and thread keep the result scoped: no chart coverage, source
production of `C'^(S+1)`, chart-produced following products, Jacobian
arithmetic, normal crossings/RLCT extraction, transition invariance,
termination, or printed-vector repair is claimed.

Independent xhigh review (`Sagan the 5th`) reported no blockers.  It did not
run Lean; controller verification ran
`lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` and
`lake build DLNFibre`.
