# Review - A5 Lemma 4 same-coordinate bridge

Reviewed objects:

- `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`
- `reproduction-lemma4-same-coordinate-bridge-a5.md`
- `statement-card-a5-lemma4-same-coordinate-bridge.md`

Verdict: source-gap classification and Lean/API design pass at the
same-coordinate bridge scope.

Independent xhigh source checker `Cicero the 5th` found that Aoyagi's
Definition 4 defines componentwise vector order but not a unique endpoint
selection map from `T` to `(H_j),(S_j)`.  The checker confirmed that the
endpoint conclusion follows with an explicit same-coordinate correspondence
and gave a two-coordinate counterexample showing that componentwise bounds
alone do not imply `H_ell=0`.

Independent xhigh Lean/API scout `Jason the 5th` found no existing A5 vector
API for this bridge and recommended a conservative wrapper using ordinary
pointwise function order, without importing A4 blow-up scaffolding.

Final independent xhigh landed-patch reviewer `Hooke the 5th` found no
findings.  The reviewer confirmed source-gap fidelity, Lean/API scope,
explicit hypotheses, proof hygiene, and consistency of
Proved/Assumed/Cited/Deferred documentation across the statement card and
expedition ledgers.

Scope check: this is not Aoyagi Lemma 4 itself.  It proves only that a supplied
same-coordinate vector squeeze implies the terminal endpoint sandwich and
therefore, with the selected-width endpoint-zero calculation, `H_ell=0`.  It
does not prove the source `T -> (H_j),(S_j)` correspondence, the full
`Htilde`/`Htilde'` chains, the two-value increment hypothesis, vector
admissibility, correspondence to `lambda`, Lemma 5, pole order, normal
crossings, or RLCT extraction.
