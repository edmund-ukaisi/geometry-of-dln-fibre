# Review - A5 Htilde value-set count

Reviewer: `Goodall the 5th` (xhigh landed-patch review).

Verdict: pass.

## Scope Checked

- Lean patch in `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`.
- Reproduction note:
  `reproduction-htilde-value-set-count-a5.md`.
- Statement card:
  `statement-card-a5-htilde-value-set-count.md`.
- Expedition ledger updates.

## Findings

No blocking findings.

The Nat-indexed wrapper is empty outside `j < ell+1`, and the summed theorem
uses exactly `Finset.Icc 1 (ell-1)` with an explicit range proof before
rewriting cardinalities.  No off-by-one issue was found.

Against Aoyagi PDF pp. 25-27, the patch matches the displayed
`Htilde`/`Htilde'` interval-size arithmetic and does not upgrade it into
Lemma 5's chart-family/order-count theorem.  The reproduction and ledgers keep
admissibility, coverage, vector constructions, pole-order interpretation,
normal crossings, and RLCT extraction deferred.

## Follow-up Applied

The reviewer noted a non-blocking wording issue in the statement card: the
excess sum is `a(ell-a)`, while the baseline-plus-excess count is
`a(ell-a)+1`.  The statement card was updated to use that distinction.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre.lean`
- `lake build DLNFibre`
- `git diff --check`
- `./lean/scripts/sorries`
