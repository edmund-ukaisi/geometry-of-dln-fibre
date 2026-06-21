# Statement card - A5 Lemma 5 equation (5) piecewise certificate

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5Eq5PiecewiseSourceVector`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5Eq5SelectedSpanBranchValue`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_branchValue_of_block`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_selectedSpan_branchValue`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector`

## Claim

Lean now has a supplied branch certificate for Aoyagi Lemma 5 equation `(5)`.
With paper `j0` represented by Lean coordinate `p`, the certificate records
the five displayed branches over selected blocks in zero-based notation.

For any source index in the half-open selected span, Lean classifies it into
one of the advertised equation `(5)` branch alternatives.  The certificate
also implies the previously defined own-coordinate branch record, so the
existing Eq(5) offset and interval-membership lemmas can be applied to any
full supplied certificate.

## Inputs

- Selected cutpoints `C`.
- A supplied equation `(5)` branch certificate.
- Source guards stored as fields:
  `a<=ell`, `1<=alpha`, `alpha<p`,
  `alpha<=aoyagiLemma5IntervalExcess ell a p`, and
  `p+(a-alpha)+1<=ell`.

## Proves

- Selected-block classification into the five equation `(5)` branches.
- Selected-span classification using the existing selected-block coverage.
- Conversion from the full supplied certificate to
  `AoyagiLemma5Eq5OwnCoordinateBranch`.

## Does Not Prove

- Construction or existence of equation `(5)`'s displayed vector.
- Source-label legality for `k`.
- Terminal `tilde t=0`.
- Coverage outside the half-open selected span or at the terminal endpoint.
- Vector admissibility or source-vector-to-chain correspondence.
- Case 1(2) chart sequence.
- Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi PDF p. 27, equation `(5)`.

## Review

Pen-and-paper scout: `Schrodinger`.
Lean API scout: `Euclid`.
Final landed review: `review-lemma5-eq5-piecewise-certificate-a5.md`.
