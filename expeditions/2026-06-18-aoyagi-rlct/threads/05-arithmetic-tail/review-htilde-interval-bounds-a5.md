# Review - A5 Htilde interval bounds

Reviewed objects:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `reproduction-htilde-interval-bounds-a5.md`
- `statement-card-a5-htilde-interval-bounds.md`

Verdict: pass at the stated same-coordinate finite interval-bound scope.

Independent xhigh source checker `Nietzsche the 5th` confirmed that Aoyagi
Definition 4 on PDF p. 14 defines only componentwise vector order and does not
define a canonical endpoint projection or a unique map `T -> (H_j),(S_j)`.
The checker also confirmed that the endpoint implication is valid with a
supplied same coordinate and false as a pure componentwise-order statement.

Independent xhigh Lean/API scout `McClintock the 5th` recommended the
interval-offset/value-set API and a separate conditional treatment of the
two-value increment blocker.  The scout explicitly warned not to derive
`F_j in {M-1,M}` from same-coordinate chain bounds alone.

Final independent xhigh landed-patch reviewer `Ampere the 5th` found no
findings.  The reviewer checked source fidelity, theorem scope, Lean
assumptions, overclaiming risks, finite interval membership/cardinality,
endpoint zero, and displayed-chain count wrappers.  The reviewer confirmed
that the arbitrary-chain two-value hypothesis remains explicit and that the
remaining risks are exactly the deferred A5 obligations.

Scope check: this is not Aoyagi Lemma 4 or Lemma 5.  It proves only finite
same-coordinate interval membership, endpoint-zero consequences, displayed
chain two-value counts, and conditional wrappers into existing finite count
theorems.  It does not prove a source `T -> (H_j),(S_j)` correspondence,
same-coordinate hypotheses for Aoyagi's displayed extremal vectors, arbitrary
intermediate two-value increments, vector admissibility, chart coverage, pole
order, normal crossings, or RLCT extraction.
