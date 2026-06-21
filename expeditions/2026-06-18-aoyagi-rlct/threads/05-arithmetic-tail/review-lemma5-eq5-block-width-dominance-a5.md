# Review - Lemma 5 equation (5) block width dominance

Reviewers: `McClintock the 2nd` (xhigh paper/source scout) and
`Locke the 2nd` (xhigh Lean/API scout).  Verdict: valid as a conditional
index-level width bridge; invalid if stated as a Definition 3 consequence
without extra assumptions.

## Findings

No issue was found with the conditional Lean statements.

The selected-block arithmetic is direct:

```text
C.block p S
```

gives

```text
C.point p <= S+1 < C.point(p+1).
```

Thus any block-local lower-bound hypothesis for actual widths immediately
supplies `W_p <= n(S+1)`.

The left-endpoint-minimum wrapper is also valid: if the selected left endpoint
has width `W_i` and the block's actual widths are no smaller than that
endpoint width, the block-local lower-bound hypothesis follows.

The off-selected dominance wrapper is valid only because it is stated at the
level of layer positions.  If `S+1` is not the block's left endpoint, it is
strictly between adjacent selected cutpoints and therefore unequal to every
selected cutpoint.

## Source Fidelity

The theorem must not be presented as a direct consequence of Definition 3.
Definition 3's non-selected dominance is value-level: it applies when
`M(s)` is not in the selected width-value set.  It does not control an
unselected layer whose width equals a selected width.

The saved reproduction includes a concrete obstruction with duplicate selected
width values.  Therefore the Lean theorem correctly keeps one of the following
extra hypotheses explicit:

- block-local width dominance;
- left-endpoint width plus block-local minimum;
- index-level off-selected-layer dominance.

## Checks

Controller verification:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
lake env lean DLNFibre.lean
lake build DLNFibre
./scripts/sorries
git diff --check
```

These passed.  The full build emitted only known pre-existing Core warnings.

## Residual Risks

This theorem does not prove:

- block-local width dominance from Definition 3 alone;
- no-duplicate selected-width-value data;
- equation `(5)` displayed-vector construction or existence;
- terminal `tilde t=0`;
- vector admissibility or source-vector-to-chain correspondence;
- Case 1(2) chart sequence;
- Lemma 5 order count;
- pole order, normal crossings, or RLCT extraction.
