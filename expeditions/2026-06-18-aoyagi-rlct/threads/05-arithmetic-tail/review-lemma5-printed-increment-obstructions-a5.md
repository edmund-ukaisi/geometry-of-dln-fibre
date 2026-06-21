# Review - Lemma 5 Printed Increment Obstructions

Reviewers: controller review; Bohr the 2nd final source-fidelity xhigh review.

Verdict: PASS.

## Findings

The Lean slice formalises only finite consequences of supplied adjacent
`H`-chain values.  It does not construct source vectors, labels, or charts.

The new Eq `(3)` theorems state that the nonterminal printed special value
forces the next Lemma 4 increment to be `M+1`, hence not one of the two
allowed values.

The new Eq `(4)` theorems state that the printed special one-point line forces
the corresponding increment to be the next selected width minus one, and under
Definition 3 selected-width hypotheses this is strictly below `M-1`.

## Checks

Controller checks completed so far:

```text
lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
scripts/sorries
lake build DLNFibre
git diff --check
```

The Lake command is run from `lean/`.

Bohr the 2nd independently checked the Lean statements and documentation
against Aoyagi Lemma 4 p. 25 and Lemma 5 equations `(3)` and `(4)` p. 27.  The
review found no blocking source-fidelity or theorem-boundary issues and reran
the focused module build, direct `lake env lean` module check, `scripts/sorries`,
and `git diff --check`.

## Residual Risks

This does not search for corrected formulas and does not prove that no
corrected reading of Aoyagi's proof exists.
