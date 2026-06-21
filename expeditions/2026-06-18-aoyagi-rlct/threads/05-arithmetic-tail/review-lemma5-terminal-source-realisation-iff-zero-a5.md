# Review - Lemma 5 terminal source realisation iff zero

Date: 2026-06-21.

Reviewer: xhigh independent reviewer `Chandrasekhar`.

## Verdict

Pass.  No blocking Lean, mathematical-scope, source-fidelity, naming, or
bedrock issue was found.

## Audit

The new equivalence theorems

```text
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_realisation_iff_terminalZero
AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_realisation_iff_terminalZero
```

are correct hypothesis reductions.  They use branch-chain terminal zero to
rewrite

```text
F.fullH x (Fin.last ell) = 0
```

into an equivalence between source-realisation equality and source-zero
equality.

The admissible theorem correctly keeps `a<=ell` and the selected-width sum,
because those hypotheses are needed by the admissible terminal chain-zero
theorem.  The binary theorem correctly omits them because binary terminal
chain-zero is supplied by `Hlast` and `baseHlast` fields.

The Lean statements and notes do not claim terminal source zero, construction
of the source-realisation equality, terminal source-branch construction,
terminal-label exactness, classifier coverage, pole order, normal crossings,
or RLCT extraction.

## Verification

The reviewer reported:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalSourceBridge.lean
```

passing from the `lean/` directory.  The controller also ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalSourceBridge.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5TerminalSourceBridge
lake build DLNFibre
./scripts/sorries
git diff --check
```

with the build and scanner passing; the full build emitted only pre-existing
Core linter warnings.
