# Statement Card - A5 Lemma 5 Supplied Terminal Candidate Family

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalLeastValue_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalExponent_eq_minNumerator`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalCandidateData`

## Claim

A supplied terminal-candidate family attaches each tagged supplied Lemma 5
branch to an introduced source label, supplies terminal least value zero, and
supplies the missing numerator normalisation.  Therefore each tagged branch has
terminal exponent equal to the isolated Lemma 3 minimum numerator.

## Inputs

- A full supplied admissible Lemma 5 branch family.
- Introduced-label exponent certificates.
- Branch-to-label maps `branchS`, `branchK`.
- Branchwise introduced-label proofs.
- Branchwise least-value-zero proofs.
- Branchwise numerator normalisations to the Lemma 3 free-count expression.
- The selected-width sum hypothesis and `a <= n+1`.

## Proves

- The inherited branch count:

```text
|fullBranches| = a*(n+1-a)+1.
```

- For each tagged branch:

```text
introducedLabel(branchS x, branchK x),
leastValue(branchS x, branchK x)=0,
terminalExponent(branchS x, branchK x)=a*(n+1)*((n+1)-a).
```

## Does Not Prove

- Source construction of the branch labels.
- Terminal `tilde t=0` from Aoyagi's printed chart process.
- Injectivity of branch labels or absence of extra terminal minimizers.
- `lambda`, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi PDF pp. 22-27.  This is a supplied-data package because the printed
Lemma 5 family does not currently provide reproduced source-label,
terminality, numerator-normalisation, or no-extra-minimizer data.
