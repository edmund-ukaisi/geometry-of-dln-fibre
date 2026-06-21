# Reproduction - Lemma 5 Terminal Minimum Label Bijection API

Status: supplied-data wrapper; Lean formalised.

The exactness package stores two supplied fields:

```text
branchLabel is injective on fullBranches
terminalMinimumLabels subset branchLabelImage
```

For downstream finite chart/certificate data, the same content is often more
natural as a single bijection from supplied branches to terminal minimum
labels.  This note records the finite equivalence used by the Lean wrapper.

## From Exactness To Bijection

The map is the existing supplied branch label map

```text
branchLabel : Option beta -> Sigma Nat (fun _ => Nat).
```

It is a bijection

```text
fullBranches -> terminalMinimumLabels
```

because:

1. maps-to follows from the already proved inclusion
   `branchLabelImage subset terminalMinimumLabels`;
2. injectivity is the exactness field `branchLabel_injOn`;
3. surjectivity follows from
   `terminalMinimumLabels = branchLabelImage`, which is the equality derived
   from exactness.

## From Bijection To Exactness

Conversely, a supplied `Set.BijOn branchLabel fullBranches terminalMinimumLabels`
has:

1. injectivity on `fullBranches`, by `BijOn.injOn`;
2. no-extra containment, by `BijOn.surjOn`: every terminal minimum label is the
   image of a supplied branch, hence lies in `branchLabelImage`.

Thus a supplied bijection is a standard API form of the same finite exactness
boundary.

## Count

Once a bijection is supplied, the terminal-minimum set equals the finite image
of `branchLabel` over `fullBranches`; branch-label image counting and the
already proved full-branch count give

```text
terminalMinimumLabels.card = a*(n+1-a)+1.
```

This count does not use the selected-width sum because the bijection already
contains the exact coverage of terminal minimum labels.  It still assumes
`a <= n+1` for the supplied full-branch count.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_exactness
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_branchLabel_bijOn
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_branchLabel_bijOn
```

## Nonclaims

- The bijection is not proved from Aoyagi's printed equations.
- No source-backed branch-label injectivity or no-extra-minimizer theorem is
  proved.
- No pole order, normal crossings, or RLCT extraction is proved.
