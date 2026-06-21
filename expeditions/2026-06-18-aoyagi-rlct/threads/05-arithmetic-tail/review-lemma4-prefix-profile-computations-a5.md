# Review - Lemma 4 prefix-profile computations

Status: reviewed/formalised; xhigh scout check survived.

## Scope

This slice adds two generic computations for the Lemma 4 increment-prefix
normal form: upper Htilde minus an offset gives `upperHighCount + offset`, and
lower Htilde gives `lowerHighCount`.

## Verdict

No findings.  Xhigh scout `Feynman` independently identified the same
corrected proof skeletons after detecting the first failed proof attempt and
duplicate endpoint lemma names.  The final Lean file keeps only the two
non-duplicate coordinate computations; the initial and terminal prefix facts
remain the pre-existing Lean lemmas.

## Checks

Focused Lean check passed:

```text
lake build DLNFibre.DLN.Aoyagi.HtildeChainArithmetic
```

## Nonclaims

These lemmas do not prove Eq5 endpoint profiles, binary deltas, two-value
Lemma 4 increments, Eq5 vector construction, endpoint realisation, source-label
legality, classifier data, order count, pole order, normal crossings, or RLCT
extraction.
