# Review - A6 supplied final assembly boundary

Status: reviewed/formalised; independent xhigh review survived.

## Scope

This slice adds `Theorem2FinalAssembly.lean`, a supplied final boundary that
packages existing A6/A0 bridge hypotheses and source-facing selected-width
provenance.

## Controller Check

The Lean result remains conditional.  It projects formula equalities only from
the supplied A0 extraction hypothesis and supplied finite exponent formula
equalities.  The selected-width fields are provenance and finite bookkeeping;
they do not construct Definition 3 selected cutpoints or prove the finite
exponent equalities.

## Checks

Focused Lean check passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean
```

Pen-and-paper/source reviewer `Nash the 2nd` passed the boundary as a
conservative supplied composition, with the warning that it may assert only
conditional projections and not Aoyagi Theorem 2 as an unconditional RLCT
theorem.

Lean/API scout `Turing the 2nd` recommended trimming the boundary structure:
keep selected-width equality, A0 extraction, and finite exponent formula as
fields, while taking selected rank-width and source selected-width inequality
as explicit auxiliary theorem arguments.  The Lean and docs were updated to
this smaller boundary.

## Pending

Independent xhigh diff reviewer `Curie the 2nd` found no blocking issues.  Two
low-severity findings were addressed before commit:

- `selectedWidth_le_pred` no longer takes an unused final-boundary argument;
  it depends only on `data` and the separately supplied source-selected
  inequality.
- The source anchor now says PDF p. 28 is conclusion/asymptotic discussion,
  not a separate proof-assembly step.

Controller gate passed after these repairs:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

## Nonclaims

This is not an unconditional Aoyagi Theorem 2 theorem.  It does not prove
normal-crossing chart production, finite exponent formula equalities, Lemma 5
order count, pole order without A0, or the analytic extraction theorem.
