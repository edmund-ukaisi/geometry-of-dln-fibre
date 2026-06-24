# Review - A4 Case 2 supplied-successor reindexed product

Date: 2026-06-24.

Reviewer: xhigh scout `Einstein the 2nd`.

Verdict: pass after metadata refresh.

## Findings

- Low: the initial statement card and reproduction metadata were stale after
  Lean implementation and the focused module build.  This was documentation
  hygiene only, not a mathematical or Lean issue.

No high or medium findings.

## Fidelity Check

The reproduction justifies exactly the Lean theorem: assume a supplied
successor equality

```text
Csucc = case2DisplayedSourceSuccessorFollowingFactor n hS hcont residual C,
```

reuse the same row-operation witness `q`, and rewrite only the right-hand
successor object in the displayed reindexed product.  All corrected post-data
fields are preserved.

## Lean Statement Check

The statement keeps both inputs explicit:

```text
hB :
  case2DisplayedSourceSubstitutionBlock n hS hcont u residual = B
hCsucc :
  Csucc = case2DisplayedSourceSuccessorFollowingFactor n hS hcont residual C
```

It does not assert source production, chart production, analytic transition
regularity, normal crossings, pole order, or RLCT data.

## Proof Check

The proof is finite congruence: it calls the existing substitution-block
theorem, keeps the witness and post-data, then closes by rewriting the two
proposition abbreviations with `hCsucc`.

The `SourceProductionObligation` wrapper is acceptable.  It is a thin adapter
using only `ob.Csucc_eq_formula`; it adds no source-production claim and no
new obligation field.

## Verification

Reviewer-observed commands:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
git diff --check
```

Both passed.
