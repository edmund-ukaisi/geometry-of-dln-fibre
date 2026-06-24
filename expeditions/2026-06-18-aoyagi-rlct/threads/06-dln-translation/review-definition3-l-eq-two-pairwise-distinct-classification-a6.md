# Review - Definition 3 `L=2` pairwise-distinct classification

Reviewer: xhigh `Maxwell the 3rd`.

Status: passed with statement-tightening, incorporated.

## Verdict

The classification is mathematically sound under the explicit hypotheses:

```text
hr : forall s, 1 <= s -> s <= 3 -> r <= H s
```

and pairwise distinctness of the three integer reduced widths

```text
aoyagiReducedWidthInt H r 1,
aoyagiReducedWidthInt H r 2,
aoyagiReducedWidthInt H r 3.
```

The `ell=1` exclusion correctly uses the Lean structure's value-level
nonselected condition.  A nonselected source position is not enough by itself;
pairwise distinctness is what turns the missing source position into a missing
reduced-width value.

## Required Tightening

The final theorem must keep `hr` and pairwise distinctness explicit.  The
reproduction must phrase the all-source nonselected clauses as vacuous because
every source-range reduced-width value belongs to the selected value set, not
merely because every source position is selected.  The forced-cutpoint theorem
must be scoped to `ell=2` source data.

These requirements are incorporated in the Lean targets:

```text
AoyagiDefinition3SourceData.ell_eq_two_of_L_eq_two_rankWidth_pairwiseDistinct
AoyagiDefinition3SourceData.cut_eq_consecutive_of_L_eq_two
AoyagiDefinition3SourceData.exists_sourceData_iff_allSourceStrict_of_L_eq_two_rankWidth_pairwiseDistinct
```

## Nonclaims Checked

The result is only the `L=2` pairwise-distinct finite classification.  It does
not classify repeated-width profiles, repair Definition 3 for arbitrary
profiles, compute ceiling data, construct Eq5 payloads, produce charts, prove
source production, identify pole order, or extract RLCT.
