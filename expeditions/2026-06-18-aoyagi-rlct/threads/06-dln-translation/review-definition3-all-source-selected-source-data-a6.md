# Review - Definition 3 all-source selected source data

Reviewer: xhigh `Erdos the 3rd`.

Status: passed.

## Verdict

The constructor is valid and worth formalising.  It is a genuine
generalisation of the equal-width lane: it keeps the same consecutive
all-source cutpoints but replaces the constant positive reduced-width
hypothesis with the exact strict selected inequality needed by
`AoyagiDefinition3SourceData`.

## Corrections Incorporated

The strict hypothesis is stated against the consecutive all-source sum:

```text
sum_{j : Fin (L+1)} M^(j.val+1).
```

No rank-width, positivity, or constant-width hypothesis is included.  The
nonselected fields are discharged directly, because `AoyagiDefinition3SourceData`
uses nonmembership in the selected width-value image and every source-range
value has a consecutive selected cutpoint witness.

## Nonclaims

This does not prove arbitrary selected-cutpoint existence, classify
Definition 3, produce a ceiling datum in closed form, construct Lemma 5
vectors, produce charts, identify pole order, or extract RLCT.
