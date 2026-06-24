# Review - Definition 3 ell=1 nonselected obstruction

Date: 2026-06-24.

Reviewer: xhigh independent checker `Maxwell the 2nd`.

## Verdict

PASS.

The integer argument is correct.  For `ell = 1`, the nonselected upper
inequality gives the selected sum `T <= 0`; source-range rank-width
nonnegativity at the two selected cutpoints gives `0 <= T`; hence `T = 0`.
The strict selected inequality then gives `m_0 < 0`, contradicting selected
nonnegativity.

## Source Fidelity

The source use is faithful to Aoyagi Definition 3, PDF pp. 8-9.  The proof
uses only the strict selected inequality and the nonselected upper inequality.
Definition 3 also includes the selected-below-nonselected comparison, but this
comparison is unused in this obstruction.

## Lean Review

The checker accepted the positive membership target under explicit
source-range rank-width nonnegativity:

```text
AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth
```

The theorem has the expected inputs:

```text
S : AoyagiDefinition3SourceData L 1 H r C
hr : forall t, 1 <= t -> t <= L+1 -> r <= H t
hs1 : 1 <= s
hsL : s <= L+1
```

and concludes that the reduced-width value at `s` lies in the selected value
set.  The reviewer did not run a Lean build; the controller ran the focused
build separately.

## Nonclaims

No selected-cutpoint construction, no classification for `ell > 1`, no repair
of Definition 3, no Lemma 5 exactness, no chart production, no pole order, and
no RLCT extraction.

