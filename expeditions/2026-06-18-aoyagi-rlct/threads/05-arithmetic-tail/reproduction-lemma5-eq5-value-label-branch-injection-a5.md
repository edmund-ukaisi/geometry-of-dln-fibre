# Reproduction - Lemma 5 Eq5 value-label branch injection

Date: 2026-06-22.

Scope: finite branch-label injectivity and terminal cardinal-squeeze packaging
from supplied nonbase value-label data.  This does not construct Eq5 branches,
prove the value-label relation from Aoyagi's printed equations, prove terminal
Eq5 payload coverage, prove source no-extra coverage, prove the Lemma 5 order
count, prove pole order, prove normal crossings, or extract RLCT data.

## Branch-Label Injection

Let `TC` be a supplied terminal-candidate family.  Suppose every nonbase branch
label lies in its supplied selected block:

```text
cut.block j (TC.branchLabel (some b)).1
```

for `b in TC.family.branches j`, and suppose the branch label records the
branch value by:

```text
TC.family.value b = (TC.branchLabel (some b)).2 - 1.
```

Also keep base/nonbase branch-label separation supplied for the first adapter.

For two nonbase branches `b,c`, assume:

```text
TC.branchLabel (some b) = TC.branchLabel (some c).
```

Membership in `TC.fullBranches` gives coordinates `j,k` with

```text
b in TC.family.branches j,
c in TC.family.branches k.
```

Equality of source-label first coordinates and selected-block uniqueness give

```text
j = k.
```

After rewriting `c` into the same branch set, equality of source-label second
coordinates and the value-label relation give:

```text
TC.family.value b = TC.family.value c.
```

The supplied nonbase family already has one-coordinate value injectivity, so:

```text
b = c.
```

Together with the supplied base/nonbase separation, this proves injectivity of
`TC.branchLabel` on the full `Option`-tagged branch set.

## Terminal-Endpoint Base Label

The second adapter replaces the opaque base/nonbase separation hypothesis by
the existing terminal-endpoint base-label argument.  If

```text
TC.branchLabel none = (cut.point (N+1)-1, 1),
```

then equality with a nonbase branch label would put the terminal endpoint
`cut.point (N+1)-1` inside a selected block.  The cutpoint API excludes this.

## Cardinal Squeeze

The terminal pAlpha/value-label wrappers use:

```text
TC.terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn
TC.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase
```

as the counted-datum and branch-label injectivity inputs for the existing
finite cardinal-squeeze wrappers.  Thus, under supplied terminal Eq5 payloads,
terminal `(p, alpha)` injectivity, nonbase block membership, value-label data,
terminal-label nonbase inequalities, and the terminal-endpoint base label, Lean
proves:

```text
TC.TerminalMinimumLabelExactness
TC.terminalMinimumLabels.card = a * (N+1-a) + 1.
```

This remains a conditional exactness/cardinality theorem.  It is not a
source-backed no-extra coverage theorem.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
```

## Nonclaims

- No Eq5 branch construction.
- No source proof of the value-label relation.
- No source proof of terminal Eq5 payload coverage.
- No source proof of terminal `(p, alpha)` injectivity.
- No counted-datum-preserving back-to-label construction.
- No source-backed no-extra terminal-minimum coverage.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
