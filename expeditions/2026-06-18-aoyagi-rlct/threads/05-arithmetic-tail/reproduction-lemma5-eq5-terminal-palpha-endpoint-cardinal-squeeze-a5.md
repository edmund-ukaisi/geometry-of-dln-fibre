# Reproduction - Lemma 5 Eq5 terminal pAlpha endpoint cardinal squeeze

Date: 2026-06-22.

Scope: finite cardinal-squeeze packaging for a supplied terminal-candidate
family.  This slice removes two opaque hypotheses from the previous
alpha-indexed terminal wrapper:

```text
Set.InjOn countedDatum TC.terminalMinimumLabels
base/nonbase branch-label separation
```

It does not construct Eq5 branches, prove terminal Eq5 payloads from source,
prove `(p, alpha)` injectivity from source, prove no-extra terminal-minimum
coverage, prove Lemma 5's order count, prove pole order, prove normal
crossings, or extract RLCT data.

## Inputs

Let `TC` be a supplied terminal-candidate family.  The existing terminal
cardinal-squeeze theorem uses:

```text
TC.terminalMinimumLabels
TC.fullBranches
TC.branchLabelImage
```

and proves terminal-minimum exactness once two independent injectivity facts are
available:

```text
hinjCountDatum :
  Set.InjOn (label |-> some (pOf label, T label label.1))
    TC.terminalMinimumLabels

hinjBranchLabel :
  Set.InjOn TC.branchLabel TC.fullBranches
```

The previous alpha-indexed branch wrapper derives `hinjBranchLabel` only after
assuming an opaque base/nonbase separation hypothesis.  The present wrapper
uses the already-proved structured adapters:

```text
TC.terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn

TC.branchLabel_injOn_of_eq5AlphaIndexed_nonbase_terminalEndpointBase
```

## Counted-datum injection

For terminal labels `x,y`, equality of counted data gives

```text
pOf x = pOf y
T x x.1 = T y y.1.
```

The supplied Eq5 piecewise source-vector payload at the own block gives

```text
T x x.1 = Htilde'_(pOf x) - labelAlphaOf x
T y y.1 = Htilde'_(pOf y) - labelAlphaOf y.
```

After rewriting by `pOf x = pOf y`, integer cancellation gives

```text
labelAlphaOf x = labelAlphaOf y.
```

Thus supplied injectivity of

```text
label |-> (pOf label, labelAlphaOf label)
```

on `TC.terminalMinimumLabels` proves `x=y`.  This is exactly the existing
adapter
`TC.terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn`.

## Branch-label injection

For nonbase branches, the existing alpha-indexed branch-label adapter proves
injectivity from:

```text
coordinatewise branch alpha injectivity,
nonbase branch source-coordinate block membership,
the Eq5 branch-label formula.
```

The remaining base/nonbase separation is supplied in a structured form:

```text
TC.branchLabel none = (cut.point (N+1)-1, 1).
```

If this base label equalled a nonbase branch label, the nonbase branch's
source-coordinate block membership would put the terminal endpoint
`cut.point (N+1)-1` inside an interior selected block.  The cutpoint API
excludes this.  Hence the terminal-endpoint base-label adapter gives
`Set.InjOn TC.branchLabel TC.fullBranches`.

## Cardinal squeeze

The existing Eq5 terminal counted-datum classifier gives

```text
|TC.terminalMinimumLabels| <= a * (N+1-a) + 1.
```

The supplied terminal-candidate lower-bound package gives

```text
TC.branchLabelImage subset TC.terminalMinimumLabels.
```

Branch-label injectivity and the supplied full-branch count give

```text
|TC.branchLabelImage| = a * (N+1-a) + 1.
```

Finite cardinality therefore forces

```text
TC.terminalMinimumLabels = TC.branchLabelImage.
```

Together with branch-label injectivity this is
`TC.TerminalMinimumLabelExactness`, and the exact terminal-minimum cardinality
follows.

## Lean targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze
```

## Nonclaims

- No Eq5 branch construction.
- No source proof of terminal Eq5 payload coverage.
- No source proof of terminal `(p, alpha)` injectivity.
- No source proof of alpha-domain coverage.
- No counted-datum-preserving back-to-label construction.
- No no-extra terminal-minimum coverage from Aoyagi's printed paragraph.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
