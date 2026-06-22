# Reproduction - Lemma 5 Eq5 branch-label injection

Status: reproduced; Lean checked; xhigh review passed.

## Source Boundary

Aoyagi PDF p. 27, equation `(5)`, supplies nonbase branch labels of the
strict-offset form

```text
k = Htilde'_j + 1 - alpha.
```

Earlier Lean slices already proved fixed-coordinate branch-label injectivity
from a supplied alpha projection that is injective on that coordinate's branch
family.  This slice does not construct the Eq5 branch family.  It only
packages the finite disjointness needed to lift those fixed-coordinate
injections to the full supplied terminal branch set.

The full supplied terminal branch set is `Option`-tagged:

```text
none       -- the supplied base branch
some b     -- a supplied nonbase branch
```

The nonbase branches are partitioned by coordinates
`j in Icc 1 N`.

## Reproduction

Let `TC` be a supplied terminal-candidate family, and write

```text
B = TC.fullBranches.
```

First, suppose the nonbase map

```text
b |-> TC.branchLabel (some b)
```

is injective on `{b | some b in B}`, and suppose the base branch label is
separated from every nonbase branch label:

```text
TC.branchLabel none != TC.branchLabel (some b)
```

for every `some b in B`.  Then `TC.branchLabel` is injective on all of `B` by
the four `Option` cases:

- `none = none` is immediate;
- `none` versus `some b` contradicts base/nonbase separation;
- `some b` versus `none` is the symmetric contradiction;
- `some b` versus `some c` follows from the supplied nonbase injectivity.

Now specialize the nonbase injectivity to Eq5 alpha-indexed branches.  Suppose
for each coordinate `j in Icc 1 N`:

```text
Set.InjOn alphaOf (TC.family.branches j),
cut.block j (TC.branchLabel (some b)).fst
  for every b in TC.family.branches j,
(TC.branchLabel (some b)).snd
  = Htilde'_j + 1 - alphaOf b
  for every b in TC.family.branches j.
```

Take two nonbase branches `some b, some c in B` with equal branch labels.  The
nonbase full-branch characterization gives coordinates

```text
j, k in Icc 1 N,
b in TC.family.branches j,
c in TC.family.branches k.
```

Equality of Sigma labels gives equality of source coordinates:

```text
(TC.branchLabel (some b)).fst = (TC.branchLabel (some c)).fst.
```

By the supplied block-membership hypotheses, that common source coordinate
lies in both selected blocks `j` and `k`.  Selected-cutpoint block uniqueness
therefore gives

```text
j = k.
```

With both branches in the same coordinate family, the fixed-coordinate Eq5
alpha-indexed injectivity theorem applies to the displayed label formula and
the supplied alpha injectivity.  Hence `b=c`.

Combining this nonbase injection with the base/nonbase separation gives full
branch-label injectivity on `TC.fullBranches`.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_fullBranches_of_some_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_eq5AlphaIndexed_nonbase
```

## Kill Conditions

- Do not infer base/nonbase separation from the Eq5 label formula; it remains
  an explicit hypothesis.
- Do not infer alpha injectivity from alpha-domain membership or coverage; it
  remains explicit coordinate-by-coordinate.
- Do not drop the supplied block-membership hypothesis; cross-coordinate
  disjointness comes from selected-cutpoint block uniqueness.
- Do not treat this as branch construction or as no-extra terminal-minimum
  coverage.

## Nonclaims

No Eq5 branch construction, no alpha-domain coverage, no terminal Eq5 payloads
for every terminal label, no counted-datum injectivity, no back-to-label map,
no upper-bound classifier, no no-extra terminal-minimum coverage, no Lemma 5
order count from the printed branch families, no pole order, no normal
crossings, and no RLCT extraction is proved here.
