# Review - Lemma 5 Eq4 rising-guard exhaustion

Date: 2026-06-21.

Reviewer: xhigh independent reviewer `Lagrange`.

## Verdict

Pass.  No blocking Lean, mathematical, source-fidelity, naming, or bedrock
issue was found.

## Audit

The Lean statements are correct and narrowly scoped to guard arithmetic.
The hypothesis `p<=a` is necessary for

```text
not (p+1<=a) <-> p=a.
```

The raw selected-index variant correctly adds `a<=ell`, because it rewrites
the printed cutoff bound through `aoyagiLemma5Eq4_selectedIndexGuard_iff`.

The displayed-vector wrapper does not overclaim.  It combines guard failure
with the existing `AoyagiLemma5Eq4PiecewiseSourceVector.indexGuard` field and
does not state the false converse

```text
not Eq4PiecewiseSourceVector(...) <-> p=a.
```

The notes accurately identify Aoyagi Lemma 5 equation `(4)` on PDF p. 27 as
the source of the printed `j0<=a` condition and the repaired
`p+1<=a` guard, and they distinguish the `p=a` guard-failure boundary from the
guard-success terminal case `p+1=a`.

## Verification

The reviewer reported focused `lake env lean` checks passing for the two
touched Lean files.  The controller also ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5IntervalArithmetic
lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
lake build DLNFibre
./scripts/sorries
git diff --check
```

with the build and scanner passing; the full build emitted only pre-existing
Core linter warnings.
