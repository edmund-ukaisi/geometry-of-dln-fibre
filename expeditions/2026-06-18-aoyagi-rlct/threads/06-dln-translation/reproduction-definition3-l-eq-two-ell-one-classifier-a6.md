# Reproduction - Definition 3 `L=2`, `ell=1` Classifier

Date: 2026-07-02.

Status: formalised; xhigh review passed; full verification passed.

## Source Anchor

Aoyagi Definition 3 on PDF pp. 8-9 gives selected source cutpoints and
selected/nonselected reduced-width inequalities.  This slice is only the
finite `L=2`, `ell=1` part of those inequalities.  It does not use the
normal-crossing-to-RLCT extraction theorem.

## Claim

For `L=2`, Definition 3 source data with `ell=1` exists exactly when the
three source-range reduced widths

```text
x = M^(1),   y = M^(2),   z = M^(3)
```

are all positive and at least two of them are equal.

## Forward Calculation

Assume

```text
S : AoyagiDefinition3SourceData 2 1 H r C.
```

There are two selected-index positions, hence a selected value image generated
by two selected reduced-width values.  The already-formalized `ell=1` cover
lemma says that every source-range value belongs to this selected value set:

```text
M^(s) in {M^(C_0), M^(C_1)},    s = 1,2,3.
```

The strict selected inequalities are, for the two selected values `a,b`,

```text
a < a+b,    b < a+b.
```

Equivalently `0 < b` and `0 < a`.  Since each of `x,y,z` has a
selected-index witness, all three source-range values are positive.

Finally, the three source-range values have selected-index witnesses in the
two-element index type `Fin 2`.  By the finite pigeonhole principle, two of
the chosen selected-index witnesses for `x,y,z` have equal indices.  Therefore
one of

```text
x = y,    x = z,    y = z
```

holds.

## Reverse Calculation

Assume `0 < x`, `0 < y`, `0 < z`, and one of the three equalities above.  The
existing constructor

```text
exists_ell_one_of_L_eq_two_positive_repeated
```

chooses two source cutpoints whose selected values cover all three
source-range values and proves the Definition 3 inequalities.  Thus
`ell=1` source data exists.

## Lean Shape

Added in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_ell_one_sourceData_iff_repeatedPositive_of_L_eq_two
```

This is an exact `ell=1` classifier, not a classifier for arbitrary `ell` and
not a canonical branch selection theorem.

The complete finite `L=2` classifier

```text
AoyagiDefinition3SourceData.exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two
```

now calls this theorem in its `ell=1` forward branch, rather than keeping the
same arithmetic embedded inline.

## Lean Check

Focused direct elaboration and focused module build passed:

```text
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
```

Xhigh reviewer `Mill the 2nd` passed the Lean/API review after a documentation
precision fix replacing "two-element selected value set" with selected-index
witnesses in `Fin 2`.

Full local verification also passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
```

The touched Lean-file forbidden-marker scan was clean.  Direct axiom probes
for the new theorem and the refactored complete `L=2` classifier report only:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

No `L > 2` statement, no arbitrary-`ell` branch choice, no branch-independent
Theorem 2 formula, no Eq5 payload, no chart production, no normal crossings,
no pole order, and no RLCT extraction.
