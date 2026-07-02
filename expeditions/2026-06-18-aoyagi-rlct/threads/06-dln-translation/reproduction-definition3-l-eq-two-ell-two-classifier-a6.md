# Reproduction - Definition 3 `L=2`, `ell=2` Classifier

Date: 2026-07-02.

Status: formalised; scout review passed; full verification passed.

## Source Anchor

Aoyagi Definition 3 on PDF pp. 8-9 gives selected source cutpoints and the
selected/nonselected reduced-width inequalities.  This slice is only the
finite `L=2`, `ell=2` part of those inequalities.  It is independent of the
normal-crossing-to-RLCT extraction theorem.

## Claim

For `L=2`, Definition 3 source data with `ell=2` exists exactly when the
three all-source strict triangle inequalities hold:

```text
2*x < x+y+z,   2*y < x+y+z,   2*z < x+y+z,
```

where

```text
x = M^(1),   y = M^(2),   z = M^(3).
```

## Forward Calculation

Assume

```text
S : AoyagiDefinition3SourceData 2 2 H r C.
```

There are three selected cutpoints, and each is between `1` and `3`.  Since
the cutpoints are strictly increasing, they must be consecutive:

```text
C_0 = 1,   C_1 = 2,   C_2 = 3.
```

This is the already-formalized lemma

```text
cut_eq_consecutive_of_L_eq_two.
```

The selected strict inequalities in Definition 3 are therefore exactly

```text
2*M^(1) < M^(1)+M^(2)+M^(3),
2*M^(2) < M^(1)+M^(2)+M^(3),
2*M^(3) < M^(1)+M^(2)+M^(3).
```

No nonselected inequality is used in this direction.

## Reverse Calculation

Assume the three all-source strict inequalities.  Package them as

```text
forall s, 1 <= s -> s <= 3 ->
  2*M^(s) < sum_{j : Fin 3} M^(j+1).
```

The existing constructor

```text
exists_consecutive_of_all_selected_strict
```

with `L=2` chooses the consecutive selected cutpoints and proves Definition 3
source data with `ell=2`.

## Lean Shape

Add in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_ell_two_sourceData_iff_triangle_of_L_eq_two
```

The complete finite `L=2` classifier should then call this theorem in its
`ell=2` forward branch and in the triangle reverse branch.

Implemented in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.  The
complete finite `L=2` classifier now calls this theorem in its `ell=2`
forward branch and in the triangle reverse branch.

## Lean Check

Focused direct elaboration and focused module build passed:

```text
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
```

Xhigh scout `Ptolemy the 2nd` checked the target shape and passed it: no exact
fixed-`ell=2` iff theorem was already named, the statement is the right finite
source-data slice, and the direct proof through consecutive cutpoints and the
all-source selected constructor is preferred.

Full local verification also passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
```

The touched Lean-file forbidden-marker scan was clean.  Direct axiom probes
for the two fixed-branch classifiers and the refactored complete `L=2`
classifier report only:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

No `L > 2` statement, no arbitrary-`ell` branch choice, no branch-independent
Theorem 2 formula, no Eq5 payload, no chart production, no normal crossings,
no pole order, and no RLCT extraction.
