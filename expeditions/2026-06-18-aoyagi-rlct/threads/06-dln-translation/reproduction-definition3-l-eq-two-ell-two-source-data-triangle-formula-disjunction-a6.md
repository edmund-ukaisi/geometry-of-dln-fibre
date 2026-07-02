# Reproduction - Definition 3 `L=2`, `ell=2` Triangle Formula Disjunction

Date: 2026-07-02.

Status: formalised; xhigh review passed; full verification passed.

## Source Anchor

Aoyagi Definition 3 on PDF pp. 8-9 supplies the finite selected-width
inequalities.  The existing Lean branch packages reproduce the finite Theorem
2 formula arithmetic for the `L=2` all-source triangle branch.  This slice is
only a fixed-`ell=2` dispatch theorem.

## Claim

Given

```text
S : AoyagiDefinition3SourceData 2 2 H r C
```

and Nat witnesses

```text
M^(1)=w1,   M^(2)=w2,   M^(3)=w3,
```

the finite Theorem 2 branch package is one of the two triangle packages:

```text
L2TriangleOddTheorem2FormulaBranch H r w1 w2 w3
or
L2TriangleEvenTheorem2FormulaBranch H r w1 w2 w3.
```

There is no repeated-positive branch in this fixed-`ell=2` conclusion.

## Calculation

The extracted classifier

```text
exists_ell_two_sourceData_iff_triangle_of_L_eq_two
```

turns `S` into the three integer strict triangle inequalities:

```text
2*M^(1) < M^(1)+M^(2)+M^(3),
2*M^(2) < M^(1)+M^(2)+M^(3),
2*M^(3) < M^(1)+M^(2)+M^(3).
```

Using the Nat-width identities, these become

```text
2*w1 < w1+w2+w3,
2*w2 < w1+w2+w3,
2*w3 < w1+w2+w3.
```

Now split on the parity of `w1+w2+w3`.  If the total is odd, call

```text
exists_consecutive_three_widths_theorem2Formula_of_triangle_odd.
```

If not odd, the remainder modulo `2` is `0`, and call

```text
exists_consecutive_three_widths_theorem2Formula_of_triangle_even.
```

The Nat-width wrapper first obtains `w1,w2,w3` from the supplied `ell=2`
source datum via the existing `L=2` source-data Nat-width extraction and then
applies the fixed-`ell=2` branch theorem.

## Lean Shape

Add in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_L_eq_two_ell_two_theorem2Formula_triangleBranchDisjunction_of_sourceData
AoyagiDefinition3SourceData.exists_L_eq_two_ell_two_theorem2Formula_triangleBranchDisjunction_of_sourceData_natWidths
```

Implemented in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

## Lean Check

Focused direct elaboration and focused module build passed:

```text
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
```

Xhigh reviewer `Euler the 2nd` passed the Lean/API/nonclaim review.

Full local verification also passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
```

The touched Lean-file forbidden-marker scan was clean.  Direct axiom probes
for the two new declarations report only:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

No canonical branch choice between odd/even beyond parity, no repeated-branch
exclusion for arbitrary `L=2` source data, no branch-independent lambda/order
payload, no Eq5 payload, no chart production, no normal crossings, no pole
order, and no RLCT extraction.
