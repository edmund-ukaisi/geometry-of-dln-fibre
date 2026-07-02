# Reproduction - A4 Case 2 branch-indexed current-center payloads

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before Lean support-layer
implementation.

## Question

After the fixed-current-center payload constructors, what is the next honest
interface for all-pivot Case 2 source production?

The answer is not a recurrence-wide fixed-center
`SelectedEntryAtlasProducedBranchData`.  Aoyagi's Case 2 calculation is local
at a branch state `(S,J)`.  The blow-up center is the current residual block:

```text
case2ResidualBlockPivotEntries n S J
```

As `(S,J)` changes along the recurrence, this center changes.  The Lean
producer record `SelectedEntryAtlasProducedBranchData ctx BranchState` has one
fixed `ctx`, hence one fixed selected-entry center.  Current-center payloads
can therefore be assembled recurrence-wide only through either an explicit
fixed-center alignment condition or a branch-indexed interface.

## Source Reproduction

Aoyagi Case 2 assumes equality of the current residual weights
`b_{J+1} = ... = b_{M(S)}` and blows up the residual block entries

```text
d_ij = 0,
i = J+1, ..., M(S),
j = J+1, ..., M(S+1).
```

On the selected chart, the block is written as `u_{S,J+1}` times a normalized
matrix whose selected entry is `1`.  The source substitutions include

```text
b'_{J+1} = u_{S,J+1} b_{J+1}, ..., b'_{M(S)} = u_{S,J+1} b_{M(S)}
M'_{S,J+1} = (M(S)-J)(M(S+1)-J).
```

The regular matrix `Q` normalizes the first row, and Aoyagi transports the
following factor by

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

Then a regular matrix `P` clears the first column and yields a block
`D'''_J` with selected entry `1` and lower-right block `D_{J+1}`.  The product
identity is rewritten through `diag(b')`, `D'''_J`, and the transported
following factor.

This calculation identifies a local selected pivot and the local chart source
data at `(S,J)`.  It does not identify one fixed center shared by every later
branch state.

## Branch Split

The continuing branch moves to `(S,J+1)` when another pivot remains:

```text
J + 2 <= prefixMinNat n (S + 1).
```

When no further pivot remains, the stopped alternatives are still separate:

```text
actual-width stopped:
  n (S + 1) = J + 1

row-exhausted stopped:
  prefixMinNat n S = J + 1
```

The row-exhausted payload APIs in Lean are not yet one total semantic row
payload.  They remain split into:

```text
terminal-last:
  row-exhausted stopped and S + 1 = L

source-suffix:
  row-exhausted stopped and S + 1 <= L
```

These packages are not exclusive.  They are different data packages for
different downstream source information, not a proof that the row-exhausted
semantic guard has already been collapsed into the producer's single row
payload.

## Fixed-Center Alignment Contract

If a recurrence-wide fixed-center all-pivot producer is attempted with a fixed
center `center : Finset (ℕ × ℕ)`, then current-center payloads require:

```text
for every active branch state s,
  center = case2ResidualBlockPivotEntries n s.S s.J.
```

This is stronger than anything printed in Aoyagi's local Case 2 calculation.
It is an additional interface condition.  Without it, a payload constructed
from the formulas at state `s` is typed over the current residual-block chart
certificate, while the producer shell expects the fixed chart certificate.

## Branch-Indexed Interface

The honest support layer is therefore branch-indexed:

```text
for each continuing state s:
  payload over case2ResidualBlockPivotEntries n s.S s.J

for each actual-width stopped state s:
  payload over case2ResidualBlockPivotEntries n s.S s.J

for each terminal-last row-exhausted state s:
  payload over case2ResidualBlockPivotEntries n s.S s.J

for each source-suffix row-exhausted state s:
  payload over case2ResidualBlockPivotEntries n s.S s.J
```

Each payload carries its own public chart equivalence for that current center.
The existing fixed-center constructors provide the branch entries of this
interface.

## Verdict

Formalise a branch-indexed current-center payload support layer and a
fixed-center alignment contract.  Do not provide a conversion to
`SelectedEntryAtlasProducedBranchData`.  Such a conversion would require
either a genuine fixed-center alignment proof or a redesigned dependent atlas
producer whose context varies with branch state.

## Nonclaims

This slice proves no recurrence-wide producer, no full row-exhausted semantic
payload, no source-production coverage theorem, no transition regularity, no
Jacobian/volume compatibility, no normal crossings, no pole order, and no
RLCT extraction.
