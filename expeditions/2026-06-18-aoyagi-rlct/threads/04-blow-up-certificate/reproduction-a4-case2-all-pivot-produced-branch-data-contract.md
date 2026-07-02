# Reproduction - A4 Case 2 all-pivot produced-branch-data contract

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before any Lean implementation.

## Question

Can Aoyagi's displayed Case 2 calculation on PDF pp. 19-22 fill the
recurrence-aware all-pivot producer's `sourceProduction` field?

Answer: not directly.  The source calculation gives the local pivot chart and
the finite continue/stop bookkeeping.  The Lean producer field requires
analytic chart-produced payloads in one fixed atlas context.  The correct next
step is to specify the exact produced-data contract and the remaining missing
mathematical fields.

## Source Calculation

At a pre-pivot state `(S,J)`, Case 2 assumes that the residual weights from
`J+1` through `M(S)` agree.  Aoyagi blows up the residual block entries:

```text
d_ij = 0
for i = J+1, ..., M(S)
and j = J+1, ..., M^(S+1).
```

On the selected pivot chart, the residual block is written as `u` times a
normalized matrix whose `(J+1,J+1)` entry is `1`.  The bookkeeping introduced
on p. 20 is:

```text
t_{S,J+1}^{(i)} = M^(i+1)        for i = 1, ..., S-1
t_{S,J+1}^{(S)} = ... = t_{S,J+1}^{(L)} = J
tilde t_{S,J+1} = J
b'_i = u b_i                    for i = J+1, ..., M(S)
M'_{S,J+1} = (M(S)-J)(M^(S+1)-J)
```

The exponent contribution is the number of entries in the blown-up center.
This is finite chart algebra; it does not by itself give a chart-domain point
in the all-pivot analytic atlas context.

Aoyagi then applies a regular matrix `Q` to normalize the first row and
transports the following factor by:

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

After substituting `b'_i = u b_i`, a regular matrix `P` clears the first
column and produces a block:

```text
D'''_J = [ 1  0 ]
         [ 0  D_{J+1} ]
```

with the appropriate row/column orientation when one side has collapsed.  The
displayed product identity rewrites the old product through `diag(b')`,
`D'''_J`, and `C'_J^(S+1)`.

## Branch Split

After the pivot `(J+1,J+1)` is consumed, the same-stage branch continues only
if another pivot remains:

```text
J + 2 <= prefixMinNat n (S + 1).
```

If not, then:

```text
prefixMinNat n (S + 1) = J + 1.
```

Since this prefix minimum is the minimum of the current prefix width and the
actual next width, Lean must keep two stopped cases:

```text
actual-width stopped:
  n (S + 1) = J + 1

row-exhausted stopped:
  prefixMinNat n S = J + 1
```

These stopped alternatives can overlap, so exclusivity is not the target.  The
target is payload separation: the terminal/suffix data needed in the
actual-width case is not definitionally the same as the row-exhausted case.

## State and Progress Check

The recurrence-aware branch state is:

```text
s : AoyagiRecurrenceBranchState L n alpha
```

with fields `(S,J)` and recurrence data over labels introduced at `(S,J)`.
For the continuing branch, the child state is:

```text
AoyagiRecurrenceBranchState.sameStageChildWithRecurrence s childRecurrence
```

where:

```text
childRecurrence :
  IntroducedLabelRecurrenceState L n s.S (s.J + 1) alpha
```

The existing progress theorem proves this is a decreasing child from the
prefix-minimum bound.  This is only a termination/progress fact.  It does not
prove that the produced chart point, produced source parameter, or
branch-specific source data realizes `childRecurrence`.

The source-production payload must therefore contain or be paired with a
source-faithful construction of the child recurrence data, not an arbitrary
inhabitant.

## Produced Payload Check

The current producer interface asks each branch payload to name:

```text
producedChart
producedPoint
producedPoint_mem_chartDomain
producedParam
producedParam_eq_chartMap
producedParam_mem_sourceDomain
sourceData
producedSourceData
```

The Aoyagi pp. 19-22 calculation supplies formulas for `u`, normalized
residual coordinates, `Q`, `P`, `C'`, and `D'''`.  It does not supply:

- the analytic chart token in `Fin C.numCharts`;
- the proof that the chosen point lies in the atlas chart domain;
- the source-domain membership proof for the produced parameter;
- overlap/domain regularity for transitions;
- the branch-specific source-data structures for successor and stopped
  payloads.

Thus, a Lean inhabitant of `SelectedEntryAtlasProducedBranchData` is
source-faithful only after these fields are built explicitly.

## Center-Alignment Check

For a single Case 2 branch state, the natural center is:

```text
case2ResidualBlockPivotEntries n S J
```

The all-pivot analytic atlas context, however, is built from one fixed
`center`.  If a recurrence-wide branch state ranges over many `(S,J)`, the
center changes with the state.

Therefore the current fixed-center all-pivot producer can be used safely only
under an explicit alignment mechanism:

- restrict the producer to one fixed state or one fixed center;
- include a proof that every active state has the fixed center;
- or replace the fixed-center producer by a dependent branch-indexed atlas
  interface.

Without this, the formulas may be correct for Aoyagi's local residual block
but typed against the wrong chart certificate.

## Reproduction Verdict

The elementary Aoyagi calculation supports the guard names and the continuing
same-stage update.  It also identifies the finite algebra that each
branch-specific source-data payload must contain.

It does not yet provide a direct Lean proof of:

```text
SelectedEntryAtlasProducedBranchData
  (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv)
  (AoyagiRecurrenceBranchState L n alpha)
```

The missing work is a source-data construction, not a wrapper around the
producer shell.

## Nonclaims

This packet proves no Lean theorem.  It does not construct source-production
payloads, analytic chart domains, atlas coverage, transition regularity,
Jacobian/volume compatibility, normal crossings, pole order, or RLCT.
