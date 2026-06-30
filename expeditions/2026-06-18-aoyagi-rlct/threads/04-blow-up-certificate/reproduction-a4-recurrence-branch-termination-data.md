# Reproduction - A4 recurrence branch termination data

Date: 2026-06-30.

Status: controller pen-and-paper reproduction before Lean.

## Question

How should the combined recurrence branch progress kernel be exposed to the
selected-entry analytic-atlas interface?

The selected-entry producer interface asks for a
`SelectedEntryBranchTerminationData`, namely:

```text
step : BranchState -> BranchState -> Prop,
WellFounded step,
initial : BranchState.
```

The previous slice already built the finite branch state
`AoyagiRecurrenceBranchState L n alpha` and the well-founded relation
`AoyagiRecurrenceBranchState.progressStep L n alpha`.  Thus the only new datum
needed to produce termination data is an initial recurrence state over the
initial branch domain `(S,J)=(1,0)`.

## Finite Calculation

The initial state is

```text
S = 1,
J = 0.
```

The stage proof obligations are:

```text
1 <= 1,
1 <= L.
```

The first is reflexive; the second is a supplied hypothesis `hL : 1 <= L`.
The recurrence field is supplied as

```text
initialRecurrence : IntroducedLabelRecurrenceState L n 1 0 alpha.
```

Then the termination data is:

```text
step = AoyagiRecurrenceBranchState.progressStep L n alpha,
step_wellFounded =
  AoyagiRecurrenceBranchState.progressStep_wellFounded L n alpha,
initial =
  (1, 0, proof 1<=1, hL, initialRecurrence).
```

## Nonclaims

This constructs no source-production payloads, no branch guards, no child
states for continuing branches, no terminal payloads, no chart construction,
no full analytic-atlas branch termination theorem, no normal crossings, no pole
order, and no RLCT.

It only makes the finite well-founded relation available through the existing
selected-entry termination-data socket.
