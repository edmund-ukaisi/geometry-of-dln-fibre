# Reproduction - Lemma 5 terminal Eq5 gap

Date: 2026-06-21.

Scope: one-coordinate finite-set inventory at the terminal coordinate
`p=ell`.  This records that Eq5's strict offsets are empty at the terminal
coordinate, while the same-coordinate interval is the singleton `{0}` under
Definition 3's selected-width sum.  A separately supplied terminal zero fills
that singleton, but this slice does not construct such a source branch.

This does not construct Aoyagi's displayed vectors, prove source-label
legality, terminal-label exactness, chart coverage, all-coordinate
branch-family coverage, pole order, normal crossings, or RLCT extraction.

## Source Inventory

Aoyagi Lemma 5 equation `(5)` supplies strict offsets

```text
Htilde'_p - alpha,    1 <= alpha < p,
```

with the additional interval-excess guard.  At `p=ell`, the interval excess is

```text
min(ell, ell-ell, a, ell-a) = 0.
```

Therefore no positive `alpha` satisfies the guard, and the Eq5 strict-offset
set is empty.

The displayed lower and upper `Htilde` chains have common terminal value zero
under Definition 3's selected-width sum:

```text
Htilde_ell = 0,    Htilde'_ell = 0.
```

This is already proved in Lean as the terminal-zero facts for the lower and
upper chains.

## Pen-And-Paper Derivation

At `p=ell`, Eq5's offset set is

```text
{ Htilde'_ell - alpha :
    alpha in [1, min(intervalExcess(ell), ell-1)] }.
```

Since `intervalExcess(ell)=0`, the upper bound of the alpha interval is `0`,
so there is no `alpha>=1`.  Hence

```text
Eq5Offsets_ell = empty.
```

Under the selected-width sum and `a<=ell`, the terminal Htilde values are

```text
Htilde_ell = 0,
Htilde'_ell = 0.
```

The same-coordinate interval between equal endpoints is the singleton

```text
IntervalValueSet_ell = {0}.
```

Thus Eq5 offsets alone do not fill the terminal interval:

```text
Eq5Offsets_ell != IntervalValueSet_ell.
```

If a separate source branch supplies terminal value zero, i.e.

```text
T(C.point ell - 1) = 0,
```

then inserting this supplied value into the empty Eq5 offset set gives

```text
insert T(C.point ell-1) Eq5Offsets_ell
  = {0}
  = IntervalValueSet_ell.
```

This last step is only supplied endpoint bookkeeping.  It does not prove that
Aoyagi's printed equations construct such a terminal branch, nor does it prove
terminal-minimum-label exactness.

For compatibility with adjacent terminal APIs, we also record the same supplied
coverage statement when the terminal equality is stated as

```text
T(C.point ell - 1) = Htilde'_ell.
```

Under the selected-width sum, `Htilde'_ell=0`, so this is the same finite-set
calculation with the endpoint written in upper-chain form.

## Lean Targets

```text
aoyagiLemma5Eq5OffsetValueSet_eq_empty_of_terminal
aoyagiHtildeIntervalValueSetNat_terminal_eq_singleton_zero_of_selectedSum
aoyagiLemma5Eq5_terminal_offsets_ne_intervalValueSetNat_of_selectedSum
aoyagiLemma5_suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat
aoyagiLemma5_suppliedTerminalUpper_Eq5_offsets_eq_intervalValueSetNat
```

## Kill Conditions

- Keep the selected-width sum and `a<=ell` explicit for terminal interval
  singletonness.
- Keep the terminal zero or terminal upper-endpoint source as a supplied
  equality.
- Do not infer that Eq3, Eq4, or Eq5 constructs the terminal-zero branch.
- Do not infer source-label legality, terminal-label exactness,
  all-coordinate endpoint realisation, injection, back-to-label coverage,
  Lemma 5 order count, normal crossings, or RLCT extraction.
