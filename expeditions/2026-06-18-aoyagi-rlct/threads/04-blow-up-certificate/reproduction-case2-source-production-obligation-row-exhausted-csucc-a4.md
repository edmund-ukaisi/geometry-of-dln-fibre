# Reproduction - Case 2 obligation row-exhausted Csucc rows

Date: 2026-06-22.

Status: finite projection from a supplied source-production obligation.

## Source Anchor

Aoyagi PDF pp. 21-22, Case 2.  The displayed chart operation gives the
formula-level successor following factor

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

The row-exhausted stopped branch keeps the terminal rows in transported-prefix
form when the branch hypothesis is

```text
prefixMinNat n S = J+1.
```

This is not the actual-width exhaustion hypothesis `n(S+1)=J+1`.

## Finite Calculation

The row-exhausted field of `SourceProductionObligation` supplies

```text
Cterm = transportedRows(C).
```

The same obligation also supplies the formula equality

```text
Csucc = case2DisplayedSourceSuccessorFollowingFactor n hS hcont residual C.
```

Lean already proves

```text
originalRows(case2DisplayedSourceSuccessorFollowingFactor ... C)
  = transportedRows(C).
```

Therefore, by symmetry of that row equality and by the supplied formula for
`Csucc`,

```text
Cterm = originalRows(Csucc).
```

This is the precise row-exhausted reading: row `J+1` is original as a row of
the supplied successor factor `Csucc`, because `Csucc(J+1,-)` is the top row
of `Q^-1 C`; it is not asserted to equal the old row `C(J+1,-)`.

## Lean Target

Add a projection theorem under `SourceProductionObligation`:

```text
SourceProductionObligation.rowExhausted_Cterm_eq_originalRows_Csucc
```

It should consume only:

- `ob.rowExhausted_Cterm_eq hrow`;
- `case2DisplayedSourceTerminalOriginalRows_successorFollowingFactor`;
- `ob.Csucc_eq_formula`.

## Nonclaims

This does not construct the obligation, `Csucc`, `C'^(S+1)`, a suffix, a
successor chart family, chart coverage, transition regularity, corrected
post-data from coordinates, Jacobian arithmetic, normal crossings, pole order,
termination, RLCT extraction, or repair of the printed Case 2 vector mismatch.

It does not derive `hrow` from failed continuation, does not make stopped
branches exclusive, and does not relabel row-exhausted wide-next data to
`(S+1,0)`.
