# Reproduction - Case 2 obligation Csucc projections

Date: 2026-06-22.

Status: finite projections from a supplied source-production obligation.

## Source Anchor

Aoyagi PDF pp. 21-22, Case 2.  The displayed chart operation gives the
formula-level successor following factor

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

The current Lean source-production frontier keeps this as a supplied
obligation:

```text
Csucc = case2DisplayedSourceSuccessorFollowingFactor n hS hcont residual C.
```

The following two projections both consume this equality.  The actual-width
projection also consumes the obligation's supplied terminal-row equality for
that stopped branch.  Neither projection constructs the successor object from
chart coordinates.

## Continuing Tail

The next same-stage following restriction is taken at `(S,J+1)`, so it starts
after row `J+1`.  The formula-level successor factor differs from `C` only at
row `J+1`; therefore the tail restriction is unchanged:

```text
case2SourceFollowingFactor(S,J+1,Csucc)
  = case2SourceFollowingFactor(S,J+1,C).
```

The Lean proof rewrites `Csucc` by the obligation field `Csucc_eq_formula`
and then applies the existing finite row-tail theorem
`case2SourceFollowingFactor_successorFollowingFactor_succ`.

## Actual-Width Stopped Rows

In the actual-width stopped branch, the branch hypothesis is

```text
n(S+1) = J+1.
```

The obligation supplies

```text
Cterm = originalRows(C).
```

Lean already proves that actual next-width exhaustion collapses the
formula-level successor following factor back to the old factor:

```text
case2DisplayedSourceSuccessorFollowingFactor ... C = C.
```

Thus `originalRows(C)` rewrites to original rows of the canonical successor
factor, and `Csucc_eq_formula` rewrites that canonical factor to the supplied
`Csucc`:

```text
Cterm = originalRows(Csucc).
```

This is distinct from the row-exhausted projection already landed.  The
row-exhausted hypothesis is `prefixMinNat n S = J+1`, and there row `J+1` is
original only as a row of `Csucc`, not necessarily as a row of old `C`.

## Lean Targets

Add projection theorems under `SourceProductionObligation`:

```text
SourceProductionObligation.continuing_Csucc_tail_eq_original
SourceProductionObligation.actualWidth_Cterm_eq_originalRows_Csucc
```

The actual-width theorem consumes only:

- `ob.actualWidth_Cterm_eq hwidth`;
- `case2DisplayedSourceSuccessorFollowingFactor_eq_original_of_width_next_eq`;
- `ob.Csucc_eq_formula`.

The continuing-tail theorem consumes only:

- `ob.Csucc_eq_formula`;
- `case2SourceFollowingFactor_successorFollowingFactor_succ`.

## Nonclaims

These do not construct the obligation, `Csucc`, `C'^(S+1)`, a suffix, a
successor chart family, chart coverage, transition regularity, corrected
post-data from coordinates, Jacobian arithmetic, normal crossings, pole order,
termination, RLCT extraction, or repair of the printed Case 2 vector mismatch.

They do not derive branch hypotheses from failed continuation, do not make
stopped branches exclusive, and do not source-produce the successor following
factor.
