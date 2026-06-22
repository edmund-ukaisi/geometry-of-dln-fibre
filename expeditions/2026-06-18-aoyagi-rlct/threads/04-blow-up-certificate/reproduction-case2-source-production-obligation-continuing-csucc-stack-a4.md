# Reproduction - Case 2 obligation continuing Csucc stack

Date: 2026-06-22.

Status: finite consumer of a supplied source-production obligation.  This is
not source/chart production.

## Source Anchor

Aoyagi PDF pp. 21-22, Case 2, gives the displayed chart formula

```text
C'_J^(S+1) = Q^-1 C_J^(S+1)
```

and says that, in the continuing branch, the induction proceeds with `J`
increased.  The current Lean boundary records a supplied successor object
through

```text
SourceProductionObligation.Csucc_eq_formula :
  Csucc = case2DisplayedSourceSuccessorFollowingFactor ...
```

The existing continuing source-current stack theorem already proves the full
old-top/source-suffix matrix identity, but its right side is written with the
formula-level successor block.

## Finite Calculation

The current-row block of the supplied successor object is

```text
case2SourceCurrentFollowingBlock n S Csucc.
```

Using the obligation field `Csucc_eq_formula`, this block is definitionally the
same as

```text
case2SourceSuccessorFollowingBlock n hS hcont residual C.
```

Therefore the existing continuing stack theorem can be rewritten from
formula-level successor notation to supplied-`Csucc` notation:

```text
... * currentFollowingBlock(C) * sourceSuffix
  =
... * currentFollowingBlock(Csucc) * sourceSuffix.
```

The continuing branch still requires the nonempty-next-center hypothesis

```text
J+2 <= prefixMinNat n (S+1).
```

## Lean Targets

```text
SourceProductionObligation.continuing_Csucc_currentFollowingBlock_eq_formula
SourceProductionObligation.continuing_sourceCurrentStack_suppliedCsucc
```

## Nonclaims

This does not construct the obligation, `Csucc`, `C'^(S+1)`, the source
suffix, a successor chart family, coverage, transition regularity, coordinate
post-data, Jacobian arithmetic, normal crossings, pole order, termination,
RLCT, or repair of the printed Case 2 vector mismatch.

It does not derive `hnext`, does not make stopped branches exclusive, and does
not identify lower-tail algebra with full source production.
