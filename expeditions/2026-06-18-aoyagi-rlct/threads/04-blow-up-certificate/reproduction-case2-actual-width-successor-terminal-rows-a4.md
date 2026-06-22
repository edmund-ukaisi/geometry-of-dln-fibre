# Pen-and-paper reproduction - A4 Case 2 actual-width successor terminal rows

Status: reproduced, xhigh-checked, and formalised.

## Source Anchor

Aoyagi PDF pp. 21-22, Case 2 stopped branch.  This checkpoint concerns only
the actual next-width exhausted case

```text
n(S+1)=J+1.
```

## Reproduction

The existing actual-width supplied-following boundary proves the stopped
terminal product with terminal rows written as the original source rows:

```text
ideal(source-chart left side * F)
  =
ideal((terminalWeight * originalRows(C)) * F),
```

and carries the relabelled `(S+1,0)` level and exponent certificates.

The formula-level successor following factor is

```text
Csucc(j,a) =
  if j = J+1 then top row of (Q^-1 C) at a
  else C(j,a).
```

Under actual next-width exhaustion, the post-pivot correction sum in the top
row of `Q^-1 C` is empty.  Hence

```text
Csucc = C.
```

Therefore

```text
originalRows(Csucc) = originalRows(C),
```

and the same actual-width supplied-following boundary can be stated as

```text
ideal(source-chart left side * F)
  =
ideal((terminalWeight * originalRows(Csucc)) * F).
```

The following product `F` remains arbitrary supplied data.

## Lean Name

```text
sourceChart_actualWidth_terminalOriginalRowsSuccFollowingSuppliedSuffixBoundary
```

## Boundary Checks

- This is API alignment only; it is a one-rewrite actual-width restatement.
- It uses exactly actual next-width exhaustion `n(S+1)=J+1`.
- It does not apply to row exhaustion, failed continuation alone, or a broad
  stopped-frontier condition.
- No source-suffix, identity-following, finite-center, or frontier-package
  variants were added.

## Kill Conditions

- Do not call this source/chart production of `Csucc`, `F`, source suffixes,
  old-top rows, or a full successor `C'^(S+1)`.
- Do not infer successor chart-family data, chart coverage, transition
  invariance, Jacobian arithmetic, normal crossings, pole order, termination,
  RLCT, or repair of the printed Case 2 vector mismatch.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.
