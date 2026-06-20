# A4 Case 2 Terminal Frontier Bridges

Status: reproduced two elementary bridges toward Aoyagi's stopped Case 2
terminal `C'^(S+1)` notation, without proving chart production.

## Source Anchor

On PDF pp. 21-22, after the displayed Case 2 `Q/P` calculation, Aoyagi
states that if the next continuation fails then

```text
D'''_J = (1,0,...,0)    or    D'''_J = (1,0,...,0)^t,
```

and the product is written in the advanced source order

```text
diag(b_1,...,b_J,b'_(J+1),...,b'_{M(S+1)})
  C'^(S+1) prod_{s=S+2}^L C^(s).
```

Here `M(S+1)` is the prefix minimum.  It is not the actual next width
`M^(S+1)` unless the actual-width side is the exhausted side.

## Pen-And-Paper Reproduction

Let

```text
muNext = M(S+1) = prefixMinNat n (S+1).
```

The displayed continuation and stop hypotheses are

```text
J+1 <= muNext,
not (J+2 <= muNext).
```

Therefore

```text
muNext = J+1.
```

So the source-row type already used by the candidate,

```text
{1,...,J+1},
```

is equivalent to the terminal prefix row type

```text
{1,...,M(S+1)}.
```

This is only a prefix-row statement.  In the row-exhausted and wide-next case
`M(S)=J+1<M^(S+1)`, the transported following factor `Q^-1 C_J^(S+1)` still
has actual rows beyond `J+1`; those rows are not part of the terminal
advanced prefix object `C'^(S+1)`.

The second bridge isolates the future chart-production obligation.  Suppose a
supplied terminal matrix `Cterm` indexed by `{1,...,J+1}` satisfies:

```text
Cterm(i,-) = C(i,-)                         for i=1,...,J,
Cterm(J+1,-) = top row of Q^-1 C_J^(S+1).
```

Then `Cterm` is exactly the existing terminal `C'` candidate.  Consequently
the terminal product candidate rewrites as

```text
(source terminal weight * Cterm) * F.
```

Lean packages these assumptions in `SuppliedTerminalCprimeBridge`.  The row
equations are assumptions in this bridge.  A later chart-production theorem
must prove them from source coordinates.

## Lean Shape

The terminal prefix row type and row equivalences are:

```text
case2SourceTerminalPrefixRowIndex
case2SourceTerminalRowEquivPrefix
case2SourceTerminalRowEquivPrefixOfNotNext
```

The prefix-row candidates are:

```text
case2DisplayedSourceTerminalWeightPrefixCandidate
case2DisplayedSourceTerminalCprimePrefixCandidate
case2DisplayedSourceTerminalProductPrefixCandidate
```

The prefix-row product theorem and source old-top/suffix wrapper are:

```text
case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_cprimePrefixCandidate_mul
exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalPrefixProduct_of_not_next_cont
```

The supplied terminal matrix handoff is:

```text
case2DisplayedSourceTerminalCprimeCandidate_oldRow
case2DisplayedSourceTerminalCprimeCandidate_pivotRow
SuppliedTerminalCprimeBridge
case2DisplayedSourceTerminalCprimeCandidate_eq_of_oldRows_pivotRow
case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_suppliedCterm_mul
SuppliedTerminalCprimeBridge.cprimeCandidate_eq
SuppliedTerminalCprimeBridge.terminalProduct_eq_weight_mul_Cterm_mul
SuppliedTerminalCprimeBridge.terminalPrefixProduct_eq_weight_mul_CtermPrefix_mul
exists_sourceOldTopSourceSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont
```

## Boundaries

- These are row-index and row-equation bridges only.
- They do not prove chart production of `C'^(S+1)`.
- They do not identify actual rows beyond `M(S+1)` with terminal prefix rows.
- They do not relabel recurrence/exponent domains except under the separate
  actual-width exhaustion theorem already proved.
- They do not prove chart coverage, coordinate regularity, Jacobian
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariance, automatic Case 2 gap/tail transport, or printed-vector repair.

## Kill Conditions

- Do not use prefix exhaustion as a substitute for actual-width exhaustion in
  introduced-label relabels.
- Do not claim that the supplied `Cterm` is source-produced until a later
  theorem proves the old-row and pivot-row equations from coordinates.
- Keep Aoyagi's terminal prefix rows `1..M(S+1)` distinct from actual next
  layer rows `1..M^(S+1)`.
