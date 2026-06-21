# Reproduction - Lemma 5 Supplied Terminal Candidate Family

Status: supplied-data boundary; ready for a narrow Lean package.

This note packages the branchwise data needed to read the supplied Lemma 5
branches as terminal candidates in the generic exponent-certificate API.

## Supplied Data

Start from a full supplied admissible Lemma 5 branch family.  For each tagged
branch `x`, supply:

```text
branchS(x), branchK(x)
```

as the source label attached to that branch.  Also supply:

1. the label is introduced at the current exponent-certificate state;
2. the least value of its exponent vector is zero;
3. the numerator attached to that label is the Lemma 3 free-count expression
   for the branch:

```text
numerator(branchS x, branchK x) = A(n+1,a,b_x).
```

Here

```text
b_x = aoyagiLemma4FreeHighCount n M m (fullH x).
```

The introduced-label field includes actual source-label legality through the
generic `introducedLabel` predicate.

## Consequences

The previous supplied terminal-numerator bridge proves

```text
terminalExponent(branchS x, branchK x)
  = a*(n+1)*((n+1)-a).
```

The new package theorem records the three branchwise facts together:

```text
introducedLabel(branchS x, branchK x),
leastValue(branchS x, branchK x)=0,
terminalExponent(branchS x, branchK x)=a*(n+1)*((n+1)-a).
```

The package also inherits the supplied Lemma 5 finite branch count

```text
|fullBranches| = a*(n+1-a)+1.
```

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily
AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches
AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card
AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalLeastValue_zero
AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalExponent_eq_minNumerator
AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalCandidateData
```

## Kill Conditions

- Do not infer the branch labels from equations `(3)`, `(4)`, or `(5)`.
- Do not treat this as a source-backed proof of terminal `tilde t=0`; terminal
  least value zero is a supplied field.
- Do not claim that every terminal minimizer is in this supplied family.
- Do not derive pole order from the branch count without supplied
  no-extra-minimizer/injectivity data and the normal-crossing extraction
  interface.

## Nonclaims

- No displayed-vector construction is proved.
- No chart coverage or chart regularity theorem is proved.
- No `lambda`, pole-order, normal-crossing, or RLCT theorem is proved.
