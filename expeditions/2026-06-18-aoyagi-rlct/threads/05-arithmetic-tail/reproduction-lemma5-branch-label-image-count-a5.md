# Reproduction - Lemma 5 Branch-Label Image Count

Status: supplied-data boundary; ready for a narrow Lean wrapper.

This note records the finite-set calculation that separates a tagged supplied
branch count from a distinct supplied-label count.

## Setup

Start with a supplied terminal-candidate family.  Its tagged branch set is

```text
B = fullBranches.
```

Each tagged branch has a supplied source label

```text
ell(x) = (branchS x, branchK x).
```

Lean represents this label as the existing source-label dependent pair
`Sigma.mk (branchS x) (branchK x)`, matching `introducedLabelFinset`.

Define the finite label image

```text
I = ell(B).
```

This is only the image of the supplied candidate branches.  It is not the set
of all terminal minimizers unless a separate coverage/no-extra-minimizer
statement is supplied.

## Cardinality Calculation

Assume the branch-to-label map is injective on the supplied branch set:

```text
x,y in B and ell(x)=ell(y)  ==>  x=y.
```

Then the map `ell : B -> I` is bijective:

1. Surjectivity is true by the definition of image.
2. Injectivity is the supplied hypothesis restricted to `B`.

Therefore

```text
|I| = |B|.
```

The previous supplied terminal-candidate theorem gives

```text
|B| = a*(n+1-a)+1.
```

Combining the two equalities gives the distinct supplied-label image count:

```text
|I| = a*(n+1-a)+1.
```

Lean implements the finite bijection step with
`Finset.card_image_of_injOn`.

The supplied introduced-label field also gives

```text
ell(x) in introducedLabelFinset L width S J
```

for every `x in B`, hence

```text
I subset introducedLabelFinset L width S J.
```

## Candidate Data on the Image

If `label in I`, then by image membership there is a tagged branch
`x in B` with

```text
label = ell(x).
```

The branchwise supplied terminal-candidate theorem already gives

```text
introducedLabel(ell(x)),
leastValue(ell(x))=0,
terminalExponent(ell(x))=a*(n+1)*((n+1)-a).
```

Substituting `label = ell(x)` transfers those three facts to every label in
the image.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_mem_introducedLabelFinset
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_subset_introducedLabelFinset
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_eq_fullBranches_card_of_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_terminalCandidateData
```

## Kill Conditions

- Do not infer branch-label injectivity from Aoyagi's printed equations.
- Do not identify `branchLabelImage` with the full terminal-minimizer set.
- Do not call the image count a pole order without no-extra-minimizer coverage
  and the normal-crossing extraction interface.
- Do not use this to prove source construction of labels or terminal
  `tilde t=0`.

## Nonclaims

- No source-backed label injectivity is proved.
- No no-extra-minimizer theorem is proved.
- No `lambda`, pole-order, normal-crossing, or RLCT theorem is proved.
