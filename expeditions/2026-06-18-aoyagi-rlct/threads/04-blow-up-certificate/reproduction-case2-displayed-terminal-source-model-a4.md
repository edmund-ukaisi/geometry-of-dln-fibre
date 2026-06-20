# A4 Case 2 Displayed Terminal Source Model

Status: reproduced the actual-width-exhausted source-domain condition for the
displayed Case 2 terminal candidate.  This is still a supplied source-order
model, not a construction of the full `(S+1,0)` transition.

## Source Anchor

Aoyagi PDF pp. 20-22 perform the displayed Case 2 pivot at
`(J+1,J+1)`.  In the notation used by the Lean files, the residual row and
column domains are

```text
rows    J+1 <= i <= prefixMinNat n S,
columns J+1 <= j <= n(S+1),
```

and the displayed pivot exists under

```text
J+1 <= prefixMinNat n (S+1).
```

At the terminal stop, Aoyagi writes the remaining product in a source-order
form with a diagonal weight matrix outside the next following matrix.  The
previous checkpoint formalised the candidate finite matrix product

```text
Wnext = blockdiag(Atop, [post.weight (J+1)]),
Cnext = [Ctop; C0],
terminal = (Wnext * Cnext) * F,
```

where `C0` is the top pivot row of `C' = Q^-1 C`.

## Pen-And-Paper Reproduction

There are two different facts in the terminal branch.

First, failed next continuation

```text
not (J+2 <= prefixMinNat n (S+1))
```

is enough for the finite matrix-entry ideal calculation: the post-pivot
lower-right block is empty on at least one side, so the lower rows of
`D''' * C'` contribute zero after the displayed pivot-first clearing.

Second, reading the resulting candidate as a stage-relabelled source-domain
object at `(S+1,0)` needs actual next-width exhaustion

```text
n(S+1) = J+1.
```

Indeed, the introduced labels after the displayed pivot at old state
`(S,J+1)` are

```text
s < S, plus layer S labels k <= J+1.
```

The labels at the stage-relabelled state `(S+1,0)` are

```text
s < S+1,
```

which includes all actual-width layer `S` labels

```text
1 <= k <= n(S+1).
```

Thus the two domains agree when `n(S+1)=J+1`.  This is exactly the content of
the Lean theorem
`introducedLabel_currentSucc_iff_succStage_zero_of_nextWidth_eq` and its
finite-set version.

Prefix exhaustion alone is not enough.  The terminal frontier can arise from

```text
prefixMinNat n S = J+1
```

while still having

```text
n(S+1) >= J+2.
```

In that case `(S,J+2)` is an actual-width label introduced at `(S+1,0)` but
not at `(S,J+1)`.

## Formalisation Shape

The Lean structure `Case2DisplayedSuppliedActualWidthTerminalSourceModel`
packages:

```text
Atop : Matrix old old R
Ctop : Matrix old tau R
F    : Matrix tau suffix R
actualWidth_exhausted : n(S+1) = J+1
```

The projections name the supplied candidate pieces:

```text
terminalWeightCandidate = blockdiag(Atop, [b0])
terminalCnextCandidate  = [Ctop; C0]
terminalProductCandidate = (terminalWeightCandidate * terminalCnextCandidate) * F
```

The model proves:

```text
not_next_cont :
  not (J+2 <= prefixMinNat n (S+1))

introducedLabelFinset L n S (J+1)
  = introducedLabelFinset L n (S+1) 0.
```

The final wrapper theorem applies the existing supplied displayed-boundary
entry-ideal theorem using
`model.not_next_cont_of_actualWidth_exhausted`.

## Boundaries

- `Atop`, `Ctop`, and `F` remain supplied.
- The model gives a finite label-domain equality only.  It does not construct
  a recurrence state or exponent state over `(S+1,0)`.
- It does not prove `[Ctop;C0]` is Aoyagi's source-produced `C'^(S+1)`.
- It does not prove chart production, chart coverage or regularity, Jacobian
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariance, or repair of the printed Case 2 vector mismatch.

## Kill Conditions

- Do not use prefix-width exhaustion in place of actual-width exhaustion for
  the source-domain relabel.
- Do not promote the finite introduced-label equality to transported
  recurrence or exponent post-data.
- Do not cancel the surviving pivot weight `post.weight (J+1)`.
