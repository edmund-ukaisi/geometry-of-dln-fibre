# A2 with-following source-cylinder radius-free basepoint shrink

## Claim

For the continuous-at prior-density finite-integral wrapper, the selected-entry
signed-box radii do not appear in the conclusion.  Therefore the local
basepoint-in-signed-box shrink can choose a signed box around the basepoint
internally.

Concretely, for any selected-entry coordinate vector

```text
y : center -> R,
```

choose

```text
R i = |y i| + 1.
```

Then `0 < R i` for every `i`, and `y ∈ signedBoxSet R`.

## Pen-and-paper check

The signed box is

```text
signedBoxSet R = {y | for every i, -R i < y i and y i < R i}.
```

For `R i = |y i| + 1`, positivity is immediate from `0 <= |y i|`.
Membership follows from

```text
|y i| < |y i| + 1,
```

which is equivalent to

```text
-(|y i| + 1) < y i < |y i| + 1.
```

Thus every basepoint selected-entry coordinate lies in some positive signed
box.  Feeding this existential signed box into the already verified
basepoint-in-signed-box shrink removes the explicit `Rres`, `hRres`, and
`z0.1.yNext ∈ signedBoxSet Rres` inputs from the finite-integral wrapper.

## Boundary

This is an ergonomic local wrapper, not a new global coverage theorem.  It is
sound because the chosen signed-box radii are internal to the theorem and do
not occur in the conclusion.

Do not use this radius choice for statements where the signed box appears in
the conclusion, where the measure depends on the radii, or where a small-box
hypothesis such as `R i <= delta` is needed.  The chosen box is large enough
to contain the basepoint, not small.
