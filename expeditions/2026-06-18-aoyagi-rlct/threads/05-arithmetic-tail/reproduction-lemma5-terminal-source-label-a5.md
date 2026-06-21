# Reproduction - Lemma 5 Terminal Source Label

Status: elementary source-label bookkeeping; formalisation-ready.

This slice isolates the source-label legality of the terminal singleton used
in the terminal Eq5 coverage wrapper.  It does not construct the terminal
source branch.  The source-coordinate value remains supplied as

```text
T(C.point ell - 1) = 0.
```

## Terminal Source Index

Assume `1 <= ell`.  The selected cutpoints are positive and strictly
increasing.  Since `0 < ell`, we have

```text
C.point 0 < C.point ell.
```

Also `1 <= C.point 0`, hence

```text
2 <= C.point ell.
```

Therefore

```text
1 <= C.point ell - 1.
```

If the selected terminal point lies within the source range,

```text
C.point ell <= L + 1,
```

then subtracting one gives

```text
C.point ell - 1 <= L.
```

Thus the terminal source coordinate is in the layer range `1..L`.

## Terminal Label

Take terminal label

```text
k = 1.
```

The lower label bound is immediate.  The upper label bound is exactly the
explicit width-positivity hypothesis

```text
1 <= n(C.point ell),
```

because

```text
(C.point ell - 1) + 1 = C.point ell.
```

Consequently

```text
actualWidthLabel L n (C.point ell - 1) 1.
```

At state

```text
(S,J) = (C.point ell - 1, 1),
```

the same actual label is introduced by the current-layer rule, since the
source layer is equal to the state layer and `1 <= 1`.

## Terminal Value

Under the selected-width sum and `a <= ell`, the terminal same-coordinate
Htilde interval is already proved to be the singleton

```text
aoyagiHtildeIntervalValueSetNat ell a M m ell = {0}.
```

Therefore the supplied terminal source-coordinate equality

```text
T(C.point ell - 1) = 0
```

implies

```text
T(C.point ell - 1)
  in aoyagiHtildeIntervalValueSetNat ell a M m ell
```

and also

```text
T(C.point ell - 1) = (1 : Int) - 1.
```

Combining these facts gives terminal interval membership, the `k-1` value
identity for `k=1`, and membership of `(C.point ell - 1,1)` in the introduced
label finset at state `(C.point ell - 1,1)`.

## Nonclaims

- No terminal source branch is constructed.
- No equality between a supplied branch chain and the terminal source
  coordinate is constructed.
- No terminal-minimum-label exactness, classifier coverage, branch-label
  injectivity, back-to-label coverage, pole order, normal crossings, or RLCT
  extraction is proved.
