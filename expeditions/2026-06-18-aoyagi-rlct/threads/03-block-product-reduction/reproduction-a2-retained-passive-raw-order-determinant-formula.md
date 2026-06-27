# A2 retained-passive raw-order determinant formula

Status: controller reproduction with independent endpoint-convention check.

## Scope

This note reproduces the determinant of the retained-passive p.13 raw-order
coordinate map already formalised in Lean.  It is a calculation in the local
coordinate system
`RetainedPassiveNonredundantCoordinateData.TopologyTuple`, not a new
source-prior theorem.

The PDF text was not freshly extractable in the current VM: `pdftotext`,
`pdfinfo`, `mutool`, and `qpdf` are absent, and no Python PDF reader is
installed.  The source-fidelity checkpoint for this note is therefore:
compare this retained-passive chart calculation against Aoyagi p.13 by a
manual/PDF-readable pass before a final source claim depends on it.

## Lean objects being reproduced

Let

```text
z : TopologyTuple rho kappa' R
data := ofTopologyTuple z
coord := data.toCoordinateData
A p := coord.solvedA1 p
G p := coord.solvedA3 p
F i := coord.F2 i
C p := coord.C p
```

The product tuple order is

```text
(A1passive, F2, A3passive, C, Ctop, F3).
```

The determinant chart hypothesis is exactly

```text
IsUnit data.Ctop.det and forall p : Fin M, IsUnit (data.A1passive p).det.
```

The solved top-left family is

```text
A 0 = Tail^{-1} * Ctop,
A (p.succ) = A1passive p,
Tail = retainedPassiveA1TailAfterFirst data.A1seed
     = A_M * ... * A_1
```

with the empty product `Tail = 1` when `M = 0`.

The solved lower-left final block is

```text
G (Fin.last M) = -(F3 - earlyTail) * LastTop,
LastTop =
  residualFactorProduct A (Fin.last (M+1)) (Fin.last M).castSucc
    (Fin.last M).castSucc.le_last.
```

Lean references:

- `TopologyTuple`: `RetainedPassiveCoordinatesTopology.lean:29`.
- `topologyTupleEdgeRawOrder`: `RetainedPassiveCoordinatesTopology.lean:360`.
- component formulas: `RetainedPassiveCoordinatesTopology.lean:370`,
  `:389`, `:410`, `:427`, `:445`, `:464`.
- `retainedPassiveA1TailAfterFirst`: `RetainedPassiveCoordinates.lean:1203`.
- `retainedPassiveSolvedA1`: `RetainedPassiveCoordinates.lean:1601`.
- `retainedPassiveSolvedA3`: `RetainedPassiveCoordinates.lean:1725`.
- `residualFactorProduct` and endpoint lemmas:
  `ProductReduction.lean:1983`, `:2013`, `:2037`, `:2051`.
- current abstract determinant API:
  `RetainedPassiveCoordinatesDerivative.lean:2664`, `:2698`, `:2742`,
  `:2761`.
- endpoint check: xhigh read-only scout `Boole the 4th`, 2026-06-27,
  confirmed `LastTop = solvedA1 (Fin.last M)`, hence `LastTop = Ctop`
  when `M = 0`.

## Raw block formulas

For each edge `p : Fin (M+1)`, the edge-family output of
`topologyTupleEdgeRawOrder z` has blocks

```text
Y11_p = A p + F (p.succ) * G p,
Y12_p = - A p * F p.castSucc
        + F (p.succ) * (C p - G p * F p.castSucc),
Y21_p = G p,
Y22_p = C p - G p * F p.castSucc.
```

The tuple readout stores:

```text
Y11_1, ..., Y11_M     in A1passive output,
Y12_0, ..., Y12_M     in F2 output,
Y21_0, ..., Y21_{M-1} in A3passive output,
Y22_0, ..., Y22_M     in C output,
Y11_0                 in Ctop output,
Y21_M                 in F3 output.
```

The terminal convention is `F (M+1) = 0`.

## Elementary determinant decomposition

The map is triangular after replacing the displayed block variables by the
edge-local pairs `(Y11_p, Y21_p)` before `(Y12_p, Y22_p)`.

### The `Ctop` source variable

Only `A 0 = Tail^{-1} * Ctop` has a non-translation dependence on the active
top source variable.  Thus the `rho x rho` variable `Ctop` contributes left
multiplication by `Tail^{-1}` on a space with `|rho|` columns:

```text
absdet(Ctop contribution) = |det Tail|^(- |rho|).
```

For `M = 0`, `Tail = 1`, so this factor is `1`.

### Each `F_p, C_p` pair

Fix `p : Fin (M+1)`.  With `(Y11_p, Y21_p)` already regarded as earlier
coordinates, the transformation

```text
(F_p, C_p) |-> (Y12_p, Y22_p)
```

has block form

```text
F_p |-> -A p * F_p - F (p.succ) * G p * F_p
C_p |->              F (p.succ) * C_p

F_p |->             -G p * F_p
C_p |->              C_p.
```

Equivalently, in block matrix notation it is

```text
[ -(A p + F (p.succ) * G p)    F (p.succ) ]
[          -G p                    1       ].
```

Its Schur complement against the lower-right identity block is `-A p`.
Hence the absolute determinant contribution is

```text
|det (A p)|^(|kappa' p.castSucc|).
```

This includes `p = 0`, where `A 0 = Tail^{-1} * Ctop`.

### The final `F3` source variable

The output `F3` coordinate is `Y21_M = G M`.  The only non-translation
dependence on the source variable `F3` is

```text
F3 |-> - F3 * LastTop.
```

This is right multiplication by `LastTop` on a matrix space with
`|kappa' (Fin.last (M+1))|` rows, so its absolute determinant contribution is

```text
|det LastTop|^(|kappa' (Fin.last (M+1))|).
```

The endpoint convention has now been checked against the Lean definitions:

- for `M > 0`, `LastTop` should reduce to the final passive block `A M`;
- for `M = 0`, `LastTop` should reduce to `A 0 = Ctop`, because
  `Tail = 1`.

Thus `LastTop` is not the same object as `Tail`.  In the single-edge case the
`Ctop`-solve tail is empty, but the final lower-left solve still right
multiplies by `Ctop`.

### Shears, translations, and product reordering

The other dependencies are additions of previously exposed coordinates,
coordinate shears, or product-coordinate permutations.  They contribute
determinant `+1` or `-1`; the absolute determinant is unchanged.

## Proposed formula

Let

```text
r      = Fintype.card rho,
k_i    = Fintype.card (kappa' i),
Tail   = retainedPassiveA1TailAfterFirst coord.solvedA1,
LastTop =
  residualFactorProduct coord.solvedA1
    (Fin.last (M+1)) (Fin.last M).castSucc
    (Fin.last M).castSucc.le_last.
```

Then, up to the sign from coordinate permutations and negative multipliers,

```text
absdet D(topologyTupleEdgeRawOrder)(z)
  =
    |det Tail|^(-r)
    * |det LastTop|^(k_(M+1))
    * product_{p : Fin (M+1)} |det (A p)|^(k_p).
```

The formula is intended on `topologyTupleDetChartSet`, where all displayed
determinants are nonzero.  The current Lean library already proves the weaker
facts that this absolute determinant is positive and continuous on the chart;
it does not yet prove this explicit factorization.

## Lean target suggested by the reproduction

The first reusable API gap was the rectangular matrix determinant lemma:

```text
det (X |-> A * X) = det(A)^(number of columns),
det (X |-> X * B) = det(B)^(number of rows).
```

This has now landed in
`lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean` as

```text
linearMap_det_mulLeftLinearMap
linearMap_det_mulRightLinearMap
```

The proof uses a column-wise linear equivalence, `LinearMap.det_pi`, and
transpose for the right-multiplication version.

The remaining explicit retained-passive determinant theorem should be proved by
factoring the derivative into:

1. a product-coordinate permutation;
2. the `Ctop` left-multiplication factor;
3. edge-local `(F_p,C_p)` Schur-complement factors;
4. the final `F3` right-multiplication factor;
5. determinant-one shears/translations.

## Kill conditions

- If the PDF p.13 source chart uses a different independent coordinate order
  or a different retained-passive source convention, this note is only a Lean
  chart calculation and not source-fidelity evidence.
- If `LastTop` reduces to the identity in the `M = 0` Lean convention, the
  final `F3` factor above is wrong in the one-edge case.  This has been
  checked against the current Lean definitions and does not happen:
  `LastTop = Ctop` for `M = 0`.
- If `LastTop` is identified with `retainedPassiveA1TailAfterFirst`, the
  final `F3` factor is wrong.  `retainedPassiveA1TailAfterFirst` is the
  first-edge solve tail; `LastTop` is the one-edge terminal factor in
  `retainedPassiveSolvedA3`.
- If the derivative factorization cannot be made triangular without replacing
  the source variables by target variables, the proposed formula may be the
  determinant of a different coordinate change.
- If a future Lean proof of the edge-local `(F_p,C_p)` block determinant gives
  `Y11_p` rather than `A p` as the Schur factor, the edge-local reproduction
  above has chosen the wrong block elimination direction.
- This formula is not a source-prior pushforward theorem, not a selected-entry
  source chart theorem, not source-rank coverage, not normal crossings, and not
  RLCT extraction.
