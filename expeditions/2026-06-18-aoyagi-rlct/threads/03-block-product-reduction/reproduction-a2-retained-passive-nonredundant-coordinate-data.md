# Reproduction - A2 Retained-Passive Nonredundant Coordinate Data

Date: 2026-06-26.

Status: pen-and-paper prerequisite for replacing the dummy-slot coordinate
object by an actual finite coordinate object.  This is still fixed-base
algebra only.

## Question

The bundled coordinate-data object

```text
RetainedPassiveCoordinateData
```

is convenient for calling the solved-family API, but it still stores three
non-coordinate slots:

```text
A1seed_0,
A3seed_last,
F2_last.
```

The first two are dummy placeholders ignored by the solved endpoint
constructors.  The last one is constrained to be zero.  The next coordinate
object should store only actual retained-passive coordinates.

## Nonredundant Fields

For `M+1` edges, keep the following fields:

```text
A1passive_q    for q : Fin M
F2_p           for p : Fin (M+1), interpreted as F2_{p.castSucc}
A3passive_q    for q : Fin M
C_p            for p : Fin (M+1)
Ctop
F3.
```

The intended index meanings are:

```text
A1passive_q = A1seed_{q.succ}          (all p != 0),
F2_p        = full F2_{p.castSucc}     (all non-final F2 slots),
A3passive_q = A3seed_{q.castSucc}      (all p != last edge).
```

For `A3passive_q`, the matrix row type is

```text
κ' (q.castSucc.succ),
```

because the corresponding edge is `q.castSucc : Fin (M+1)`.

When `M=0`, both passive families are empty.  This is correct: the unique edge
is both `0` and `last`, so the `A1` and `A3` seed entries are both solved
endpoint variables rather than stored passive coordinates.

## Embedding Into The Existing Bundle

Embed the nonredundant data into `RetainedPassiveCoordinateData` by filling
the non-coordinate slots canonically:

```text
A1seed_0       = 0,
A1seed_{q.succ}= A1passive_q,
fullF2_{p.castSucc}=F2_p,
fullF2_last    = 0,
A3seed_{q.castSucc}=A3passive_q,
A3seed_last    = 0,
C,Ctop,F3      unchanged.
```

The terminal `F2_last=0` side condition becomes definitional:

```text
toCoordinateData.F2 (Fin.last (M+1)) = 0.
```

The passive determinant-unit hypotheses become:

```text
IsUnit (A1passive q).det       for every q : Fin M.
```

These imply the side condition required by the existing bundled theorems:

```text
∀ p : Fin (M+1), p != 0 -> IsUnit (A1seed p).det,
```

because every nonzero `p` is `q.succ` with `q = p.pred hp`.

## Source Map And Readback

Define the nonredundant source map by projection:

```text
edgeMatrix(data) = data.toCoordinateData.edgeMatrix.
```

The existing bundled recoverable-readback theorem then gives:

```text
source-left: F2_0, Ctop, F3,
per-edge:    A1seed_p for p != 0,
             fullF2_{p.castSucc},
             A3seed_p for p != last,
             C_p.
```

Rewriting the embedding equations turns this into readbacks for the stored
nonredundant fields:

```text
topLeft(T_{q.succ})      = A1passive_q,
F2 readback at edge p    = F2_p,
lowerLeft(T_{q.castSucc})= A3passive_q,
schurResidual(T_p)       = C_p,
S_0.Ctop                = Ctop,
lowerLeft(S_0.L)        = F3,
-S_0.B                  = F2_0.
```

## Full Extensionality

If two nonredundant coordinate objects satisfy the passive unit hypotheses and
have equal edge families, then the existing recoverable extensionality theorem
for their embeddings proves equality of every stored field:

```text
A1passive = A1passive',
F2 = F2',
A3passive = A3passive',
C = C',
Ctop = Ctop',
F3 = F3'.
```

Unlike the previous bundled theorem, this is full equality of the
nonredundant coordinate records, because the dummy slots have been removed.

## Nonclaims

This does not define an open coordinate domain, topology, source-rank coverage,
source/image equality, measure pushforward, density/Jacobian accounting,
normal crossings, pole order, or RLCT extraction.  It also does not yet use
the centered active variable `X=Ctop-I`; it keeps `Ctop` directly, matching the
already-proved finite endpoint algebra.
