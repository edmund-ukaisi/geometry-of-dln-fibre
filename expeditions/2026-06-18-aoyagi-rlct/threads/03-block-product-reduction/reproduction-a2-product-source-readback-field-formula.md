# A2 product source-readback field formula reproduction

Date: 2026-06-30.

## Scope

This note is only the finite p.13 product-coordinate algebra.  It is independent
of the quiver paper.  It does not prove source-prior transport, Haar transport,
normal crossings, pole order, or RLCT extraction.

## Calculation

Consider a chain with at least two p.13 product-coordinate edges.  Write the raw
edge family as

```text
E_0        = [ Ctop   -Ctop F2 ; 0    C_0 ],
E_p        = [ I       0       ; 0    C_p ]       for 0 < p < last,
E_last     = [ I       0       ; -F3  C_last ].
```

The deterministic source-readback suffix recursion visits edges from right to
left.  At the right endpoint, the terminal suffix state has `B = 0`,
`Ctop = I`, `D = I`, and `L = I`.  The transformed edge is already

```text
[ I  0 ; -F3  C_last ].
```

After this step the suffix state has

```text
B = 0,
Ctop = I,
L = [ I 0 ; F3 I ],
D = C_last.
```

Every middle edge has transformed shape

```text
[ I 0 ; 0 C_p ],
```

because the incoming suffix state still has `B = 0`.  Therefore each middle
step preserves `B = 0`, `Ctop = I`, and

```text
L = [ I 0 ; F3 I ],
```

while multiplying the residual `D` by the corresponding `C_p`.

At the left endpoint the incoming tail state still has `B = 0`, so the
transformed edge is exactly

```text
[ Ctop  -Ctop F2 ; 0  C_0 ].
```

The left step changes the suffix fields to

```text
B = -F2,
Ctop = Ctop,
L = [ I 0 ; F3 I ].
```

Consequently the source-readback fields are:

```text
A1passive_p = I              for every passive top-left slot,
F2_0         = F2,
F2_p         = 0              for p > 0,
A3passive_p = 0              for every retained passive lower-left slot,
C_p          = the supplied residual factor C_p,
Ctop         = the supplied Ctop,
F3           = the supplied F3.
```

The sign check is important.  The right endpoint stores `-F3` as the lower-left
block of the transformed edge, but the readback field `F3` is read from the
lower-left block of the accumulated lower-unitriangular suffix matrix `L`,
where the step has converted `-F3` into `+F3`.

## Consequence

The product-coordinate edge family is not a full inverse to the original
passive theta data by itself.  Its source-readback overwrites the retained
passive `A1passive` and `A3passive` fields with `I` and `0`; it keeps only the
p.13 regular variables `Ctop`, `F2`, `F3` and the residual factors `C_p`.
This is the expected p.13 suspension algebra and is not a source-prior theorem.
