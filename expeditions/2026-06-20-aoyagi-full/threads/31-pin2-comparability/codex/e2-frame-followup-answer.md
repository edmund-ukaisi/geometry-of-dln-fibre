The correct E2 invariant is **only the three framed read blocks of `M̂` are unchanged**:

- `M̂.toBlocks₁₁`
- `M̂.toBlocks₁₂`
- `M̂.toBlocks₂₁`

The whole framed matrix need not be unchanged. In particular, `M̂.toBlocks₂₂` is not read by the energy, so it is allowed to move.

But the proposed shortcut

```text
hold raw P01 = A0·Y1 + Y0·T1 fixed
```

does **not** by itself imply the three framed read blocks stay fixed.

Reason: from the given algebra, `M̂` is obtained from the raw product by a fixed linear pre/post operation. Fixed does not mean block-preserving. If the endpoint matrices are general in the `r ⊕ (·−r)` decomposition, then for

```text
U = [[u11,u12],[u21,u22]]
V = [[v11,v12],[v21,v22]]
P = [[P00,P01],[P10,P11]]
```

the read blocks of `U P V` contain terms involving `P11`, for example:

```text
(UPV)11 includes u12·P11·v21
(UPV)12 includes u12·P11·v22
(UPV)21 includes u22·P11·v21
```

So, unless one has an additional fact that the relevant endpoint/framing maps kill those `P11` contributions, raw `(2,2)` can leak into framed `(1,1),(1,2),(2,1)`.

Therefore:

- **Fact from energy definition:** E2 only needs the three framed regular blocks fixed; framed `(2,2)` may move.
- **Inference from general block algebra:** holding only raw `P01` fixed is insufficient in general.
- **Sufficient raw invariant:** hold the raw product as a whole fixed. Since `P00` and `P10` are already independent of `Y1,T1`, this means requiring both

```text
P01' = P01
P11' = P11
```

So the certification “hold `P01` fixed” is valid only if there is an extra proven no-leakage lemma for the endpoint conjugation/framing. From the algebra provided, that no-leakage does not follow.