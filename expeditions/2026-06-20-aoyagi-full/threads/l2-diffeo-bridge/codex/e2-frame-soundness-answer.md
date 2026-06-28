**1. WHICH FRAMES ENTER P01 AT L=2**

Necessarily from the Lean facts you gave:

`P = (Pf 0) · (prod - B) · (Qf 1)`.

So `P01` is read through exactly the two generic endpoint frames:

- `Pf 0`: first layer left frame.
- `Qf 1`: last layer right frame.

The identity-boundary frames

- `Qf 0 = 1`,
- `Pf 1 = 1`

do not enter this framed product at L=2.

Inference from block multiplication: if

```text
Pf 0 = [ a  b ]
       [ c  d ]

Qf 1 = [ e  f ]
       [ g  h ]
```

then the top-right block of `Pf0 · M · Qf1` contains a term

```text
b · M11 · h
```

so a moved `(2,2)` block can leak into `P01` unless the relevant off-diagonal mixing is killed. Block-lower `Pf 0` means `b = 0`; block-upper `Qf 1` means `g = 0`.

**2. VERDICT**

**NEEDS-TRIANGULARITY.**

Given your added Lean facts, the generic frames do not drop out. The L=2 bridge with arbitrary `Pf 0` and `Qf 1` is insufficient for a sound E2 invariance statement.

The earlier general-frame failure applies directly here: `deepestEFull` reads `(P00 - 1, P01, P10)`, and those blocks are formed after multiplying by the generic `Pf 0` and `Qf 1`. The identity facts `Qf 0 = 1` and `Pf 1 = 1` are irrelevant to this read.

**3. IF NEEDS-TRIANGULARITY**

Minimal practical hypothesis for the bridge:

```text
Pf 0 is block-lower with respect to the r/rest split
Qf 1 is block-upper with respect to the r/rest split
```

i.e.

```text
(Pf 0)01 = 0
(Qf 1)10 = 0
```

with invertibility already supplied by membership in `GL`.

This is dischargeable at L=2 only if you instantiate the bridge using the explicitly constructed triangular normalizing frames. The corner-leading-block invertibility lets you construct a block-lower normalizer such as

```text
[ A11⁻¹              0 ]
[ -A21 · A11⁻¹       I ]
```

and, dually, the corresponding block-upper right normalizer. It does not prove that arbitrary existing generic frames `Pf 0` and `Qf 1` are triangular. So the bridge should either require these triangularity hypotheses, or be specialized to the constructed normalizer frames.