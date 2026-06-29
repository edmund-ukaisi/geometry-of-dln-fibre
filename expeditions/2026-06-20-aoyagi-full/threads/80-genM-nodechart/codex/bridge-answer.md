Short answer: **A yes, B yes, C yes**, with one precision: `B` is not literally independent of the pivot coordinate. It is **radial-free**: after `pivotBlowupOn`, `B` uses the pivot coordinate as an ordinary coordinate, and `det DB = a^2` is `u`-free.

For M222, write the radial map as:

```text
π(u,a,b,n,w0,w1,lf0,lf1)
  = (p,a,b,n,w0,w1,L0,L1)
  = (u,a,b,n,w0,w1,u lf0,u lf1)
```

and define:

```text
B(p,a,b,n,w0,w1,L0,L1) =
  [[a,   a n],
   [a b, a b n + p]],

  [[L0 - n w0, L1 - n w1],
   [w0,        w1]]
```

Then exactly:

```text
phiFlatLiveR1 M222 = B ∘ π
```

and

```text
det Dπ = u^2
det DB = a^2
det Dphi = a^2 u^2
```

So your finding (2) is correct. The additive `+u` is not an affine-radial obstruction. It is the pivot coordinate itself. The Schur coordinate extracts it cleanly:

```text
p = A00_11 - A00_10 * A00_01 / A00_00
  = (a b n + u) - (a b)(a n)/a
  = u
```

The local inverse for `B` is also explicit when `a != 0`:

```text
a  = A0_00
n  = A0_01 / A0_00
b  = A0_10 / A0_00
p  = A0_11 - A0_10 A0_01 / A0_00
w0 = A1_10
w1 = A1_11
L0 = A1_00 + n w0
L1 = A1_01 + n w1
```

So `B` is a local isomorphism on the engine-open chart `a != 0`, including at `u = 0`.

For B: yes, the delegation target should be **`genBlkFlatLiveR1`’s actual fixed-pivot/live-leaf blocks**, using `T222` only as a structural template. Do not ask the formalizer to prove `phiFlatLiveR1 = phi222`; that equality is false at the decoder level. The right proof shape is Schur-frame isolate pivot, shear off the `N W` leaf terms, then apply radial `pivotBlowupOn` to the live active coordinates.

For C: yes. For the fixed-pivot decoder, the fixed `E(0,0)=1` is not active. The active set is:

```text
{structPivot} ∪ {leaf free coords} ∪ {E-free coords excluding fixed E(0,0), if any}
```

At `(2,2,2)`, the E block is `1x1`, so there are no E-free leftovers. Thus active is exactly:

```text
{u, lf0, lf1}
```

cardinality `3 = minAdm(2,2,2)`, giving the radial determinant factor `u^(3-1) = u^2`.

The only caveat is logical: `det = a^2 u^2` alone would not prove the factorization. But here the explicit `B ∘ π` decomposition above does, and the determinant agrees with it exactly.