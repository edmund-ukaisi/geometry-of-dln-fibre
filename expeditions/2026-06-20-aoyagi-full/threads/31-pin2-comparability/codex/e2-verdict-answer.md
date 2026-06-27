**Verdict:** the cert’s joint `(T1,Y1)` Ψ is **broken for general endpoint frames**. Holding only raw

```text
P01 = A0·Y1 + Y0·T1
```

fixed is sufficient only when the endpoint action does not leak raw `(2,2)` into the framed read blocks.

With `U = reindex(P0)`, `V = reindex(QL)`, and

```text
ΔP = [[0, 0],
      [0, D]],   D = ΔP11 = -S0·(T1 - T1')
```

the framed read-block change is exactly

```text
(11): u12·D·v21
(12): u12·D·v22
(21): u22·D·v21
```

So for general invertible `U,V`, this is not zero. Your exact-rational failures are not numerical noise; they witness a genuine polynomial obstruction. The original Ψ is valid under the extra condition `u12 = 0` and `v21 = 0`, i.e. `P0` block-lower and `QL` block-upper in the chosen `r ⊕ (·−r)` split.

**Endpoint Frames**
No, the deepest-point frame facts do **not** guarantee those triangular structures.

The Lean-side frame theorem gives:

```text
layer 0: Qf(first) = I, Pf(first) is a left normal-form unit
last layer: Pf(last) = I, Qf(last) is a right normal-form unit
```

It does not give `Pf(first)` block-lower or `Qf(last)` block-upper. A normalizing frame need not be triangular. Even for

```text
A = [[1, 0],
     [0, 0]]
```

we have

```text
[[1, a],
 [0, b]] · A = A      with a ≠ 0
A · [[1, 0],
     [c, d]] = A      with c ≠ 0
```

so the normal-form/corner equation itself permits exactly the bad off-diagonal blocks. The existing `hcorner`/`hbexact` does not force triangularity; `hbexact` only says both sides read the same framed residual blocks.

**Correct Fix**
The minimal correct invariant is:

```text
Πreg( U · (P(Ψx) - P(x)) · V ) = 0
```

where `Πreg` reads the framed `(1,1),(1,2),(2,1)` blocks. It is **not** “raw `P01` fixed”.

For the current Ψ, since `ΔP` has only a raw `(2,2)` block, this invariant becomes the three equations above. For general endpoint frames, generically this forces `D = 0`, i.e. raw `P11` fixed.

Option A, “also hold `P11` fixed”, is sufficient for E2 but generically incompatible with E1 in the same two-slot `(T1,Y1)` action: with `P01` fixed, `P11` fixed says `S0·(T1' - T1)=0`, while E1 prescribes a nontrivial `T1' - T1` in general.

Option B is not sound. The shared reindex is already present in `hbexact`; it aligns the definitions but does not remove endpoint-frame leakage or imply triangularity.

For arbitrary endpoint frames, the product-level corrected form is:

```text
ΔP = U⁻¹ · [[0, 0],
            [0, C]] · V⁻¹
```

so the framed change lands only in unread `(2,2)`. Equivalently, if `U⁻¹ = ū`, `V⁻¹ = v̄`, and one wants raw `ΔP11 = D` with `ū22,v̄22` invertible, the necessary raw compensations are

```text
ΔP01 = ū12·ū22⁻¹·D
ΔP10 = D·v̄22⁻¹·v̄21
ΔP00 = ū12·ū22⁻¹·D·v̄22⁻¹·v̄21
ΔP11 = D
```

That cannot be realized by the current `(T1,Y1)`-only Ψ because it requires changing raw `P00` and `P10` in general.

So the sound paths are:

1. prove/choose endpoint frames with `P0` block-lower and `QL` block-upper, then the existing Ψ works; or
2. replace the bridge by an enlarged Ψ that preserves the **framed** reg blocks directly.

Under the current hypotheses, the cert’s E2 claim is false.