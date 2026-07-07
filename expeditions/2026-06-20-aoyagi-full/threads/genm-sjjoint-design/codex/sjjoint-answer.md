1. **VERDICT: joint-resolution-required.**

The stated IH is not enough as a black box. Even granting that the residual core is controlled by the redChain box integral, the binding cut uses essentially all redChain integrability slack. The extra Gram determinant pole cannot be paid for by Hölder or by a separate tail-chain IH call near the endpoint.

2. **Binding Arithmetic: `M=(3,3,3,3)`, `t*=2`**

Here
`p=M0-t=1`, `q=M1-t=1`, `a=pq=1`.

The values are:

```text
minAdm(3,3,3,3) = 6
minAdm(redChain 2 M) = minAdm(2,3,3) = 5
minAdm(tailChain M) = minAdm(3,3,3) = 7
```

Take `c' = 3 - ε`. Then after the corank atom,

```text
s = c' - a/2 = 3 - ε - 1/2 = 5/2 - ε.
```

The residual has the shape

```text
G · K^{-s}
```

with

```text
G = det(Q_b Q_b^T)^(-1/2) = ||Q_b||^(-1),
K ≈ redChain core.
```

The redChain IH gives integrability of `K^{-s}` only for

```text
s < 5/2.
```

If one tries Hölder with exponents `α, β`, then the redChain factor needs

```text
β s < 5/2,
β < (5/2)/(5/2 - ε).
```

Thus the conjugate exponent must satisfy

```text
α > (5/2)/ε.
```

But `G^α = ||Q_b||^{-α}` is controlled, at best, by the shorter chain `(1,3,3)` only when

```text
α/2 < minAdm(1,3,3)/2 = 3/2,
so α < 3.
```

Near the endpoint this is impossible: for `ε ≤ 5/6`, Hölder already fails. Even the over-generous fantasy of using the full tail threshold `minAdm(3,3,3)/2 = 7/2` would only give `α < 7`, still failing for `ε < 5/14`.

So the obstruction is not the value `minAdm(M)/2`; it is the lack of separable exponent slack at the binding cut.

3. **Precise Mechanism**

The shared object is the deeper tail product

```text
Z = A2 ··· A_{L-1}.
```

At `L=2`, the tail is a single free matrix, so `Q_p` and `Q_b` are disjoint row blocks of a free variable. The determinant pole

```text
Δ_b = det(Q_b Q_b^T)
```

can be analyzed independently from the pivot/red part.

At `L>=3`,

```text
Q_b = A1_b Z,
Q_p = A1_p Z.
```

The determinant divisor

```text
Δ_b = det((A1_b Z)(A1_b Z)^T) = 0
```

and the redChain core divisor, involving the quotient/projection of `A1_p Z` modulo the row span of `A1_b Z`, live over the same deeper factors `Z`. The IH for redChain sees only the vanishing of the red core. The IH for tail chains sees only ordinary box-product smallness, not the Gram rank-drop divisor, and for `q>1` it does not even control nonzero rank-deficient `Q_b`.

This looks **bounded Aoyagi-style**, not like a true wall: the determinant pole should be paid for by codimension along the joint rank strata. But proving that requires simultaneous monomial or normal-form bookkeeping for `Δ_b` and the red core. Treating them as independent black-box IH outputs loses the necessary correlation data.

4. **Most Likely Way This Verdict Could Be Wrong**

If there is an additional black-box theorem giving uniform determinant-weighted estimates for shorter products, or fiberwise redChain bounds with explicit dependence on the singular values/rank strata of the shared deeper product `Z`, then one could package the needed argument as “black-box.” But that theorem would already contain the simultaneous joint resolution in substance.