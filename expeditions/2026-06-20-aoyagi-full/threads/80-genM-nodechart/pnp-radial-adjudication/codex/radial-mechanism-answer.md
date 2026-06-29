**Q-A Verdict: needs hypothesis, but then forced.**

Let the chart variables be `(u, r_1, ..., r_D, z)`, where the `r_i` are exactly the free scalar entries of all `Rmat_k` and `Rfin` blocks, excluding the pivot itself. Under the stated recursion and assuming `Bmat_k`, `Nblk_k`, `Wblk_k`, and the internal K-core coordinates are all `u`-independent and disjoint from the `R` variables, every chart output has the form

```text
h_j(z)              or
h_j(z) + u * r_i
```

because:

```text
C_L = u * Rfin
C_k = Bmat_k * chainQ(Nblk_k) + u * Rmat_k
A_k = [ C_{k+1} - Nblk_k * Wblk_k ; Wblk_k ]
```

and `C_{k+1}` is inserted additively, not multiplied by later blocks.

So the Jacobian columns for the `r_i` variables each carry a factor `u`. Pulling those factors out gives

```text
det Dphi = u^D * G
```

where `D = # {free scalar entries in all u-scaled R blocks}`.

Moreover, under the same hypothesis, `G` is `u`-free: after the `u` factors are pulled from the `r_i` columns, the remaining Jacobian entries involve only `r_i` and the non-radial coordinates.

This can fail if any supposedly non-radial block depends on `u`, or if an `R` coordinate is reused inside `Bmat`, `Nblk`, or `Wblk`. Then terms like `u * r_i * n_j`, `u * b_j`, or even `u^2 * r_i` can enter the Jacobian, and the quotient by `u^D` need not be `u`-free.

So for Lean, the clean theorem should not merely assume “`u` appears linearly”; it should assume something like:

```text
all chart outputs are u-free except for additive terms u * r_i,
with the r_i disjoint from the remaining coordinates.
```

Then the determinant factorization is a proof, not a heuristic.

---

**Q-B Verdict: not forced by Q-A alone; forced only if the chart is really an achiever chart for a min-codimension stratum.**

The determinant argument proves:

```text
Jacobian exponent = # u-scaled free R entries.
```

It does not by itself prove:

```text
1 + # u-scaled free R entries = minAdm(M).
```

That identity is geometric. `minAdm(M)` counts the codimension of the deepest/minimal achiever stratum selected by the Aoyagi-style peeling recursion. If the chart is built by blowing up exactly that codimension-`minAdm(M)` center, then there are `minAdm(M)` normal coordinates. One is chosen as the pivot `u`; the remaining `minAdm(M) - 1` normal coordinates are radialized as `u * r_i`. Hence

```text
# u-scaled free entries = minAdm(M) - 1.
```

That is a proof conditional on the chart construction being known to select the minimal achiever stratum and the `R` blocks being exactly the non-pivot normal coordinates.

It is not forced by the recursion shape alone. For example, even at `M = (2,2,2)`, the minimal product-zero stratum has codimension `3`, matching the observed `D = 2`. But if one instead built a non-achiever chart around the smaller rank stratum where one factor is zero, the center has codimension `4`, so a radial chart would have `D = 3`, while `minAdm(2,2,2) = 3`. The determinant would then carry `u^3`, not `u^2`, because the chart is resolving a non-minimal boundary.

So the three examples are not mere numerology, but the identity belongs to the “this is an achiever/minimal chart” theorem, not to the Jacobian-factor theorem alone.

---

**Q-C Verdict: forced no, under the stated recursion and disjointness hypotheses.**

From the displayed recursion, `u` enters only in the additive summands

```text
u * Rfin
u * Rmat_k
```

and those summands are inserted directly into `A_k` through `C_{k+1}`. The later kept/lift split uses

```text
C_{k+1} - Nblk_k * Wblk_k
```

so `C_{k+1}` is not multiplied by `Nblk_k` or `Wblk_k`. Therefore an `R` entry contributes to a chart output as exactly

```text
u * r_i
```

not as `u * r_i * x_j`.

Also, because `C_k` is not recursively multiplied into later `Bmat` or `chainQ` terms, there is no mechanism producing `u^2`.

Thus, with `Bmat`, `Nblk`, `Wblk`, and K-core coordinates independent of `u`, and with the `R` variables disjoint, nonlinear radial terms cannot occur. The single pivot blow-up model is structurally justified.

It could only fail if the implementation violates those hypotheses, for example by letting the pivot coordinate live inside an LDU/K-core block, or by reusing an `R` coordinate inside `Nblk` or `Wblk`. Then `Bmat * chainQ` or `Nblk * Wblk` could generate products involving `u`. But that is outside the recursion as stated.