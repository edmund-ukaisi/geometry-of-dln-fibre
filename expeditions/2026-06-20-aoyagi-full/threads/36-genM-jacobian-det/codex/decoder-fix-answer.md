**Q1**

FACT: each Schur frame has the exact factorization
```text
C = [[K, K N],
     [X K, X K N + u E]]
  = [[I, 0], [X, I]]
    [[K, 0], [0, u E]]
    [[I, N], [0, I]].
```

So its Schur residual is exactly `u E`. If the chain recursion telescopes the full product to
```text
A_0 ... A_{L-1} = u H
```
with no further common `u` forced, then
```text
F(phi(x)) = ||u H||_F^2 = u^2 ||H||_F^2.
```

INFERENCE: the rate survives as a divisibility/rate statement if `H` is generically nonzero. The “unit” claim is only valid on chart regions where `||H||^2` is not vanishing identically.

Verdict: **Yes, the rate can survive: the product has one explicit `u`, hence `F = u^2 U`. This says nothing about the Jacobian.**

**Q2**

FACT: because `Rfin := 0`, any flat coordinates assigned to those leaf residual slots do not appear in any output matrix entry. If there are `r > 0` such unused coordinates, then after permuting columns,
```text
D phi = [ *  *  0_{N x r} ],
```
so
```text
rank D phi <= N - r < N,
det D phi = 0
```
identically, including off the hyperplane `{u = 0}`.

FACT: even ignoring the unused-slot defect, the no-fixed-pivot active block is off by one. For `m` residual entries all treated as free entries,
```text
(e_1, ..., e_m), u = e_1
  -> (u e_1, u e_2, ..., u e_m)
   = (u^2, u e_2, ..., u e_m),
```
has Jacobian determinant
```text
2 u^m.
```
With a separate identity pivot output it similarly contributes `u^m` for `m` scaled residual entries. The desired `u^{m-1}` only comes from
```text
(u, a_2, ..., a_m) -> (u, u a_2, ..., u a_m),
```
where the pivot scales a fixed `1` direction.

Verdict: **for the described layered decoder, `|det Dphi| = 0` identically. The `|u|^m` behavior is the nondegenerate “no fixed 1” prototype, but the actual chart is rank-deficient.**

**Q3**

FACT: composing a degenerate decoder with a radial factor cannot fix the determinant:
```text
det D(S ∘ R) = det DS(R(x)) · det DR(x) = 0.
```
So option B, if it literally keeps the current structured decoder untouched, fails.

Recommendation: **C: use the template pattern, but with a full-rank structured Schur/LDU chart `Q` and a separate `pivotBlowupOn(active, p)` radial factor.**

That means:
```text
phi = Q_full_rank ∘ radial
```
where `Q_full_rank` has no unused flat slots, no `x_0` double duty, and the active residual center has exactly `m` coordinates. The radial factor supplies
```text
det Dradial = u^{m-1}
```
and also supplies the rate by setting the residual vector to
```text
u · (1, direction variables).
```
Then the chained product is
```text
A_0 ... A_{L-1} = u H,
```
so
```text
F = u^2 ||H||^2.
```

Verdict: **choose C. A is algebraically valid if you bake the same fixed-1 pivot into the decoder, but the cleaner general design is a full-rank structured `Q` plus the same separate radial blow-up used by the validated `(4,4,2,2)` chart.**

**Q4**

FACT: for `M = (2,2,2)`,
```text
t = 0: (2-0)(2-0) + minAdm(0,2) = 4 + 0 = 4
t = 1: (2-1)(2-1) + minAdm(1,2) = 1 + 2 = 3
t = 2: (2-2)(2-2) + minAdm(2,2) = 0 + 4 = 4
```
so
```text
minAdm(2,2,2) = 3.
```

For `Text = [2,2,1,1]`,
```text
k=0: (2-2)(2-2) = 0
k=1: (2-1)(2-1) = 1
k=2: (1-1)(2-1) = 0
```
so the chain codim is
```text
1.
```

Verdict: **they do not agree: `minAdm = 3`, but this path has chain codim `1`. Therefore `Text=[2,2,1,1]` is not a valid validate-small test for the identity `DET = |x_p|^{minAdm-1}`.**