**VERDICT:** For `L >= 3` and `a > 0`, the peel requires a joint resolution of `{P_tail=0}` and `{P_full=0}`; this is bounded labour via Aoyagi’s `(S,J)`/`D_J` bookkeeping, not a new obstruction.

The decisive point is that `P_full^{-a/2}` is subordinate only as a standalone zeta factor. That does not make it benign against the near-critical measure

```text
P_tail^{-(c' - a/2)} dA.
```

On a common resolution one must check, divisor by divisor,

```text
(c' - a/2) ord_E(P_tail) + (a/2) ord_E(P_full) < jacobian threshold_E.
```

A black-box tail-chain theorem only checks the first term. A black-box full-chain theorem only checks the second term. Since for `L >= 3` the deeper variables `A2,...,A_{L-1}` are shared, there are exceptional divisors where both orders are positive. The exponents add there.

The nesting `P_full >= P_tail` does not save the reduction. It only gives

```text
P_full^{-a/2} <= P_tail^{-a/2},
```

which would bound the mixed integrand by `P_tail^{-c'}`. At a binding cut, `c'` may be above the RLCT of the reduced tail chain, so that bound is too crude. The L=2 case is different because the relevant row blocks are independent/free; the subordinate factor does not ride on the same deeper rank-drop divisors.

Accumulation across later peels strengthens the joint verdict. Even if each `P_full^{(k)}` factor is individually below its own RLCT, their orders can pile up on the same shared deeper divisor. A single tail recursion cannot see those summed contributions. That is exactly what the joint `(S,J)` bookkeeping tracks.

Cheapest exact test that could overturn this: prove a no-loss uniform multiplier estimate in the first genuinely coupled `L=3` case. Writing `A1 = (X;Y)` and `B=A2...`, one would need something like

```text
∫_Y (||XB||^2 + ||YB||^2)^(-a/2) dY <= C · log^N(1/||XB||)
```

with `C,N` uniform as `B` drops rank. Any positive power loss in `B`’s singular values or in `||XB||` means the coupling has created joint divisor data, so the black-box single-chain reduction fails.