Short answer: **hfin is not provable from a threshold-only leaf family**. The value theorem `threshold_ge + achiever` is numerical; it is not a resolution-cover theorem.

**(1) Cover / Per-Chart Bound**

A valid hfin proof needs actual charts `phi_i` covering `(-1,1)^N` up to null sets and, on each chart,

```text
|Jac phi_i(y)| <= C_i prod_j |y_j|^{h_ij}
F(phi_i(y))   >= c_i prod_j |y_j|^{2 k_ij}.
```

The bare `(d_i,k_i,h_i)` threshold data does not supply those maps or inequalities.

For the `(3,3,4)` corank-2 stratum, if the threshold-only data really gives codim `3`, then its monomial model has threshold `3/2`. That model is **more singular**, not less singular, than the true codim-8 model. So the failure is not primarily that `|F|^{-c'}` is larger than the codim-3 model predicts. Rather, the codim-3 model is too pessimistic and becomes divergent too early. It can at best prove finiteness for `c' < 3/2`.

If, instead, the atlas claims codim `8` on that stratum but still lacks the symbolic coupled chart showing where the extra five Jacobian dimensions come from, then the per-chart bound is simply unproved. Numerically assigning `h+1=8` is not a geometric resolution.

**(2) Reconciliation**

For one exceptional divisor with loss exponent `k=1` and codim `C=h+1`, the threshold is

```text
(h+1)/(2k) = C/2.
```

For `(3,3,4)`, the true binding value is

```text
C_true = min_r [3r + (3-r)(4-r)]
       = min {12, 9, 8, 9}
       = 8,
```

attained at `r=2`, so the true threshold is `8/2 = 4`.

But the stated threshold-only certificate gives

```text
C_to = 3,
lambda_to = 3/2.
```

Then its model integral has local form like

```text
∫_0^1 rho^{3-1-2c'} d rho,
```

which is finite exactly when `c' < 3/2`. Hence for `c' in (3/2,4)`, the model leaf integral diverges and the hfin antecedent is false. The implication may be formally true, but it is useless for proving `rlct >= 4`.

So the three claims cannot all refer to the same leaf data:

```text
threshold-only codim = 3,
minAdm(3,3,4) = 8,
every leaf threshold >= minAdm/2 = 4.
```

At least one must be reinterpreted. If `threshold_ge` is genuinely proven for the atlas used in hfin, then that atlas is not the harmful threshold-only codim-3 atlas; it has already incorporated the coupled codim-8 contribution numerically. If the leaves are truly threshold-only, then `threshold_ge` is false for `(3,3,4)`.

**(3) Net Verdict**

**Obstruction**, for the threshold-only atlas.

It does not discharge hfin at the desired `minAdm/2` threshold. The obstruction is exactly the corank-2 binding stratum: the data forgetting the shared `Delta`-block cannot justify the codim-8 monomial/Jacobian exponents needed for finiteness up to `c'<4`.

Checks:

```text
(2,2,2):
C = min_r [2r + (2-r)(2-r)]
  = min {4,3,4}
  = 3,
threshold = 3/2.
```

Here threshold-only and true coupled behavior agree.

```text
(3,3,4):
C = min_r [3r + (3-r)(4-r)]
  = min {12,9,8,9}
  = 8,
threshold = 4.
```

The threshold-only codim `3` would give only `3/2`.

To make hfin reachable from scratch, the atlas must be upgraded to genuine geometric resolution charts, e.g. full coupled `diag(b)` / shared-`Delta` charts tracking which exceptional divisor multiplies which generators, with explicit cover, Jacobian exponent, and lower bound for `F ∘ phi`. The threshold-only multiplicity fold is insufficient.