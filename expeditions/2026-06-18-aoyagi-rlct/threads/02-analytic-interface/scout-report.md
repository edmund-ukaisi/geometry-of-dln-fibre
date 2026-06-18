# Scout report - analytic interface and deepest point

Status: xhigh scout `Boole`, integrated by controller. Read-only scout; no files
were edited by the scout.

Source: Aoyagi 2023 PDF pp. 5-6 and p. 14. Paper source only.

## Normal-crossing extraction source statement

PDF p. 5 defines the local learning coefficient/RLCT for an analytic function
`F` and smooth compactly supported prior/weight `phi` near `w*` by local
integrability:

```text
lambda_(w*)(F, phi) = sup { c : int_U |F|^(-k c) phi(w) dw < infinity },
```

where `k = 1` over `R` and `k = 2` over `C`. The order `theta` is the order of
the largest pole of the zeta function. If `phi(w*) != 0`, Aoyagi suppresses
`phi`.

For an ideal `J = <F_1, ..., F_m>`, Aoyagi defines

```text
lambda_(w*)(J) = lambda_(w*)(F_1^2 + ... + F_m^2).
```

PDF p. 6 applies Hironaka's theorem to a Kullback function `K(w)`. In local
coordinates `u = (u_1, ..., u_d)` on a resolution chart, Aoyagi writes

```text
K(pi(u)) = u_1^(2 k_1) ... u_d^(2 k_d),
pi'(u) phi(pi(u)) = u_1^(h_1) ... u_d^(h_d).
```

The extraction formula is

```text
lambda = min_U min_j (h_j + 1) / (2 k_j),
theta = max_u Card { j : (h_j + 1) / (2 k_j) = lambda }.
```

For Lean, the cited interface should take a finite family of normal-crossing
charts with nonvanishing unit factors and output exactly this minimum/order
formula. Coordinates with `k_j = 0` need explicit treatment, e.g. ignored or
assigned infinite ratio.

Source quirks:

- PDF p. 6 says `k_i, h_i` are "non-positive integers"; the displayed monomial
  form and formula require the usual nonnegative exponent convention.
- The change-of-variables line appears to print `K(g'(u))`; context requires
  `K(pi(u))`.

## Theorem 4 source statement and use

PDF p. 14 states Theorem 4, cited to Aoyagi [22]. It concerns homogeneous
functions `F_1, ..., F_m` in the first `j` variables and a smooth weight `phi`
with comparison/homogeneity hypotheses. It concludes

```text
lambda_(0,...,0,w*_(j+1),...,w*_d)(<F_1,...,F_m>, phi)
  <=
lambda_(w*_1,...,w*_d)(<F_1,...,F_m>, phi).
```

Aoyagi immediately uses this to set `r^(s) = r` for all `s = 1, ..., L` in the
reduced product problem.

## Scout recommendation

The scout recommended treating Theorem 4 as analytic/global background rather
than reproving it from this paper. Reasons:

- Theorem 4 is cited to another Aoyagi paper and is not proved in Aoyagi 2023.
- The printed `phi_w` hypothesis is ambiguous.
- The theorem compares RLCTs at different base points using analytic
  integrability data, not matrix algebra.

## Controller decision

The goal permits only the normal-crossing-to-RLCT extraction theorem as a Lean
citation. Therefore Theorem 4 cannot be accepted as a second cited Lean theorem
without surfacing a scope conflict.

Allowed paths:

1. Avoid Theorem 4 by proving the final result locally at the deepest point and
   formulating the Lean theorem at that point.
2. Prove a restricted homogeneous-polynomial deepest-point lemma sufficient for
   Aoyagi's use.
3. If neither is feasible, record a scope conflict and ask the operator whether
   the cited boundary may be expanded.

## Kill-conditions

- The model must remain in the real analytic setting used by Aoyagi.
- The prior/weight must be smooth, compactly supported, and nonzero at the RLCT
  point; Theorem 4 also has extra comparison/homogeneity assumptions.
- Normal-crossing extraction needs a proper analytic resolution with finite
  chart cover and nonvanishing units.
- A single chart does not determine global `lambda` unless known to attain the
  minimum.
- `theta` is the maximum number of coordinates attaining the global minimum,
  not a count in an arbitrary chart.
- Theorem 4 gives an inequality toward the zeroed point; it does not prove
  uniqueness or equality of deepest points.
