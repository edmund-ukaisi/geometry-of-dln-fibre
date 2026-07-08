**Formula**

[PROVEN] Fix a cut `t`, set `a=M_0-t`, `b=M_1-t`, and write `q=s'`. Let  
`R=A_2...A_{L-1}` and let `r=rank(R)`, so `q <= r <= n=min(M_2,...,M_L)`. The combined tail cost is

```text
C_tail(t,q)
= min_{r=q..n} [
    t*r
  + (b-q)*(r-q)
  + minAdm(M_2-r, M_3-r, ..., M_L-r)
  ].
```

Here `t*r` is the cost of `B R=0`, `(b-q)(r-q)` is the free `b x r` matrix rank-drop cost for `D R`, and `minAdm(M_2-r,...,M_L-r)` is the product-rank cost for `R`.

[PROVEN] These terms are **entangled**, not additive: the same hidden rank `r` of `R` controls both the top zero-product condition and the lower rank-deficiency condition. One must minimize once over the shared `r`; adding

```text
minAdm(b-q,M_2-q,...,M_L-q) + minAdm(t,M_2,...,M_L)
```

double-counts the deeper rank-drop variables.

[PROVEN] Since `t+b=M_1`,

```text
C_tail(t,q)
= t*q + minAdm(M_1-q, M_2-q, ..., M_L-q).
```

Thus the correct total charge on `{rank(Q_b)=q}` is

```text
charge(t,q)
= a*q + C_tail(t,q)
= M_0*q + minAdm(M_1-q, M_2-q, ..., M_L-q).
```

This is independent of the original cut `t`, except for the constraint that the stratum exists.

**Verdict**

[PROVEN] Apply the peeling identity to the tail product `P=A_1...A_{L-1}`:

```text
codim{rank(P) <= q}
= minAdm(M_1-q, ..., M_L-q).
```

Given `rank(P)=q`, the condition `A_0 P=0` costs `M_0*q`. Therefore

```text
minAdm(M_0,...,M_L)
= min_q [ M_0*q + minAdm(M_1-q,...,M_L-q) ].
```

But the bracketed term is exactly `charge(t,q)`. Hence

```text
charge(t,s') >= minAdm(M)
```

for every cut `t` and every sub-generic rank `s'`, and the minimum over all ranks equals `minAdm(M)`.

So the answer is **YES: closure holds**. There is no `(M,t,s')` counterexample with strict shortfall.

**Mechanism**

[PROVEN] Higher rank-deficiency is never more binding because its lost active decay is exactly compensated by the entangled codimension of the tail-product rank stratum; the result is one term in the right-peeling minimum for the full zero-product locus.