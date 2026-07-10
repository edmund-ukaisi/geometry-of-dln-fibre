Let `m_i = M^{(i)}`, `p_S = M(S)=min(m_1,...,m_S)`, and `F(M)=minAdm(M)`.

**1. Printed Case-2 profile, `J=0`.**

For
`t_i=m_{i+1}` for `i<S`, and `t_i=0` for `i>=S`, all summands vanish except the drop at `S`.

If `S>1`,
```text
(m_1-m_2)(m_2-m_2)=0,
(m_j-m_{j+1})(m_{j+1}-m_{j+1})=0  for 2<=j<S,
(m_S-0)(m_{S+1}-0)=m_S m_{S+1},
```
and all later terms are zero. For `S=1`, the first term is already `m_1m_2`.

So the printed terminal exponent is exactly

```text
Mval(t) = M^{(S)} M^{(S+1)}.
```

More generally, the same formal computation with constant tail `J` gives `(m_S-J)(m_{S+1}-J)`, but the `minAdm` recursion corresponds to the terminal `J=0` case.

**2. Is this always `>= minAdm`?**

Yes. It never goes below `F(M)`.

The key admissible comparison profile is the prefix-min profile
```text
u_i = p_{i+1}  for i<S,
u_i = 0        for i>=S.
```
This is admissible because prefix minima are nonincreasing. Its cost is

```text
F(M) <= p_S m_{S+1}.
```

Indeed, before stage `S`, each term is zero: either the prefix minimum does not drop, or the new width is itself the prefix minimum. The only nonzero term is `p_S m_{S+1}`. Since `p_S <= m_S`,

```text
F(M) <= p_S m_{S+1} <= m_S m_{S+1} = Mval(t_printed).
```

It can bind, but need not. Example binding: `M=(5,2,1,3)`.
```text
F(5,2,1,3)=2,
S=2 gives m_2 m_3 = 2.
```
Example strict: `M=(2,4,4)`.
```text
F(2,4,4)=min(8, 3+4, 8)=7,
S=2 gives m_2m_3=16.
```

**3. Prefix-min single-step codimension.**

Yes, also always

```text
M(S) M^{(S+1)} = p_S m_{S+1} >= F(M).
```

This is exactly the comparison profile above.

It can bind. For `M=(1,2,2)`,
```text
F(1,2,2)=2,
S=2 gives p_2 m_3 = 1*2 = 2,
```
while the printed actual-width product would be `m_2m_3=4`.

Some by-hand checks:

```text
M=(2,4,4):      F=7, prefix S=2 gives 8, actual S=2 gives 16.
M=(2,4,4,4):    F=6, prefix S=2,3 gives 8, actual gives 16.
M=(3,2,4,4):    F=5, prefix S=3 gives 8, actual S=3 gives 16.
M=(5,2,1,3):    F=2, prefix/actual S=2 gives 2.
```

**4. Does the exact Case-2 exponent matter for finiteness?**

For the `J=0` comparison, no. For finiteness at `c < (1/2)F(M)`, the load-bearing fact is only

```text
Case-2 exponent >= F(M).
```

The safe ambiguity-insensitive lower bound is the prefix-min one:

```text
Case-2 exponent >= p_S m_{S+1} >= F(M).
```

Do not use `m_Sm_{S+1}` as the safe coarse bound unless you have already fixed the interpretation as the printed terminal `Mval`. If the actual divisor codimension is the prefix-min one, `m_Sm_{S+1}` can be too large: for `M=(2,4,4)`, `S=2`, the prefix value is `8` but the actual-width product is `16`.

So the `M^{(S)}` vs `M(S)` ambiguity does not matter for this finiteness bound, but it does matter for exact divisor bookkeeping and for identifying which divisor binds.

**5. Naive prefix-min “fix” can create negative summands.**

Yes. If one replaces the column factor `m_{j+1}` by `p_{j+1}` while keeping the printed pivot `t_j=m_{j+1}`, then for `j<S` the summand becomes

```text
(m_j-m_{j+1})(p_{j+1}-m_{j+1}).
```

This is negative exactly when there was an earlier bottleneck and then a local decrease that stays above it:

```text
p_j < m_{j+1} < m_j.
```

Example: `M=(2,5,4,4)`, `S=3`, printed `t=(5,4,0)`. Prefix minima are `p_2=p_3=p_4=2`. The naive middle term is

```text
(t_1-t_2)(p_3-t_2) = (5-4)(2-4) = -2.
```

That is the failure mode: replacing column widths by prefix minima destroys the zero factors `m_{j+1}-t_j=0` and can make individual summands negative.