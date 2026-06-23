M = (2,1,2)
T = (2,2)
```

Then `A_0` is `1 x 2` with one diagonal `1`, `A_1` is `2 x 1` with one diagonal `1`, so

```text
A_1 A_0 =
[1 0
 0 0]
```

has rank `1`. But

```text
w(0,2) = min(2,2) = 2
min(w(0,2), min(M_0,M_2)) = min(2,2) = 2.
```

So the endpoint-only formula misses the intermediate width `M_1 = 1`.

For a fixed `i<j`, the endpoint-capped expression

```text
E(i,j) = min(w(i,j), M_i, M_j)
```

equals the column value `t_j = T_{j-1}` iff

```text
T_{j-1} <= T_p  for all i <= p < j
T_{j-1} <= M_i
T_{j-1} <= M_j.
```

The true matrix rank equals `t_j` iff the stronger-looking but exact condition holds:

```text
T_{j-1} <= T_p  for all i <= p < j
T_{j-1} <= M_r  for all i <= r <= j.
```

Globally for all `i<j`, this is equivalent to clauses `(i)` and `(ii)`; clause `(iii)` is irrelevant.

---

**Q3 Verdict: the minimal admissibility subset needed is `(i) + (ii)`. Clause `(iii)` is not needed.**

`(i)+(ii)` suffices by the proof in Q1.

`(iii)` is not needed. Example:

```text
L = 2
M = (5,5,5)
T = (3,2)
```

This satisfies `(i)` and `(ii)` but violates `(iii)` since `T_1 != 0`. Still the ranks are:

```text
rank(0,1)=3, rank(1,2)=2, rank(0,2)=2,
```

matching `P`.

`(i)` alone is not enough:

```text
L = 2
M = (5,5,5)
T = (1,3)
```

Clause `(i)` holds, but `(ii)` fails. At `(0,2)`:

```text
rankFn(0,2) = min(1,3,5,5,5) = 1
P(0,2) = T_1 = 3.
```

`(ii)` alone is not enough:

```text
L = 2
M = (1,5,5)
T = (3,0)
```

Clauses `(ii)` and `(iii)` hold, but `(i)` fails. At `(0,1)`:

```text
rankFn(0,1) = min(3,1,5) = 1
P(0,1) = T_0 = 3.
```

So `(i)` and `(ii)` are both needed for the universal theorem; `(iii)` is not.

---

**Q4 Verdict: `P` is not a definitional identity. It agrees for admissible `T` because admissibility has real content.**

Non-admissible example:

```text
L = 2
M = (5,5,5)
T = (1,3)
```

At cell `(0,2)`:

```text
rankFn(0,2) = min(1,3,5,5,5) = 1
P(0,2) = T_1 = 3.
```

So `P` overshoots the actual cascade rank. It overshoots because the earlier layer only transmits one diagonal coordinate, while `P` looks only at the right endpoint exponent `T_1 = 3`.

In fact, for `i<j`, the true rank can never exceed `P(i,j)=T_{j-1}`, since the product includes the last factor `A_{j-1}`. Failures are undershoots of the actual rank relative to `P`, i.e. `P` overshoots.
