Claim A is **true**. No lexicographic refinement or third interval is needed.

Let
`A* = [a,b]`, `B* = [c,d]`, and assume

```text
a < c,   c <= b + 1,   b < d
```

Let `M = min (b-a) (d-c)`. Minimality says every active pair `(P,Q)` satisfies

```text
M <= min (len P) (len Q).
```

**Covering part.**

If `I=A*`, then `b-a <= d-c`, `k=c-1`, and

```text
a <= c-1        from a < c
c-1 <= b        from c <= b+1
```

so `A*` covers `k`.

If `I=B*`, then `d-c < b-a`, `k=b+1`, and

```text
c <= b+1        from c <= b+1
b+1 <= d        from b < d
```

so `B*` covers `k`.

**Shortest-Covering Proof Skeleton**

Case 1: `I=A*`, so `b-a <= d-c`, `M=b-a`, `k=c-1`.

Assume active `Y=[x,y]` covers `k` and is shorter:

```text
x <= c-1
c-1 <= y
y - x < b - a
```

Split on `y < d`.

Subcase 1a: `y < d`.

Then `Y` pairs with `B*` as the left member:

```text
pair(Y,B*):

0 <= x          active Y
d <= N          active B*
x < c           from x <= c-1
c <= y+1        from c-1 <= y
y < d           case assumption
```

Thus `(Y,B*)` is an active pair, so by minimality:

```text
b-a <= min (y-x) (d-c)
```

but

```text
min (y-x) (d-c) <= y-x
y-x < b-a
```

contradiction by `omega`.

Subcase 1b: `d <= y`.

Then `A*` pairs with `Y` as the left member:

```text
pair(A*,Y):

0 <= a          active A*
y <= N          active Y
a < x           from b < d, d <= y, y-x < b-a
x <= b+1        from x <= c-1 and c <= b+1
b < y           from b < d <= y
```

The only non-immediate inequality is `a < x`; `omega` proves it from:

```text
b < d
d <= y
y - x < b - a
```

Then minimality gives

```text
b-a <= min (b-a) (y-x)
```

while

```text
min (b-a) (y-x) <= y-x
y-x < b-a
```

contradiction.

Case 2: `I=B*`, so `d-c < b-a`, `M=d-c`, `k=b+1`.

Assume active `Y=[x,y]` covers `k` and is shorter:

```text
x <= b+1
b+1 <= y
y - x < d - c
```

Split on `a < x`.

Subcase 2a: `a < x`.

Then `A*` pairs with `Y`:

```text
pair(A*,Y):

0 <= a          active A*
y <= N          active Y
a < x           case assumption
x <= b+1        covering
b < y           from b+1 <= y
```

Minimality gives

```text
d-c <= min (b-a) (y-x)
```

but

```text
min (b-a) (y-x) <= y-x
y-x < d-c
```

contradiction.

Subcase 2b: `x <= a`.

Then `Y` pairs with `B*`:

```text
pair(Y,B*):

0 <= x          active Y
d <= N          active B*
x < c           from x <= a and a < c
c <= y+1        from c <= b+1 <= y
y < d           from x <= a, a < c, y-x < d-c
```

Again, `omega` proves `y < d` from:

```text
x <= a
a < c
y - x < d - c
```

Then minimality gives

```text
d-c <= min (y-x) (d-c)
```

while

```text
min (y-x) (d-c) <= y-x
y-x < d-c
```

contradiction.

So every shorter active interval covering the selected `k` immediately produces a strictly smaller-min active pair, using only `A*` or `B*`.

For (c): minimality over `min(len A, len B)` is the right hypothesis. Minimizing only the left member would not contradict subcase `I=A*`, `d <= y`, because the new pair is `(A*,Y)` and the left length is unchanged. Similarly, minimizing only the right member would not contradict subcase `I=B*`, `x <= a`, because the new pair is `(Y,B*)` and the right length is unchanged.