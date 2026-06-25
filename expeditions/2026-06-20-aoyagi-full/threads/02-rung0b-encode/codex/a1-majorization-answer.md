**1. H4 Verdict**

The naive route using only `edgeQ_j ≥ M_{j+1}` does **not** compose. The exclusion of `M_0` is fatal there: the `L-n` largest entries of `{M_1,...,M_L}` need not dominate the `L-n` largest entries of `{M_0,...,M_L}`.

But the complement route **does** compose from the full corridor, using C2. C2 gives
```lean
edgeQ j = M (j+1) + u j - u (j+1)
```
with `u (j+1) ≤ u j` and `u (j+1) ≤ M (j+1)`. Thus each step replaces the pair
```text
(u_j, M_{j+1})
```
by
```text
(edgeQ_j, u_{j+1})
```
with the same total, one entry pushed down, and the other pushed up:
```text
u_{j+1} ≤ u_j, M_{j+1}
edgeQ_j ≥ u_j, M_{j+1}
```
So every largest-`m` sum weakly increases. Iterating gives:
```text
largestK m edgeQ ≥ largestK m M     for m ≤ L
```
where the right side is over all `L+1` widths. This is the step that handles `M_0`.

Then with `m = L - n`:
```text
smallestK n edgeQ
= total edgeQ - largestK (L-n) edgeQ
≤ total M     - largestK (L-n) M
= S_n.
```
So H4 is forced from full C2+C3. It is not forced from C1 alone.

**2. H5 Verdict**

Yes: H5 reduces cleanly to F1 + Step B.

Let `x : Fin c → ℤ` be the first `c` sorted edge values. Then
```text
sum x = smallestK c edgeQ ≤ S_c = P        -- F1
smallestK k x = smallestK k edgeQ          -- for k ≤ c
```
The equality is right: the `k` smallest entries are already among the `c` smallest entries. You can also prove the weaker route via restriction monotonicity, but the sorted-prefix vector is cleaner.

Then Step B gives:
```text
smallestK k edgeQ
= smallestK k x
≤ prefix_k (sort (balancedSplit P c))
= k*b + max(0, k+r-c).
```

**Clean Lemma List**

1. **Complement identity**
```text
smallestK n q = sum q - largestK (N-n) q
```
for a vector of length `N`.

2. **Corridor majorization**
```text
largestK m edgeQ ≥ largestK m M
```
for `m ≤ L`, proved by the iterative pair replacement
`(u_j, M_{j+1}) ↦ (edgeQ_j, u_{j+1})`.

Equivalent smallest-side form:
```text
smallestK (n+1) (edgeQ with an appended 0) ≤ smallestK (n+1) M.
```

3. **Sorted-prefix idempotence**
For `x` the first `c` sorted edge values and `k ≤ c`:
```text
sum x = smallestK c edgeQ
smallestK k x = smallestK k edgeQ
```

4. **Balanced-prefix maximality**
For `x : Fin c → ℤ`, `0 ≤ x_i`, `sum x ≤ P`, `P = c*b + r`, `r < c`:
```text
smallestK k x ≤ k*b + max(0, k+r-c).
```

**One-line:** F1 is the crux only if you do not prove corridor majorization; with full C2 it follows as the `n = c` case of H4, so it does not need the achiever’s `good c` property.