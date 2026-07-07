FALSE.

Concrete witness:

- `M = (1, 2, 1)`, so `minAdm M = 1`.
- Take `c' = 1/4`, valid since `0 ≤ 1/4 < 1/2`.
- Take `q = 1`.
- Let `Q : Fin 2 → Fin 1 → ℝ` be
  ```lean
  Q 0 0 = 0
  Q 1 0 = 1
  ```

Write `A0 = [a b]` with `(a,b) ∈ [-1,1]^2`. Then

```text
A0 Q = b
frobSq (A0 Q) = b^2
```

So the LHS is

```text
∫_{[-1,1]^2} (b^2)^(-1/4) da db
= 2 * ∫_{-1}^1 |b|^(-1/2) db
= 2 * 4
= 8.
```

The value at `b = 0` is `0` because of `Real.rpow`, but that is a measure-zero set, so the integral is still `8`.

Now the RHS. Here `min(M0,M1)=1`, so `t = 0, 1`.

```text
frobSq Q = 1
frobSqTopRows 0 Q = 0
frobSqTopRows 1 Q = 0
```

because the top row of `Q` is zero.

Also:

```text
peelExp M 0 = (1 - 0)(2 - 0) = 2
peelExp M 1 = (1 - 1)(2 - 1) = 0
```

For `t = 0`:

```text
0^(-(1/4 - 1)) * 1^(-1)
= 0^(3/4) * 1
= 0.
```

For `t = 1`:

```text
0^(-(1/4 - 0)) * 1^0
= 0^(-1/4) * 1
= 0
```

because `Real.rpow 0 y = 0` for `y ≠ 0`.

Thus every RHS summand is `C * 0 = 0`, for every finite `C : ℝ≥0∞`. So the inequality becomes

```text
8 ≤ 0
```

which is false.

This is exactly a `Real.rpow` artifact: analytically, `0^negative` should behave like `+∞`, not `0`. A minimal repair is to formulate the RHS powers in `ℝ≥0∞`, e.g.

```lean
(ENNReal.ofReal (frobSqTopRows t Q)).rpow (-(c' - peelExp M t / 2))
```

rather than computing a real power first and then applying `ENNReal.ofReal`.

If you require a finite RHS pointwise for every `Q`, then you must instead restrict `Q`, for example requiring

```text
c' > peelExp M t / 2 → 0 < frobSqTopRows t Q
```

for relevant `t`. An a.e.-in-`Q` version could also avoid this exact degenerate parameter set, but a.e. in `A0` does not fix the stated pointwise-in-`Q` inequality.