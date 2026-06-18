**1. HL `=>` `mOfE` Image**

Use the constructive inverse, not a Finset image/bijection argument.

Paper indexing:
`e_i = m(0, i-1)` for `1 ≤ i ≤ N`.

Lean indexing:
```lean
def eOfm (m : Fin (N+1) × Fin (N+1) → ℕ) : Fin N → ℕ :=
  fun i => m (0, i.castSucc)
```

Key identities for `hm : m ∈ kostantPartitions d 0` and `hHL`:

1. Feasibility:
```text
∑ i : Fin N, eOfm m i = d 0
```
This is just `kostantAt d m 0`; support forces every interval covering `0` to start at `0`, and corner `m(0,N)=0` removes the last term.

2. Top-row forcing, for `1 ≤ x ≤ N`:
```text
d x + m(0, x-1) = d (x-1) + m(x, N)
```
Under `Monotone d`, this rewrites to:
```text
m(x, N) = m(0, x-1) + (d x - d (x-1))
```
This is exactly the second branch of `mOfE`.

3. Pointwise equality cases:
```text
mOfE d (eOfm m) (0, y) = m(0,y)       for y < N
mOfE d (eOfm m) (0, N) = 0 = m(0,N)
mOfE d (eOfm m) (x, y) = 0 = m(x,y)   for 1 ≤ x and y < N, by HL/support
mOfE d (eOfm m) (x, N) = m(x,N)       by the top-row identity
```

Single hardest obstruction here: the adjacent Kostant-filter subtraction proving  
`d x + m(0,x-1) = d(x-1)+m(x,N)` with `Fin` predecessor/successor casts. Use existing `mOfE_zero_lt`, `mOfE_top`, `mOfE_corner` [SURE], plus `Fin.sum_univ_castSucc` [SURE], `Fin.ext` [SURE], and `omega`.

**2. Exhaustiveness**

I would not use the “minimal `a`, then minimal `b`” left-partner split. Minimal `a` does not kill the nested `b' ≥ b` case: the covering interval may touch an endpoint, e.g. `[0,b']` or `[a',N]`, so it is not a smaller interior interval.

Cleaner form-level route: pick any interior source `[a,b]` with
```text
1 ≤ a, b < N, m(a,b) > 0.
```

Look at the adjacent edge `b | b+1`.

Define:
```text
Ends_b   = ∑_{x ≤ b} m(x,b)
Starts_b = ∑_{b+1 ≤ y} m(b+1,y)
```

The Kostant constraints at vertices `b` and `b+1` give:
```text
d_b + Starts_b = d_{b+1} + Ends_b.
```

Since `d` is weakly increasing, `d_b ≤ d_{b+1}`, hence:
```text
Ends_b ≤ Starts_b.
```

But `m(a,b) > 0` and `[a,b]` ends at `b`, so `Ends_b > 0`. Therefore `Starts_b > 0`, so there exists `d'` with:
```text
b+1 ≤ d' ≤ N,   m(b+1,d') > 0.
```

Then the concrete decreasing move is always the right concat:
```text
[a,b] + [b+1,d']  ↦  [a,d'].
```

It preserves the Kostant constraints, because at each vertex the target covers exactly the union of the two adjacent sources. It does not create the forbidden corner because `a ≥ 1`, so `[a,d'] ≠ [0,N]`.

So sub-step 3 can be B-only. The A-uncross move is useful, but not needed for the converse under monotonicity. This proof also does not use `d₀ ≥ 1`; keeping that hypothesis is harmless, but the proof should not route through column `a-1`.

Useful names: `Finset.single_le_sum` [SURE], `Finset.exists_ne_zero_of_sum_ne_zero` [SURE], `Finset.sum_congr` [SURE], `Finset.sum_filter` [SURE], `Finset.sum_add_distrib` [SURE].

**3. Move Encoding**

For these multi-entry moves, use explicit piecewise arrays, not nested `Function.update`.

Recommended shape:
```lean
def concatMove m a b d' : ... :=
  fun p =>
    m p
      + (if p = (a,d') then 1 else 0)
      - (if p = (a,b) then 1 else 0)
      - (if p = (b+1,d') then 1 else 0)
```

Also define the corresponding integer delta:
```lean
def concatDelta a b d' p : ℤ :=
  (if p = (a,d') then 1 else 0)
  - (if p = (a,b) then 1 else 0)
  - (if p = (b+1,d') then 1 else 0)
```

Then prove:
```text
extendℤ (concatMove m ...) = extendℤ m + concatDelta ...
```
on the box, and use that in the Δ lemma.

`Function.update_self`, `Function.update_of_ne`, `Function.update_apply` [SURE] are fine for the already-proved single corner update, but nested updates make the move proofs order-sensitive and force repeated key-distinctness rewrites.

**4. Hardest Obstruction**

With the B-only exhaustiveness lemma, the hardest Lean obstruction is the strict Δ lemma for concat against the existing nested `codimForm`.

Estimate: 350-600 lines for the first clean version.

Subtasks:
1. Define concat keys and prove distinctness from `a ≤ b < b+1 ≤ d'`.
2. Prove `concatMove` has no underflow from the two source-positivity hypotheses.
3. Prove Kostant preservation by the “two adjacent sources equal one target” filter-sum identity.
4. Prove the `extendℤ` pointwise delta lemma.
5. Expand `codimForm` under `M + δ`; collapse finite indicator sums with `Finset.sum_eq_single_of_mem` [SURE], `Finset.sum_eq_zero` [SURE], `Finset.sum_congr` [SURE], then finish with `ring`/`omega`.
6. Conclude strict decrease from `m(a,b) ≥ 1` and `m(b+1,d') ≥ 1`.

The main theorem then becomes a short contradiction: non-HL gives concat move, concat move gives smaller codim, contradict `Finset.inf'_le` [SURE] for the minimiser.