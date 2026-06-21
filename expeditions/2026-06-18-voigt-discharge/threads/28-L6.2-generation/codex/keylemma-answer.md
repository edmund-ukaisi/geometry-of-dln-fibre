The cleanest proof is still row telescope, but replace the block argument by an adjacent Abel shift. Do not group maximal constant blocks.

Define `q_a` as the first bad column for row start `a`:

`q_a := least q ∈ [J, n+1] such that ∃ i ∈ [a,I], g i q = 0`.

Then for `a ∈ [α,I]`, the row fibre is exactly `e ∈ [J, q_a)`, and `q_a` is nondecreasing in `a`.

The key identity is:

```text
Σ_A d g
= g I J
  + g (α-1) q_α
  + Σ_{a=α}^{I-1, q_a < q_{a+1}} g a q_{a+1}.
```

Every extra term is nonnegative, so the goal follows immediately.

How it comes out:

```text
d g a e = D_a(e) - D_a(e+1),
D_a(e) := g a e - g (a-1) e.
```

For each row:

```text
Σ_{e=J}^{q_a-1} d g a e
= D_a(J) - D_a(q_a).
```

Summing over `a = α,…,I` gives

```text
Σ_A d g
= Σ_a (g a J - g (a-1) J)
  + Σ_a (g (a-1) q_a - g a q_a)
= g I J + R,
```

because `g (α-1) J = 0`.

Now handle

```text
R := Σ_{a=α}^I (g (a-1) q_a - g a q_a).
```

Use the adjacent Abel shift:

```text
R =
g (α-1) q_α - g I q_I
+ Σ_{a=α}^{I-1} (g a q_{a+1} - g a q_a).
```

Then `g I q_I = 0`. For each adjacent pair, monotonicity gives `q_a ≤ q_{a+1}`.

If `q_a = q_{a+1}`, the summand is `0`.

If `q_a < q_{a+1}`, then `q_a` is bad for `[a,I]`, but not bad for `[a+1,I]`; hence the bad point must be row `a`, so

```text
g a q_a = 0.
```

Thus the summand becomes `g a q_{a+1} ≥ 0`.

So the block proof collapses to the jump formula above.

**Ranking for Lean cost**

1. **Best:** row telescope with half-open fibres `[J, q_a)` and the adjacent Abel shift. Define `q_a` as first bad column, not as `E(a)+1`, if you can. This gives the shortest local lemmas.

2. **Acceptable:** same proof, but prove the Abel identity by induction on the row endpoint instead of Finset reindexing. Useful if integer interval shifting gets noisy.

3. **Column-first telescope:** possible with analogous lower-bound functions `β_e`, but it introduces another staircase boundary. Usually not shorter.

4. **Distinct q-values / maximal blocks:** mathematically fine, but worse in Lean: images, sorted distinct values, block endpoints, disjointness, and maximality proofs.

5. **Full 2-D induction / peeling rows or columns of the original support:** likely worst. The staircase changes nonlocally, so the cases are more painful than the telescope.

For Finsets, the robust formulation is an explicit double sum:

```text
Σ a ∈ Icc α I, Σ e ∈ Ico J (q_a), d g a e.
```

Avoid making the main proof run through `A` as a filtered product plus `Finset.sum_biUnion`. If the theorem statement uses `A`, prove once that its sum equals the explicit row-sum form, then do all telescoping on the double sum. Half-open intervals `Ico J q_a` are much cleaner than `Icc J E(a)` for the inner telescope.