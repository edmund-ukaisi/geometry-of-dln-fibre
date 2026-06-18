**Clean Route**

Use an auxiliary `phiMin d`, the `Finset.inf'` of `Phi d (↑e)` over the feasible antidiagonal, and prove:

```lean
phiMin d =
  tailSq d m + (m : ℤ) * (a - d0)^2 + 2 * (a - d0) * δ + |δ|
```

Then transfer to `qipMin` using (A):

```lean
2 * qipMin d = phiMin d + d0^2 - ∑ i : Fin N, s_i^2
```

After splitting `∑ s_i^2` into prefix `i < m` and tail `i ≥ m`, the tails cancel and this becomes exactly:

```lean
2 * qipMin d =
  d0^2 - ∑_{j=1}^m (d_j - d0)^2
    + m * (a - d0)^2 + 2 * (a - d0) * δ + |δ|
```

so `qipMin d = cValue d` by integer division by `2`.

For the lower bound, route through **attainment + (C)**. Do not try to prove the full lower bound directly per coordinate. Even though under monotonicity the tail inequality `(e_i - s_i)^2 ≥ s_i^2` actually holds because `s_i ≤ 0`, tail mass changes the active sum from `δ` to `δ - tailMass`, so (B) no longer applies with the desired `δ`. Avoiding (C) would amount to reproving the drop-to-`m` argument.

**ℕ/ℤ Gap**

Lower bound: no gap. After choosing a `Phi`-minimiser `e*`, (C) gives `e*_i = 0` for `i ≥ m`. Define

```lean
t_i := (e* i : ℤ) + d_{i+1} - a   -- for i : Fin m
```

Then `∑ t_i = δ`. Since (B) is an unconstrained `ℤ` lower bound, it applies immediately:

```lean
|δ| ≤ ∑ i : Fin m, t_i^2
```

No nonnegativity of `a + t_i - d_{i+1}` is needed in the lower bound.

Upper bound: this is the only place where nonnegativity matters. Construct a rounded `t : Fin m → ℤ` with

```lean
∑ t_i = δ
∑ t_i^2 = |δ|
t_i ∈ {0, 1}      if δ ≥ 0
t_i ∈ {-1, 0}     if δ < 0
```

Then define the witness on the `m`-face by

```lean
e_i = a + t_i - d_{i+1}   for i < m
e_i = 0                  for i ≥ m
```

You must prove:

```lean
∀ i : Fin m, 0 ≤ a + t_i - d_{i+1}
```

The branch-sensitive bounds needed are:

```lean
δ ≥ 0 → ∀ i ≤ m, d_i ≤ a
δ < 0 → ∀ i ≤ m, d_i ≤ a - 1
```

The second one is stronger than the informal “`a ≥ d_i`” certificate. That informal bound is not enough when `δ < 0`, because some `t_i = -1`.

Use only integer inequalities:

```lean
S = m * a + δ
-m < δ ∧ δ < m
m * d_i ≤ S
```

If `δ ≥ 0`, then `S < m * (a + 1)`, so `d_i ≥ a + 1` contradicts `m * d_i ≤ S`.

If `δ < 0`, then `S < m * a`, so `d_i ≥ a` contradicts `m * d_i ≤ S`.

**Lean-Shaped Skeleton**

1. `two_G_of_feasible`
```lean
lemma two_G_of_feasible (he : e ∈ feasible d) :
  2 * Gqip d (↑e) = Phi d (↑e) + d0^2 - ∑ i : Fin N, s_i^2
```
Use committed lemma (A) and rewrite `∑ e = d0`.

2. `two_qipMin_eq_phiMin_add_const`
```lean
lemma two_qipMin_eq_phiMin_add_const :
  2 * qipMin d = phiMin d + d0^2 - ∑ i : Fin N, s_i^2
```
Use `Finset.inf'` attainment for `qipMin`; show a `Gqip` minimiser is a `Phi` minimiser via (A).

3. `rounded_t_exists`
```lean
lemma rounded_t_exists :
  ∃ t : Fin m → ℤ,
    ∑ i, t i = δ ∧
    ∑ i, (t i)^2 = |δ| ∧
    (δ ≥ 0 → ∀ i, t i = 0 ∨ t i = 1) ∧
    (δ < 0 → ∀ i, t i = -1 ∨ t i = 0)
```
Construct first `natAbs δ` coordinates as `sign δ`, rest `0`.

4. `rounded_e_nonneg`
```lean
lemma rounded_e_nonneg :
  ∀ i : Fin m, 0 ≤ a + t i - d_{i+1}
```
Use the branch-sensitive prefix bounds above.

5. `rounded_e_feasible`
```lean
lemma rounded_e_feasible : eRound ∈ feasible d
```
After casting to `ℤ`, split active/tail sums and use:
`∑ t_i = δ`, `S = d0 + ∑_{j=1}^m d_j`, and `δ = S - m * a`.

6. `phi_round_eq_closed`
```lean
lemma phi_round_eq_closed :
  Phi d (↑eRound) =
    tailSq + m * (a - d0)^2 + 2 * (a - d0) * δ + |δ|
```
Rewrite active terms as `(t_i + (a - d0))^2`; tails are fixed because `e_i = 0`.

7. `phiMin_le_closed`
```lean
lemma phiMin_le_closed : phiMin d ≤ phiClosed d
```
Use the rounded feasible witness.

8. `closed_le_phiMin`
```lean
lemma closed_le_phiMin : phiClosed d ≤ phiMin d
```
Take an attained `Phi`-minimiser, apply (C), define `t`, prove `∑ t = δ`, apply (B), expand squares.

9. `phiMin_eq_closed`
```lean
lemma phiMin_eq_closed : phiMin d = phiClosed d
```
By antisymmetry.

10. `qipMin_eq_cValue`
```lean
lemma qipMin_eq_cValue : qipMin d = cValue d
```
Rewrite `2 * qipMin` using steps 2 and 9; split prefix/tail sums; cancel tails; finish with `(2 * x) / 2 = x` over `ℤ`.

**Hard Lean Steps**

- Reindexing `Fin N` into active `Fin m` plus tail `m ≤ i.val`, especially matching `d_{i+1}` with paper indices `1..m`.
- The active square expansion:
  ```lean
  ∑ (t_i + (a - d0))^2
    = ∑ t_i^2 + 2 * (a - d0) * ∑ t_i + m * (a - d0)^2
  ```
- Extracting an attained minimiser from `Finset.inf'`, especially if `qipMin` is an infimum of an image finset.

**Gaps / Hypotheses**

No `d0 ≥ 1` hypothesis is needed. You do need `1 ≤ m` and `m ≤ N`.

The main hidden gap is the negative-`δ` witness case: `a ≥ d_i` is insufficient; prove `d_i ≤ a - 1` when `δ < 0`.

`m = N` should be tested separately because all tail sums are empty. `δ = 0` should also be tested because the rounded witness has all `t_i = 0`.