1. **Yes, under literal (N)+(I), #159 is genuinely needed.**

For `L ≥ 2`, (I) forces `Qf_0 = 1`, so (N) at layer `0` becomes

```lean
Pf 0 ⬝ deepestPoint 0 = corM
```

That is exactly a left-only normal form for the `[A | 0]` boundary matrix.

Similarly, (I) forces `Pf (L-1) = 1`, so the last layer needs

```lean
deepestPoint (L-1) ⬝ Qf (L-1) = corM
```

That is exactly the right-only normal form.

The interface-slack idea only helps if you weaken (I) to `Qf_s ⬝ Pf_{s+1} = 1`. It does **not** satisfy the stated (I), and raw `deepestPoint_frame` still has uncontrolled boundary factors. Inference: making slack work would require block-compatibility of the propagated factor with `corM`, which is essentially the same one-sided normal-form content in a more global form.

2. **Minimal one-sided lemmas.**

I would state #159 as:

```lean
theorem left_normal_form_of_cols_vanish
    {m n r : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hm : r ≤ m) (hn : r ≤ n)
    (hrank : Matrix.rank M = r)
    (hcols : ∀ (i : Fin m) (j : Fin n), r ≤ (j : ℕ) → M i j = 0) :
    ∃ P : Matrix (Fin m) (Fin m) ℝ,
      IsUnit P ∧ P ⬝ M = corM (m := m) (n := n) (r := r)
```

and symmetrically:

```lean
theorem right_normal_form_of_rows_vanish
    {m n r : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hm : r ≤ m) (hn : r ≤ n)
    (hrank : Matrix.rank M = r)
    (hrows : ∀ (i : Fin m) (j : Fin n), r ≤ (i : ℕ) → M i j = 0) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      IsUnit Q ∧ M ⬝ Q = corM (m := m) (n := n) (r := r)
```

Verify-exists: exact names/types for `Matrix.rank`, `IsUnit`, and `corM` should match your Core file.

These are provable from `rank_normal_form_exists`, but not because the right factor “acts trivially” on the zero block. More precisely: if `M = [A | 0]` and `P ⬝ M ⬝ Q = corM`, the equality forces the top-right block of `Q` to vanish; the top-left `r × r` block is then invertible. Absorb that invertible corner into `P` to get `P' ⬝ M = corM`. The row version follows by transpose.

3. **Edge cases.**

Use an explicit `L = 1` / `2 ≤ L` split.

For `L = 1`, the single layer is both boundaries and there is no interior/interface constraint. Use the existing two-sided `deepestPoint_frame`.

For `2 ≤ L`, use the uniform boundary definition:

```lean
Pf s := if (s : ℕ) = 0 then P_left0 else 1
Qf s := if (s : ℕ) + 1 = L then Q_rightLast else 1
```

This handles `L = 2` correctly: layer `0` is left-only, layer `1` is right-only, and there are no strict interiors.

A fully uniform “first/last” definition without an `L = 1` split is not clean, because at `L = 1` the same layer is both first and last and the boundary vanishing lemmas are only known for `L ≥ 2`.

4. **Recommendation.**

Use option **(a): depend on #159**. Define:

- `L = 1`: raw two-sided `deepestPoint_frame`;
- `2 ≤ L`: left-only frame at layer `0`, right-only frame at layer `L-1`, identities everywhere else.

Fallback: prove the two one-sided lemmas locally from `rank_normal_form_exists` and move them to `RankNormalForm.lean` when #159 lands.

I would not use the interface-slack formulation unless you intentionally weaken downstream statements from literal interior identity to interface identity. It is less robust and still needs the same block-normal-form argument.