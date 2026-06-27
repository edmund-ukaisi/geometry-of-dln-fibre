**Definitive Answer: NO**

`static_count` is not qFM-free in the sense you specify. The alternative direct route fails in region `(b)` unless it proves exactly the positional-prefix fact supplied by the band at indices `< i`.

The decisive calculation is in the saturated region `b + 1 < τ`.

Let

```text
Aτ  := #{0 ≤ k ≤ L : M^k < τ}
pτ  := #{1 ≤ k ≤ i+1 : M^k < τ}
ετ  := [M^0 < τ].
```

Since `b + 1 < τ`, all β-block entries are `< τ`, and `aS_0,…,aS_c < τ`. Hence

```text
cLt(Ymulti, τ) = Aτ - 1
```

because `Ymulti` has `c` saturated β entries plus the sorted tail, while the full sorted `M` has the extra `aS_0`.

But the positional suffix `ws_i = [M^{i+2},…,M^L]` removes `M^0` and the positional block `M^1,…,M^{i+1}` from the full list, so

```text
cLt(ws_i, τ) = Aτ - ετ - pτ.
```

Therefore in region `(b)` the desired inequality is equivalent to

```text
Aτ - 1 ≤ Aτ - ετ - pτ
```

i.e.

```text
pτ + ετ ≤ 1.
```

Since `hlo : M^{i+1} < τ`, we already have `pτ ≥ 1`. Thus the goal is equivalent to

```text
pτ = 1  and  ετ = 0,
```

namely

```text
M^0 ≥ τ
M^1,…,M^i ≥ τ
M^{i+1} < τ.
```

So the positional suffix has enough small widths precisely because the dropped positional prefix is mostly **not** below `τ`.

That is not an achiever-only or qFM-free structural fact. The achiever data, `good_floor_core`, `aS_le_bp1`, `aS_succ_le_Yvec`, and sorting/permutation invariance only see the sorted multiset of widths. They do not control which original positions were dropped by `ws_i`. Sorting `ws_i` does not fix this: `sorted(ws_i)` is the sorted positional suffix, not a global sorted tail.

So region `(b)` cannot avoid the dropped-prefix assertion. Proving

```text
c + #{aS_{c+1..L} < τ} ≤ cLt(ws_i, τ)
```

is exactly proving that the dropped positions contain no extra `< τ` widths beyond `M^{i+1}`. That is the band/window content.

**Clean Correct Structure**

Use an in-order induction.

1. Prove/assume band for all indices `< i`.

2. From band-at-`< i` plus `hhi : τ ≤ uTel_i`, derive the window fact:

```text
M^1,…,M^i ≥ τ.
```

Together with `hlo`, this gives

```text
#{M^1,…,M^{i+1} < τ} = 1.
```

3. Separately, from qFM feasibility `qFM_j ≥ M^{j+1}` and telescoping, get

```text
uTel_i ≤ M^0,
```

hence `τ ≤ M^0`.

4. Now prove `static_count`.

Region `(a)`, `τ ≤ b + 1`, can use the achiever arithmetic/count lemmas.

Region `(b)`, `b + 1 < τ`, use the exact count identities above; the inequality becomes equality once `M^0 ≥ τ` and the dropped-prefix count is exactly one.

5. Use `static_count(i)` to prove the stage-`i` Dom/count obligation, then obtain band at `i`.

This induction is well-founded because `static_count(i)` uses only band facts at strictly smaller indices `< i`; it does not use band at `i`.

Bottom line: the lemma is true, but the reason is band-dependent. Any proof that claims to be qFM-free must still smuggle in the equivalent dropped-prefix fact.