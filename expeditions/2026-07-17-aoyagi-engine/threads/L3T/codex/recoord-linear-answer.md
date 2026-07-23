Yes—your `C` is mathematically correct. The existing `coreGen` fiber-sum pattern is also the cleanest Lean route.

1. Sum reindex

I would slightly normalize the inner coefficient:

```lean
let ai := if i = cx then 0 else readEntry d u s.layer i b
if blockEntryFlat d (s.layer + 1) rx i = some j then ai else 0
```

This is equivalent to your conjunction but makes the collapse cleaner. For each `i`, establish:

```lean
∃ fc,
  blockEntryFlat d (s.layer + 1) rx i = some fc ∧
  fc ∈ X ∧
  readEntry d u (s.layer + 1) rx i = u fc
```

Then:

```lean
rw [Finset.sum_congr rfl (fun j _ ↦ Finset.sum_mul _ _ _),
    Finset.sum_comm]
```

and, for each `i`:

```lean
simp only [hB, Option.some.injEq, ite_mul, zero_mul]
rw [Finset.sum_ite_eq, if_pos hfcX, hread]
```

No injectivity is needed: the collapse happens separately for each fixed `i`.

For the identity term `if j = x`, use the primed orientation:

```lean
simp only [ite_mul, one_mul, zero_mul]
rw [Finset.sum_ite_eq', if_pos hx]
```

2. Bridging the range bound

Use `Fin.ext`, but do not globally rewrite the resulting dependent `Fin` equality through the whole summand. That can fail because `qx.1.2` depends on `qx.1.1`.

```lean
have hlayFin : qx.1.1 = ℓ' :=
  Fin.ext (by simpa [ℓ'] using hlayNat)

have hwidth : d qx.1.1.castSucc = d ℓ'.castSucc :=
  congrArg (fun k : Fin N ↦ d k.castSucc) hlayFin
```

Then rewrite only with:

```lean
rw [hwidth]
```

This avoids the dependent-motive failure. The condition

```lean
if i = (qx.2 : ℕ) then ...
```

is unaffected because both sides are naturals.

For the row bound, isolated simplification works:

```lean
have hrx : rx < d ℓ'.succ := by
  simpa only [hlayFin] using qx.1.2.isLt
```

3. `hC`

Your proposed route is exactly right. Factor these two helpers:

```lean
blockEntryFlat d S row col = some fc →
  fc ∈ layerCoords d S
```

and

```lean
S ≠ L →
(∀ k, k ∉ layerCoords d L → u k = v k) →
readEntry d u S row col = readEntry d v S row col
```

For the second helper, split `readEntry`. The `none` case is `rfl`; in the `some fc` case, compare decoded layers using `decode_layer_of_mem_layerCoords`. No global disjointness lemma or bounds are required.

Then prove `hC` via:

```lean
refine (ignoresCoords_univ_iff_agree _ X).mpr ?_
```

and use the read helper termwise. Here `s.layer ≠ s.layer + 1` is discharged by `omega`. In fact, the proof does not need the hypotheses `x ∈ X` or `j ∈ X`.

4. v4.29 traps

- `Finset.sum_ite_eq`: condition `a = x`.
- `Finset.sum_ite_eq'`: condition `x = a`.
- `Option.some.injEq` exists; `Option.some.inj_iff` does not.
- `blockEntryFlat`’s proof-dependent guards reduce with `dif_pos`, not `if_pos`.
- Neither `Finset.sum_range` nor `Fin.sum_univ_eq_sum_range` is needed here; staying with natural-number ranges avoids casts.
- Avoid `Finset.sum_image`; explicit image-membership witnesses are simpler.
- When splitting on `cx = a`, prefer a targeted `rw [if_pos hguard]`. A broad `simp [hguard]` may rewrite `cx` throughout the fiber sum and stop an already-proved reindex identity from matching.