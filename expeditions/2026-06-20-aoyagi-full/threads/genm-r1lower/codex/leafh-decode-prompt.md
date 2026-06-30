# Codex consult: Lean 4 match-reduction decode (the genm-ambdet thrash-point)

Lean 4 + Mathlib v4.29. I'm proving `leafH_diagAxis`. After `rw [interiorLive_leafH, if_neg …, diagAxis, Equiv.apply_symm_apply, liveLeafHOnIdx]` the goal is (verified):

```
⊢ (match
      (frameSplitEquiv M (tach M) (0 + 1) ⋯ ⋯)
        ((frameSplitEquiv M (tach M) (0 + 1) ⋯ ⋯).symm (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i, i)))))) with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>
      if (finProdFinEquiv.symm qK).1 = (finProdFinEquiv.symm qK).2 then
        Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2) + (Wext M (0 + 1) - Text M (tach M) (0 + 2)) +
          2 * (Text M (tach M) (0 + 2) - 1 - ↑(finProdFinEquiv.symm qK).1)
      else 0
    | x => 0)
  = Text M (tach M) 1 - Text M (tach M) 2 + (Wext M 1 - Text M (tach M) 2) + 2 * (Text M (tach M) 2 - 1 - ↑i)
```

The `⋯ ⋯` are proof args `(ha.hdesc 0 _) (ha.hub 0)`. `frameSplitEquiv … k …` is an `Equiv` (a `_ ≃ _`). The scrutinee is `e (e.symm X)` with `X = Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i, i))))`.

WHAT FAILS:
- `simp only [Equiv.apply_symm_apply]` — does NOT reduce the scrutinee (goal unchanged; match stays).
- `rw [Equiv.apply_symm_apply (frameSplitEquiv M (tach M) (0+1) (ha.hdesc 0 (by norm_num)) (ha.hub 0))]` — "did not find pattern".
- `have hround : e (e.symm X) = X := Equiv.apply_symm_apply _ _; rw [hround]` — hround typechecks but `rw [hround]` "did not find pattern".

The blocker (genm-ambdet's note): the match-discriminant `(0:Fin 2).val + 1` (from `diagAxis`, where `frameSplitEquiv` is applied at literal `(0:Fin 2).val+1`) vs `k.val + 1` (in `liveLeafHOnIdx` after the outer `match ⟨k, Sum.inl s⟩` binds `k = ⟨0,_⟩`) — proof-irrelevant but syntactically distinct `frameSplitEquiv` instances (different `hdesc`/`hub` proof args, or `(0:Fin 2).val` vs `0`), so `rw` (syntactic) can't bridge and `simp [Equiv.apply_symm_apply]` won't fire on the coe form.

`frameSplitEquiv M t s hdesc hub : (Fin … ⊕ …) ⊕ … ≃ …` (a Mathlib `Equiv` built from `finCongr`/`Equiv.sumCongr` pieces). `finProdFinEquiv : Fin a × Fin b ≃ Fin (a*b)`.

QUESTION: what's the robust Lean 4 idiom to reduce `e (e.symm X)` → `X` inside a `match` scrutinee when `e` carries proof args that may not be syntactically identical to a hand-written copy? Options I'm considering: (a) `conv` to the scrutinee + `rw [Equiv.apply_symm_apply]` (does conv's `rw` tolerate the instance better?); (b) `simp only [Equiv.apply_symm_apply]` with `(config := …)`; (c) `generalize`/`set` the equiv as `e` first so the two occurrences unify, THEN `rw [Equiv.apply_symm_apply e]`; (d) `dsimp only [diagAxis, liveLeafHOnIdx]` to force defeq match-reduction before the round-trip; (e) prove via `Fin.cases`/`decide` on `i`? (i : Fin (Text 2), opaque width — decide won't work). Give the most likely-to-work idiom + a fallback. Concise.
