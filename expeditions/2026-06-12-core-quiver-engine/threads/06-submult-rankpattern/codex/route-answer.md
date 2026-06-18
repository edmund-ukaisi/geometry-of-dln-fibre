Recommended: **third route**, absolute-upper `Nat.leRec`. Ranking: third > shifted-tail > dependent fold. It avoids manufacturing a shifted `Tuple` and keeps all type alignment inside one auxiliary step; shifted-tail spreads casts across `A'` plus final reindex, and dependent fold gives no Mathlib monoid sugar.

```lean
def submult (d : Fin (N+1) → ℕ) (A : Tuple (k := k) d)
    (i j : Fin (N+1)) (hij : i ≤ j) :
    Matrix (Fin (d j)) (Fin (d i)) k :=
  Nat.leRec
    (motive := fun m _ => (hm : m < N+1) →
      Matrix (Fin (d ⟨m, hm⟩)) (Fin (d i)) k)
    (fun _ => 1)
    (fun {m} _ rec hm =>
      let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ hm⟩
      show Matrix (Fin (d p.succ)) (Fin (d i)) k from
        A p * (show Matrix (Fin (d p.castSucc)) (Fin (d i)) k from
          rec p.castSucc.isLt))
    hij j.isLt
```

Single public bridge lemma:

```lean
@[simp] theorem submult_zero_eq_multPrefix (j : Fin (N+1)) :
  submult d A 0 j (Fin.zero_le j) = multPrefix d A j
```

Then `mult d A = submult d A 0 (Fin.last N) ...` is just `unfold mult` plus this lemma, with orientation adjusted by `rw [← submult_zero_eq_multPrefix]`.

Diagonal rank:

```lean
def rankPattern ... (i j : Fin (N+1)) (hij : i ≤ j) :=
  (submult d A i j hij).rank
```

`submult d A i i le_rfl = 1` is not definitionally `rfl`, but should close by `simp [submult]` using `Nat.leRec_self`. Then, under `[Nontrivial k]`, `rankPattern d A i i le_rfl = d i` closes by `simp [rankPattern, submult, Matrix.rank_one]`. `Matrix.rank_one` requiring `[Nontrivial k]` is verified in v4.29.

Successor lemma is **not `rfl`**:

```lean
@[simp] theorem submult_succ (p : Fin N) (h : i ≤ p.castSucc) :
  submult d A i p.succ (Nat.le_succ_of_le h) =
    A p * submult d A i p.castSucc h
```

It needs `Nat.leRec_succ` and the local `show` alignment above. Arbitrary proof arguments may need proof-normalisation.