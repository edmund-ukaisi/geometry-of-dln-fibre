1. **Recommendation: B.**  
Use vector-level elementary transfers, but define a closed-form intermediate `V t`; this avoids `Multiset` surgery and keeps `srt`/`Tuple.sort` isolated.

2. **Intermediate Lemmas**

```lean
def smallestK (N k : ℕ) (q : Fin N → ℤ) : ℤ :=
  ∑ i ∈ Finset.range k, srt N q i

noncomputable def leastSet (N k : ℕ) (hk : k ≤ N) (w : Fin N → ℤ) : Finset (Fin N) :=
  (Finset.univ.filter (fun i : Fin N => (i : ℕ) < k)).image (Tuple.sort w)
```

```lean
lemma leastSet_card_sum
    (N k : ℕ) (hk : k ≤ N) (w : Fin N → ℤ) :
    (leastSet N k hk w).card = k ∧
    ∑ j ∈ leastSet N k hk w, w j = smallestK N k w
```

Main transfer lemma:

```lean
lemma smallestK_pair_spread
    {N k : ℕ} (hk : k ≤ N)
    {w w' : Fin N → ℤ}
    {lo hi : Fin N} (hne : lo ≠ hi)
    (hlo₁ : w' lo ≤ w lo)
    (hlo₂ : w' lo ≤ w hi)
    (hsum : w' lo + w' hi = w lo + w hi)
    (hfixed : ∀ r, r ≠ lo → r ≠ hi → w' r = w r) :
    smallestK N k w' ≤ smallestK N k w
```

For the corridor, define:

```lean
edgePad i := if h : (i : ℕ) < L then edgeQ ⟨i, h⟩ else 0

V t i :=
  if (i : ℕ) < t then edgePad i
  else if (i : ℕ) = t then u t
  else M i
```

Then prove the step:

```lean
lemma corridor_step
    (j : ℕ) (hj : j < L) (k : ℕ) (hk : k ≤ L + 1) :
    smallestK (L+1) k (V (j+1)) ≤ smallestK (L+1) k (V j)
```

with `lo = ⟨j+1, by omega⟩`, `hi = ⟨j, by omega⟩`.

3. **Single-Step Key Inequality**

Let `S := leastSet N k hk w`. If `hi ∈ S` and `lo ∉ S`, use

```lean
A := insert lo (S.erase hi)
```

otherwise use `A := S`.

Then:

```lean
smallestK N k w'
  ≤ ∑ j ∈ A, w' j        -- smallestK_le_subset
  ≤ ∑ j ∈ S, w j
  = smallestK N k w      -- leastSet_card_sum
```

The only nontrivial case is `hi ∈ S`, `lo ∉ S`:

```lean
∑ j ∈ insert lo (S.erase hi), w' j
  = ∑ j ∈ S.erase hi, w j + w' lo
  ≤ ∑ j ∈ S.erase hi, w j + w hi
  = ∑ j ∈ S, w j
```

using `hlo₂ : w' lo ≤ w hi`. The both-in case uses `hsum`; the `lo`-only case uses `hlo₁`; neither-in is fixed.

4. **Friction Risk**

The one Lean-friction point is the closed-form `V` step bookkeeping: proving only indices `j` and `j+1` changed through nested `if`s and `Fin` casts. Isolate `V_step_lo`, `V_step_hi`, and `V_step_fixed` simp lemmas; after that the induction is routine.

I would not use C or D as the main encoding. There is no reliable fixed closed-form witness subset `A_m`; the transfer history is doing real work, especially around the `M₀` mass. D works only as the **single-transfer** witness argument above, not as a no-induction proof of the whole corridor.