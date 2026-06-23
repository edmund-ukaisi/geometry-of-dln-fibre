Certain strategy: use a **different feasible witness**, namely the backward min-suffix greedy.

```lean
def pM (M) : List ℤ :=
  backwardGreedy (Mwidths M) (Ymulti M)   -- Ymulti = Yvec achiever
```

For every `k`, prove `prefix_k pM ≥ S'_k`, then use your prefix-max theorem:

```lean
prefix_k (forwardMax b Y) ≥ prefix_k pM ≥ S'_k
```

Exact invariant: prove the suffix form for `pM` by backward induction on `j`.

At the state after positions `j+1, ..., L-1` have been chosen, with remaining pool `Rj` and chosen tail sum `Tj`, maintain:

```lean
I1 : Dom ((Mwidths M).take j) Rj
I2 : Tj ≤ ∑ i in Finset.Icc (j+1) L, Mseq M i
```

At step `j`, backwardGreedy chooses the smallest live value `x ≥ M^{j+1}` preserving `Dom`. Strengthen the live-candidate lemma to the window form:

```lean
∃ y ∈ Rj,
  Mseq M (j+1) ≤ y ∧
  y ≤ (∑ i in Finset.Icc j L, Mseq M i) - Tj ∧
  Dom ((Mwidths M).take j) (Rj.erase y)
```

Then minimality gives `x ≤ y`, hence

```lean
Tj + x ≤ ∑ i in Finset.Icc j L, Mseq M i
```

so `I2` propagates. At `j = k`, this is exactly

```lean
suffix_k pM ≤ M^k + ... + M^L
```

and using `sum_Yvec = sum_M` gives

```lean
prefix_k pM ≥ M^0 + ... + M^{k-1} = S'_k.
```

The three key steps:

1. Prove `pM_perm` and `pM_feasible` from existing backwardGreedy specs under `Dom (Mwidths M) Yvec`.

2. Prove the window live-candidate lemma above from the achiever structure. This is where `good_floor_core` enters, packaged as the full-width majorization
   ```lean
   largestK (Yvec M) j ≥ largestK (Mseq M) j
   ```
   plus the sorted/Dom lower-fit facts.

3. Transfer to `forwardMax`:
   ```lean
   have hmax := forwardMax_prefixMax hDom pM pM_perm pM_feasible k
   exact le_trans hpM_prefix hmax
   ```

Concrete witness: `pM = backwardGreedy (Mwidths M) (Yvec M)`. It is a Lean-computable permutation of `Yvec`; no closed-form prefix is needed.

Riskiest step: the strengthened **live value below the upper window** lemma. That is the only genuinely Yvec-specific part; the rest is abstract greedy bookkeeping.