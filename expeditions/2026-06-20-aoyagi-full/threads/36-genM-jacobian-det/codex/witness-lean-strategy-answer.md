**Verdict**
Yes, the plan is sound. The main adjustment is Lean-facing: keep row value `0`, but express it through the canonical cast/natAdd forms expected by `bmatStack_top` and `chainA_apply_natAdd`.

1. **Constant `rowPath = 0`**
Mathematically sound. If `q` is deepest with `0 < Text q`, then by descent `0 < Text s` for every `s ≤ q`, so the row family

```lean
def i0T (s : ℕ) (hs : 0 < Text M t s) : Fin (Text M t s) := ⟨0, hs⟩
```

is enough. Do not try to use one global `i₀`; the types differ. Also expect to prove cast-shape lemmas like:

```lean
have hrow :
  i0T s hs =
    Fin.cast (show Text M t (s+1) + (Text M t s - Text M t (s+1)) = Text M t s by omega)
      (Fin.castAdd _ (i0T (s+1) hs1)) := by
  apply Fin.ext
  simp [i0T]
```

That is what lets `bmatStack_top` fire.

2. **Survival induction**
Your `P s` induction is right. I would implement it as an auxiliary induction on `d`:

```lean
have surv_aux : ∀ d, d ≤ q → P (q - d) := by
  intro d hd
  induction d with
  | zero =>
      simpa using base_q
  | succ d ih =>
      have ih' : P (q - d) := ih (by omega)
      exact step_survives (s := q - (d+1)) (by omega) ih'
have surv0 : P 0 := by
  simpa using surv_aux q le_rfl
```

For the matrix product step:

```lean
rw [Matrix.mul_apply]
rw [Finset.sum_eq_single i0_next]
· -- main term
  rw [B_row0_delta_self, one_mul]
  exact ih
· -- other columns
  intro t _ ht
  rw [B_row0_delta_ne ht, zero_mul]
· intro hmem
  exact (hmem (Finset.mem_univ _)).elim
```

`bmatStack_top` is enough for `s > 0`; it reduces the row to `K 0 t`, and your witness `K = 1` gives the Kronecker delta. There are no “other rows” to prove vanish in this sum. Handle `s = 0` separately because `Bmat 0` is the reindexed identity, not `bmatStack`.

3. **Zero above `q`**
Yes, prove the whole matrix zero separately:

```lean
∀ s, q < s → s ≤ L → c.Hmat s _ = 0
```

Base: `s = L`, use `Hmat_last` and `Rfin = 0`.

Step:

```lean
rw [Chain.Hmat_succ c s hsL, ih]
rw [Matrix.mul_zero]
have hE : c.E s = 0 := ...
rw [hE, Matrix.zero_mul, add_zero]
```

This is cleaner than entry-wise zero and makes the base at `q` much easier.

4. **Carrier suffix**
Important correction: since `toChain.E q = Rmat q * A q`, the carrier `W_q` is inside the `E_q` term. So either prove the suffix product from `q`, not only from `q+1`,

```lean
suffix_carrier :
  ∀ s, q ≤ s → s ≤ L →
    c.suffix s _ (w0 s) (w0 L) = ω ^ (L - s)
```

or prove the `E_q * suffix(q+1)` contribution directly. I prefer rewriting

```lean
(c.E q * c.suffix (q+1) _) = c.Rmat q * c.suffix q _
```

using `E = Rmat * A`, `suffix_succ`, and associativity.

For `s ≥ q`, `Text (s+1) = 0`, so `chainA` is entirely the natAdd/lift block. Use only:

```lean
chainA_apply_natAdd
```

after proving row `0` is the natAdd row with `t = 0`:

```lean
have hrow :
  w0 s =
    Fin.cast (genWidthEq M t hle s hsL)
      (Fin.natAdd (Text M t (s+1)) a0) := by
  apply Fin.ext
  simp [hText_succ_zero]
rw [hrow, chainA_apply_natAdd]
```

No castAdd/top-block cases are needed; any `Fin 0` branch should be avoided or closed by `Fin.elim`.

5. **Decomposition**
The five-lemma plan is right, with one rename/fusion:

- width facts: `Text s > 0` for `s ≤ q`, `Text s = 0` for `q < s ≤ L`
- witness block laws: `B_row0_delta`, `Rmat_zero_off_q`, `Rmat_q_pivot`, `W_row0_delta`
- `Hmat` zero above `q`
- suffix carrier from `q` to `L`
- survival from `q` down to `0`

Hardest sublemma: the witness block laws over `genBlkFlatStruct`, especially proving nonchosen `readE/readW/readK` slots are zero via `chartIdxEquiv`/role-split injectivity. The telescope inductions are routine once those entry laws exist.

**Risk Ranking**
High: off-by-one in the carrier term: `W_q` lives in `E_q = Rmat_q * A_q`.

High: flat-slot disjointness/zero proofs for the witness.

Medium: cast-shaping `⟨0,_⟩` into `Fin.castAdd`/`Fin.natAdd` forms.

Medium: special case `s = 0` for `Bmat 0`.

Low: `Finset.sum_eq_single` and the `Hmat` zero induction.
