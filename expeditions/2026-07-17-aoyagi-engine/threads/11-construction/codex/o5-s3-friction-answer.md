### §1 — Fin literal

Best: avoid the case split entirely using the banked bridge:

```lean
theorem envVal_le_admBound (M : Fin (L + 1) → ℕ) (k : Fin L) :
    envVal M k ≤ admBound M k := by
  simpa only [envVal, runMinWidth_eq_widthMinUpto] using
    (runMinWidth_le_admBound M k)
```

If the literal equality is still needed, normalize its value separately:

```lean
have hone : ((1 : Fin (L + 1)) : ℕ) = 1 := by
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (Nat.succ_lt_succ hL)

have hM1 : M (1 : Fin (L + 1)) = M ⟨k.val + 1, by omega⟩ :=
  congrArg M (Fin.ext (by simpa [hk0] using hone))
```

This avoids asking `omega` to work inside the opaque `OfNat Fin` reduction.

### §2 — seam

Replace both placeholders with:

```lean
      · -- seam: p in prefix, q beyond
        rw [if_pos hpi]
        have hqj : j ≤ q := by
          rw [Fin.le_def]
          omega
        have haqj : a q ≤ a j := hdec j q hqj
        calc
          a q ≤ a j := haqj
          _ ≤ a i := Nat.le_of_lt hdesc
          _ = widthMinUpto M j.val := hsat
          _ ≤ widthMinUpto M (p.val + 1) :=
            widthMinUpto_mono M (by omega)
      · -- both beyond
        rw [if_neg hpi]
        exact hdec p q hpq
```

The last `omega` uses `p.val ≤ i.val` and `i.val + 1 = j.val`.

### §3 — strict Mval drop

Let `μ T k` denote the `k`th `Mval` summand. The clean Lean decomposition is pointwise under `Finset.sum_lt_sum`, rather than explicitly rewriting `univ` as three unions:

- Prefix `k.val ≤ i.val`: prove `μ splice k = 0` using `widthMinUpto_succ`; then `0 ≤ μ a k` by `mval_term_nonneg`.
- Boundary `k = j`: unchanged because the current value is `a j` and the new predecessor is
  `envVal M i = a i`.
- Suffix `j.val < k.val`: unchanged because both the current coordinate and its predecessor lie beyond the splice.

Obtain strictness from the bad prefix coordinate `m`. If every prefix summand of `a` were zero, `prefix_forces_env` would give the forbidden equality at `m`. Hence obtain

```lean
∃ k : Fin L, k.val ≤ i.val ∧ μ a k ≠ 0
```

For that `k`, `mval_term_nonneg` upgrades nonzero to `0 < μ a k`, while `μ splice k = 0`. Finish with the verified Mathlib lemma:

```lean
refine Finset.sum_lt_sum (fun k _ => hterm_le k) ?_
exact ⟨k, Finset.mem_univ k, hterm_strict⟩
```

The strict term is this contrapositive-produced `k`, not necessarily the original bad coordinate `m`.

### §4 — every minimizer

First prove the generic statement:

```lean
ha   : a ∈ Adm M
hmin : ∀ b ∈ Adm M, Mval M a ≤ Mval M b
⊢ Clearable M a
```

Negating `Clearable` yields `i`, `j`, the adjacent saturated descent, and a bad prefix coordinate. The splice is admissible by `spliceEnv_mem_Adm` and strictly cheaper by §3, contradicting `hmin`.

Then specialize to `tStar` using:

```lean
tStar_mem M
Mval_tStar_eq_inf' M
Finset.inf'_le _ hb
```

Keep this argument in `ℤ`. Using `minAdm` introduces an unnecessary `Int.toNat` round trip; it is safe only via the banked nonnegativity result. No `hL : 0 < L` is needed for clearability—the `L = 0` case is vacuous.