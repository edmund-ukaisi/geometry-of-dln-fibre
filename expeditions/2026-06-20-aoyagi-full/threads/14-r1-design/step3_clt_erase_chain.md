# Step-3 `cLt_erase` chain — `cLt(ws_i,τ) = cLt(Mwidths,τ) − 1` (pp-hall → a114e07e)

The indexing-sensitive spot, pinned exactly (verified 0/13332). The off-by-one in my earlier message
("M^0..M^{i+1}", i+2 widths) was a conflation — RESOLVED below: the drop set is M^1..M^{i+1} (i+1 widths,
from `Mwidths`, which has NO M^0); M^0 enters separately in the Mfull bridge.

## The exact definitions (live @316c55f)
- `Mwidths M = List.ofFn (fun j : Fin L => (M j.succ : ℤ))` = `[M^1,…,M^L]` (length L; `Mwidths[k] = M^{k+1}
  = Mseq M (k+1)`). **NO M^0.**
- `ws_i := (Mwidths M).drop (i+1)` = `[M^{i+2},…,M^L]`.
- `Mfull := List.ofFn (fun i : Fin (L+1) => (M i : ℤ))` = `[M^0,…,M^L]` (length L+1). Used in
  `dom_Mtail_Yvec`; `hMfcons : Mfull = (M 0 : ℤ) ::ₘ (↑(Mwidths M))` is GREEN (line ~3484).
- GREEN: `Mwidths_drop_cons M k hk : (Mwidths M).drop k = Mseq M (k+1) :: (Mwidths M).drop (k+1)`.
- GREEN: `BGEngine.cLt_erase S a τ (ha : a ∈ S) : cLt S τ = cLt (S.erase a) τ + (if a < τ then 1 else 0)`.

## The Step-3 target: `cLt (ws_i) τ = cLt (Mwidths M) τ − 1`  (region A: M^{i+1}<τ, M^1..M^i≥τ)

The drop set is `Mwidths.take (i+1) = [M^1,…,M^{i+1}]` (i+1 widths). The clean form: peel them one at a
time off `Mwidths` via `cLt_erase` (or, cleaner, the recursive `Mwidths_drop_cons` + cLt_erase).

### The recursive form (cleanest — uses `Mwidths_drop_cons` directly)
Prove, by induction on the peel-count, the general fact, then specialize:
```lean
-- For each k ≤ i:  cLt (Mwidths.drop k) τ = cLt (Mwidths.drop (k+1)) τ + (if Mseq M (k+1) < τ then 1 else 0)
have hpeel : ∀ k, k < L →
    BGEngine.cLt ((Mwidths M).drop k : Multiset ℤ) τ
      = BGEngine.cLt ((Mwidths M).drop (k+1) : Multiset ℤ) τ + (if Mseq M (k+1) < τ then 1 else 0) := by
  intro k hk
  rw [Mwidths_drop_cons M k hk, ← Multiset.cons_coe,
      BGEngine.cLt_erase _ (Mseq M (k+1)) τ (Multiset.mem_cons_self _ _),
      Multiset.erase_cons_head]
```
Then telescope k = 0..i:  `cLt (Mwidths.drop 0) τ = cLt (Mwidths.drop (i+1)) τ + Σ_{k=0}^{i} [Mseq M (k+1) < τ]`.
`Mwidths.drop 0 = Mwidths`, `Mwidths.drop (i+1) = ws_i`, and the sum `Σ_{k=0}^{i} [M^{k+1}<τ] = #{M^1..M^{i+1}<τ}`.
```lean
have hsum : BGEngine.cLt (Mwidths M : Multiset ℤ) τ
    = BGEngine.cLt (ws_i : Multiset ℤ) τ
      + ∑ k ∈ Finset.range (i+1), (if Mseq M (k+1) < τ then 1 else 0) := by
  -- induction on i applying hpeel; or Finset.sum_range telescoping. (Mwidths.drop 0 = Mwidths: List.drop_zero.)
  ...
```
### The count `Σ_{k=0}^{i} [M^{k+1}<τ] = 1` (region A — uses the band-at-<i closer, NO good_floor_core)
Each term `[Mseq M (k+1) < τ]` for k ∈ [0,i] is the indicator on `M^{k+1}`:
- k = i: `[M^{i+1} < τ] = 1` (from `hlo : Mseq M (i+1) < τ`).
- k < i (so M^{k+1} = M^1..M^i): `[M^{k+1} < τ] = 0`, because `M^{k+1} ≥ τ`:
  `M^{k+1} ≥ uTel_{k+1}` (= `qFM_k ≥ uTel_k`, the band at k < i, from `hband_lt`; via the identity
  `Mseq M (k+1) ≥ uTel_{k+1} ⟺ qFM_k ≥ uTel_k` — uTel recurrence `uTel_{k+1} = Mseq M (k+1) + uTel_k −
  qFM_k`, `linarith`), and `uTel_{k+1} ≥ uTel_i ≥ τ` (`uTel_antitone_le` with k+1 ≤ i, + `hhi`).
  So `M^{k+1} ≥ uTel_{k+1} ≥ uTel_i ≥ τ` ⟹ `[M^{k+1}<τ] = 0`.
So `∑_{k=0}^{i} [M^{k+1}<τ] = 1`, giving `cLt(ws_i,τ) = cLt(Mwidths,τ) − 1`.

NB the indicator sum is over k ∈ range(i+1) = {0,…,i}, i.e. the i+1 widths M^1,…,M^{i+1}. NOT i+2; M^0 is
NOT among them (Mwidths starts at M^1). The "M^0..M^{i+1}" in my earlier message was wrong — it conflated
the Mfull list with Mwidths. CORRECTED: drop set = M^1..M^{i+1} (i+1 widths).

## The Step-2 → Step-3 bridge (where M^0 enters, separately)
The kernel (Step 2) gives `cLt(Mfull,τ) ≥ m+1` (aS_0..aS_m < τ; `Mfull` = all L+1 widths). Convert to
`Mwidths` via the green cons `hMfcons : Mfull = (M 0) ::ₘ Mwidths`:
```lean
have hMf : BGEngine.cLt Mfull τ = BGEngine.cLt (Mwidths M : Multiset ℤ) τ + (if (M 0 : ℤ) < τ then 1 else 0) := by
  rw [hMfcons, ← Multiset.cons_coe,  -- or use hMfcons directly as a Multiset cons
      BGEngine.cLt_erase _ (M 0 : ℤ) τ (Multiset.mem_cons_self _ _), Multiset.erase_cons_head]
have hM0 : ¬ ((M 0 : ℤ) < τ) := by  -- M^0 ≥ τ
  -- uTel_antitone_le (0 ≤ i): uTel_i ≤ uTel_0 = M^0; hhi: τ ≤ uTel_i. So τ ≤ M^0.
  have := uTel_antitone_le M hL (Nat.zero_le i) (le_of_lt (lt_of_lt_of_le hi (le_refl L)))  -- uTel_i ≤ uTel_0
  have hu0 : uTel M (qFM M) 0 = (M 0 : ℤ) := rfl
  omega  -- with hhi, hu0, the antitone bound
-- so cLt(Mwidths,τ) = cLt(Mfull,τ) (M^0≥τ) ≥ m+1.
```
Then: `cLt(ws_i,τ) = cLt(Mwidths,τ) − 1 ≥ (m+1) − 1 = m = cLt(Ymulti,τ)`. ∎

## Summary of the indexing (the controller's exact question)
- `ws_i = Mwidths.drop(i+1)` drops `Mwidths.take(i+1) = [M^1,…,M^{i+1}]` — **i+1 widths**, all from
  `Mwidths` (which is `[M^1,…,M^L]`, NO M^0).
- `#{M^1..M^{i+1} < τ} = 1` in region A (only M^{i+1}, by hlo; M^1..M^i ≥ τ via band-at-<i + antitone).
  ⟹ `cLt(ws_i,τ) = cLt(Mwidths,τ) − 1`.
- M^0 is SEPARATE: it's the head of `Mfull = M^0 ::ₘ Mwidths`; M^0 ≥ τ (uTel_antitone_le + hhi) ⟹
  `cLt(Mwidths,τ) = cLt(Mfull,τ)`. This is the Step-2(kernel, on Mfull) → Step-3(on Mwidths) bridge.
- So the chain is: Step 2 `cLt(Mfull,τ) ≥ m+1` → (M^0≥τ) `cLt(Mwidths,τ) ≥ m+1` → (drop i+1 widths, count 1)
  `cLt(ws_i,τ) = cLt(Mwidths,τ) − 1 ≥ m`. The off-by-one resolves: i+1 widths dropped from Mwidths, +1
  separately for M^0 in the Mfull→Mwidths step, totaling the i+2 "M^0..M^{i+1}" but split across the
  two distinct lists (Mfull vs Mwidths) — which is why working on Mwidths for the drop (count 1) and Mfull
  only for the M^0 step is the clean factoring.

Verified 0/13332 (cLt(Mwidths,τ)−cLt(ws_i,τ)=1 AND cLt(ws_i,τ)=cLt(Mfull,τ)−1). Reproducible /tmp/step3_indexing.py.
