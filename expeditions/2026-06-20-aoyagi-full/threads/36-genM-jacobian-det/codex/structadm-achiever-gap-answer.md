**Q1.** Confirmed. The precise bad index is `k = L` in `StructAdm.hdesc`:  
`Text M (tach M) (L+2) = 1` by saturation, while `Text M (tach M) (L+1) = tach M ⟨L, Nat.lt_succ_self L⟩ = tStar M (Fin.last (L-1)) = 0` for `0 < L`. Thus `hdesc L` asks for `1 ≤ 0`. This is not a real decoder need; the observed consumers use `k : Fin L` or an explicit `k < L`, so they never need the `k = L` clause.

**Q2.**
1. **A: lowest cost, best bedrock.** Small signature ripple in the shared decoder; hypotheses match actual use; `structAdm222` remains valid and easier; achiever path becomes admissible.
2. **B: medium/high cost, acceptable but less clean.** Good for concrete/full-rank anchors, but it leaves the overstrong shared structure in place and redoes reader/slot plumbing for the achiever.
3. **C: highest cost, weakest bedrock.** Parallel admissibility plus parallel decoder duplicates infrastructure and invites drift.

Recommendation: **do A**. The hidden risk is not semantic breakage; it is only that direct unfold/rfl proofs mentioning `ha.hdesc k`/`ha.hub k` must now mention the proof argument. If you also weaken `hc`, add a wrapper back to the unconditional form for `chartIdxEquiv`.

**Q3.**
```lean
structure StructAdm (M t : Fin (L + 1) → ℕ) : Prop where
  h0    : tDesc M t 0 = M 0
  hc    : ∀ p, p < L → tDesc M t (p + 1) ≤ Wext M (p + 1)
  hL    : 0 < L
  hdesc : ∀ k, k < L → Text M t (k + 2) ≤ Text M t (k + 1)
  hub   : ∀ k, k < L → Text M t (k + 2) ≤ Wext M (k + 1)
```

Consumer call-shapes:
```lean
-- readK/readX/readN/readE, with k : Fin L
frameSplitEquiv M t (k.val + 1)
  (ha.hdesc k.val k.isLt)
  (ha.hub   k.val k.isLt)

-- genBlkFlatStruct.Bmat, inside if hk : k < L
bmatStack M t (k + 1) (ha.hdesc k hk) ...

-- genBlkFlatStruct.Rmat, inside if hk : k < L
rmatPad M t (k + 1) (ha.hdesc k hk) (ha.hub k hk) ...

-- hleStruct
| 0, _ => ...
| k + 1, hk => exact ha.hub k (Nat.lt_of_succ_lt hk)
```

If `hc` is weakened too, define:
```lean
theorem hcStructFull (ha : StructAdm M t) :
    ∀ p, tDesc M t (p + 1) ≤ Wext M (p + 1) := ...
```
and pass `hcStructFull ha` to `chartIdxEquiv`. INFERENCE: that wrapper is the cleanest way to avoid widening the refactor into `RouteMChartIdx*`.