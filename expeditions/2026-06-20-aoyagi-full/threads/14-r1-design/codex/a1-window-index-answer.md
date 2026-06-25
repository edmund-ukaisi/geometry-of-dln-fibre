codex (window-index check)
**β-Block Counts**

- The balanced β-block in `Ymulti` has `c` entries indexed as `Yvec_0,…,Yvec_{c-1}`; it contains exactly `c−r` copies of `b` and `r` copies of `b+1` by construction, so `#{β=b+1}=r` and `#{β<b+1}=c−r` exactly. This matches `count_bp1_le`, which bounds the sorted widths `aS_1,…,aS_c` by `r` but does not specify `Ymulti`; no index clash occurs.
- For `M^{i+1} < τ ≤ u_i` the β-count is:
  - `0` when `τ ≤ b` (no β-entry is < τ),
  - `c−r` when `τ = b+1`,
  - `c` when `τ > b+1`.
  These values depend only on the β-block and therefore land within `{0,…,c}`; this ensures `m := cLt(Ymulti,τ) ≤ c`.

**Strict −1 Source**

- Because exactly one of the dropped widths `M^1,…,M^{i+1}` lies below `τ` in Region A, `cLt(Mwidths,τ) = cLt(ws_i,τ) + 1`.
- `Dom(Mwidths,Ymulti)` supplies `cLt(Ymulti,τ) ≤ cLt(Mwidths,τ)`. Combining with the previous identity yields the strict form `cLt(Ymulti,τ) ≤ cLt(ws_i,τ) − 1`.
- A direct β-count proof can reach the same inequality without detouring through `Dom`: sort both multisets so that `m := cLt(Ymulti,τ) ≤ c`, apply `good_floor_core` to bound `aS_m`, use `aS_succ_le_Yvec` to transfer the bound from the sorted suffix back to the positional suffix `ws_i`, and finally relate the sorted and positional counts. This path produces the `−1` automatically from the fact that `cLt(sorted ws_i,τ) = cLt(ws_i,τ)` while the prefix count on all widths exceeds by 1.

**Index Alignment**

- `Yvec_i` (0-indexed) corresponds to `aS_{i+1}`. The lemma `aS_succ_le_Yvec` states precisely `aS_{i+1} ≤ Yvec_i`, exhibiting the one-step shift.
- `count_bp1_le` operates on indices `1,…,c`, covering the same entries as the β-block but in the sorted `aS` view. Since there are exactly `c` β-entries, those correspond to `aS_1,…,aS_c`; the shift is consistent and there is no off-by-one.
- The suffix `ws_i = Mwidths.drop(i+1)` removes the first `i+1` positional widths; any comparison with the sorted data uses that the first `c` sorted entries lie within the β-window, so the same `m` value threads through `aS`, `Yvec`, and `ws_i` unchanged.

**Lean Derivation Sketch**

- Let `m := cLt(Ymulti,τ)`. Split `Ymulti` into β-block ⊎ tail; the β cases above show `m ≤ c`.
- By `good_floor_core` with index `m`, `c * aS_m ≤ Sprefix(c+1) + (m-1)`; since `τ > M^{i+1}` and `τ ≤ u_i`, the telescoping inequality ensures the suffix budget `ws_i` can host the first `m` widths below `τ`.
- `aS_succ_le_Yvec` realigns: `aS_{ℓ+1} ≤ Yvec_ℓ ≤ τ` for `ℓ < m`, proving the first `m` sorted suffix entries lie below `τ`.
- Because sorting cannot decrease a less-than count, `cLt(ws_i,τ) ≥ m = cLt(Ymulti,τ)`, completing the target inequality for Region A with the strict `−1` already in place once we fold back the relation to `cLt(Mwidths,τ)`.
