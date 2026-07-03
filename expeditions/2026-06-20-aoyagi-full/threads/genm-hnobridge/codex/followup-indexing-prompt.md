# Follow-up: resolve the off-by-one against the ACTUAL Lean index convention

In the previous consult you flagged a possible off-by-one in "raise Text(s) for s∈[q+1,b]". That was
because my prompt used a lossy convention `x_s = tStar(s)`. Here is the ACTUAL Lean convention; please
confirm whether the implementation is CORRECT under it.

## Actual Lean objects

- `tStar : Fin L → ℕ`, indices `j ∈ {0,...,L−1}`.
- `tach := Fin.cons (M 0) tStar`, so `tach(0)=M(0)` and `tach(k+1)=tStar(k)`.
- `Text(0)=M(0)`; `Text(k+1)=tach(k)`. Hence **`Text(1)=tach(0)=M(0)`** and
  **`Text(k+2)=tach(k+1)=tStar(k)`**, i.e. `Text(s)=tStar(s−2)` for `s ≥ 2`, and `Text(0)=Text(1)=M(0)`.
- `Wext(s)=M(s)`.
- Block index `j ∈ {0,...,L−1}` ↔ boundary `s=j+1`. Proven bridges:
  `rBlock(j) = Text(j+1) − Text(j+2)`  and  `cBlock(j) = Wext(j+1) − Text(j+2) = M(j+1) − tStar(j)`.
- row-drop at boundary `s`: `Text(s+1) < Text(s)` ⟺ `rBlock(s−1) > 0`.
- col-drop at boundary `s`: `Text(s+1) < Wext(s)=M(s)` ⟺ `cBlock(s−1) > 0`.

## The Lean move (`raiseTup`)

Given interior both-drop at `s₀`, first tail col-failure `b` (with `s₀ < b ≤ L−1`, so `c_b=0`,
`c_s>0` for `s∈[s₀,b−1]`), and `q` = last row-drop in `[s₀,b−1]`, the Lean code raises the
**`tStar`-index block `[q−1, b−2]`**: `raiseTup(j) = tStar(j) + (1 if q−1 ≤ j ≤ b−2 else 0)`.

Two lemmas are proven (I have independently numerically verified both — 32k and 736k random
hypothesis-satisfying cases, 0 failures — but I want your independent read):

- `Mval_raiseTup`: with flatness `rBlock=0` on block `[q, b−2]` and `cBlock(b−1)=0`,
  `Mval(raiseTup) = Mval(tStar) + (1 − rBlock(q−1) − cBlock(q−1))`.
- `raiseTup_mem_Adm`: with `rBlock(q−1)>0` and `cBlock(j)>0` for `j∈[q−1,b−2]`, `raiseTup ∈ Adm`.
  (per-layer bound: raised entries `tStar(j)+1 ≤ admBound(j)`; the `q=1`/`j=0` corner needs
  `tStar(0)+1 ≤ min(M0,M1)`, using rBlock(0)>0 ⟹ tStar(0)<M0 AND cBlock(0)>0 ⟹ tStar(0)<M1;
  weak-decrease bottom at `j=q−1` uses the row-drop; last-zero since `L−1 ∉ [q−1,b−2]`.)

## Questions

Q1. Under THIS convention (`tach=Fin.cons(M0,tStar)`, `Text(k+2)=tStar(k)`), is raising the
`tStar`-index block `[q−1, b−2]` the CORRECT move (i.e. does it correspond to your earlier "correct"
plateau raise, now that boundary `s`'s residual `cBlock(s−1)=M(s)−tStar(s−1)` involves `tStar(s−1)`,
not `tStar(s)`)? In particular: does it raise `tStar(b−1)` (the entry with `cBlock(b−1)=0`)? It must
NOT — confirm the top raised entry is `tStar(b−2)`, whose cap is protected by `cBlock(b−2)>0`.

Q2. Confirm `Mval_raiseTup`'s per-`j` delta collapses to `j=q−1` with value `1−rBlock(q−1)−cBlock(q−1)`
(interior `j∈[q,b−2]` contributes `−rBlock(j)=0` by flatness; the entry `j=b−1` contributes
`+cBlock(b−1)=0`). Any residual off-by-one at the endpoints `q−1` or `b−2`?

Answer plainly: is the LEAN implementation (block `[q−1,b−2]`) correct under this convention, or is
there still a real bug?
