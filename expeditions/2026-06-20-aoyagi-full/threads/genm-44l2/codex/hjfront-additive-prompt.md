# Question: is the hJfront discharge an ADDITIVE BOUNDED re-arch, or does it need the arbitrary-choice abstraction?

## Setting (Lean 4 + Mathlib, a DLN-RLCT formalisation)
A deep linear network has layers `H : Fin (L+1) → ℕ`, params = a tuple of layer matrices, `prod` = their product. For a rank-`r` target `B : Matrix (Fin (H 0)) (Fin (H (last L))) ℝ`, `deepestPoint` is a CONSTRUCTED point of the fibre `{w | prod w = B}` with every layer rank exactly `r`. It is defined as `Classical.choice (deepestPoint_exists ...)` — its per-layer structure is NOT directly exposed (only `prod deepestPoint = B` + per-layer rank-`r` + some tail-vanishing facts are banked as `deepestPoint_isDeep`).

## The frame-pivot chooser
`deepestPoint_frame_pivot_exists` produces a pivot embedding `J : Fin r ↪ Fin (H (last L).succ)` for the deepest point's LAST layer. `J` comes from `exists_pivot_cols_of_rank V hVrank` where `V` = the top-`r` rows of `deepestPoint(lastLayer)`. `exists_pivot_cols_of_rank` uses `exists_linearIndependent'` — it picks an ARBITRARY maximal-independent column subfamily (a `choose`), NOT canonical/leftmost.

## The open hypothesis `hJfront`
The L=2 value lemma needs:
  `hJfront : (deepestPoint_frame_pivot_exists ...).choose.trans (finCongr ...) = frontEmbed`
i.e. the arbitrary pivot J equals the front embedding `k ↦ k` (Fin.castLE).

## What's available (the column-WLOG, sorry-free)
`headline_frontRowColPivot_exists` gives, at the ⨅-over-optimalSet level (the headline LHS, NOT a single point): a column permutation P + row permutation R such that `Bpr = B.submatrix R P` has its FRONT r columns full rank + TOP r rows full rank, and the ⨅ is invariant. So WLOG B has front-pivot columns + top-pivot rows.

## The row-side TEMPLATE that worked (DeepestLeadingBlock.lean)
For the htop ROW side, a banked lemma `deepestPoint_leadingBlock_isUnit` derives "deepest point's layer-0 leading r×r block invertible" from `htop` (B's top r rows full rank) WITHOUT editing deepestPoint_exists: via `deepestPoint_isDeep.1` (prod=B) + a front-peel (`prod = layer0 · reindex(rest)`) + a tail-column-vanishing fact on layer0, giving `top-r-rows(B) = (leading block) · Y`, then a rank-squeeze `r = rank(top-rows B) ≤ rank(leading block) ≤ r`.

## My proposed ADDITIVE route (no edit to the arbitrary chooser)
1. New Core lemma: `exists_front_pivot_cols_when_front_full_rank V (h : (V.submatrix id castLE).rank = r) : IsUnit (V.submatrix id castLE)` — front cols full rank ⟹ front embedding IS a valid pivot set. Trivial (square full-rank ⟹ unit).
2. New deepest-frame existence variant `exists_deepest_lastLayer_pivotFrame_front` / `deepestPoint_frame_pivot_exists_front` that RETURNS `J = frontEmbed` (built from the front pivot, NOT the arbitrary choose), conditional on a "last layer's top-r-rows front cols full rank" hypothesis.
3. The COLUMN-DUAL of DeepestLeadingBlock: derive "deepestPoint(lastLayer)'s top-r-rows have front r cols full rank" from B's front-pivot-columns fact (col-WLOG), via prod=B + a BACK-peel + last-layer tail-ROW-vanishing.
4. Re-thread the #44 L2 chain through the _front variant so its J IS frontEmbed by construction, discharging hJfront.

## Questions
1. Is step 3 (the column-dual peel) sound — does B's front-pivot-column structure transfer to deepestPoint(lastLayer)'s top-row factor's front columns, given prod=B and a back-peel? Or does the Classical.choice in deepestPoint genuinely block knowing the last layer's column structure (i.e. the last layer could route B's front columns through ARBITRARY internal columns)?
2. Is the whole route ADDITIVE+BOUNDED (~150-250 LoC, no edit to deepestPoint_exists or the arbitrary chooser), or is there a hidden dependency forcing an edit to the Classical.choice construction?
3. Any cleaner route I'm missing?
Answer concisely, focus on whether step 3 is sound and the route is additive.
