1. **OK.** The Schur complement is `B22 - B21 * Δ⁻¹ * B12`, so `S = 0` is exactly `B22 = B21 * Δ⁻¹ * B12`. The dimensions compose correctly: `(l×m) * (m×m) * (m×n) = l×n`, matching `B22`.

2. **OK.** `rank = Fintype.card m` is the right formalization of “rank exactly r” when `m` indexes the pivot block. Since `Δ` is invertible, `rank M ≥ card m`; Guttman rank additivity gives `rank M = rank Δ + rank S = card m + rank S`, so equality holds iff `S = 0`. No edge case suggests `rank = card m` with nonzero Schur complement, or conversely.

3. **OK.** With rows `(m⊕l)` and columns `(m⊕n)`, the intended sizes are `p = card m + card l`, `q = card m + card n`. Thus `Matrix m n k` is `r×(q-r)` and `Matrix l m k` is `(p-r)×r`; no transposition problem.

4. **OK.** The iff is genuine: `[Invertible Δ]` only supplies a two-sided inverse for `Δ`; it imposes no condition on `B22`. The equality `B22 = B21 * ⅟Δ * B12` is an actual rank-cutting equation.

5. **OK.** `{rank = card m ∧ IsUnit toBlocks₁₁.det}` faithfully encodes the exact-rank-`r` locus intersected with the chart where the top-left pivot block is invertible. Over a field, `IsUnit Δ.det` is equivalent to `Δ ∈ GL_r`.

6. **OK.** This honestly proves the parameter-space `finrank` identity and the arithmetic identity for `δ`, not a variety-dimension theorem. Deferring “open subset has ambient dimension” is the right algebraic-geometry boundary unless the repo already has a developed Zariski/topological dimension API.

7. **OK.** The listed names do not overclaim as described: `rank_fromBlocks_eq_card_iff_schur` names the exact iff, `pivotRankChartEquiv` is a type/k-point equivalence, and the dimension names explicitly say `params` or arithmetic `delta`. I would only avoid names like `dim_pivotRankChart` unless a genuine variety-dimension theorem is proved.