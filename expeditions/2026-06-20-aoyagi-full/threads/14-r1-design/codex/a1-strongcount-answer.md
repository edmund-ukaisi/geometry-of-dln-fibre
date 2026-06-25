codex
**Summary**
- Region split is optimal: Region T (`τ ≤ M^{i+1}`) follows immediately from the tight-chain dominance `eraseIter_dom`, and Region A (`M^{i+1} < τ ≤ head'_i`) needs the separate static achiever bound; no leaner proof removes this dichotomy without re-proving the same ingredients.
- In Region A we combine `submultiset` with the static bound `cLt(Ymulti, τ) ≤ cLt(ws_i, τ)` for `M^{i+1} < τ ≤ u_i = head'_i`. This static bound is derived by sorting both sides and invoking `good_floor_core` at the index `m := cLt(Ymulti, τ)`; `aS_succ_le_Yvec` transfers the good-floor inequality from sorted suffix widths to the positional suffix `ws_i`.
- The `good_floor_core` clause is pointwise in τ: `u_i` appears only to delimit the τ-window; the inequality itself does not depend on any choice of earlier picks, so Region A’s proof is non-circular.

**Region Decomposition**
- Region T proof stops at the tight-chain inequality `cLt(R_i, τ) ≤ cLt(M^{i+1} :: ws_i, τ)` and the indicator drop; nothing from the achiever enters.
- Region A necessarily reuses the static achiever fact, because direct tight-chain control leaves a +1 slack, and every alternative route reinstates the same inequality under another name.

**Achiever Mechanism**
- For `τ` in Region A set `m := cLt(Ymulti, τ)`; the β-block contributes `0`, `c−r`, or `c` elements depending on τ relative to `b` and `b+1`, so `m ≤ c`.
- `good_floor_core` yields `c · aS_m ≤ Sprefix(c+1) + (m − 1)`; the LHS counts `m` copies of the `m`-th sorted width, while the RHS is the total width budget still available in the top `c+1` slots.
- Because `τ ≤ u_i`, the telescope guarantees the suffix budget in `ws_i` dominates the demand of `m` widths below τ. Sorting those suffix widths gives `aS_m ≤ τ`, and `aS_succ_le_Yvec` aligns each sorted suffix entry with the corresponding target in `Yvec`, letting us conclude `cLt(sorted ws_i, τ) ≥ m`.
- Finally, removing the sort only increases counts: the positional suffix `ws_i` contains those `m` small widths somewhere in its tail, so `cLt(ws_i, τ) ≥ m = cLt(Ymulti, τ)`.

**Dependence on `u_i`**
- `u_i` is defined from past picks but only gates the τ-range. The inequality `cLt(Ymulti, τ) ≤ cLt(ws_i, τ)` comes entirely from the fixed pool structure and suffix widths; it holds for every τ in the stated interval independently of how `u_i` was reached, so there is no circular dependence.

No gaps spotted; all ingredients are accounted for and well-justified within the stated hypotheses.
tokens used
