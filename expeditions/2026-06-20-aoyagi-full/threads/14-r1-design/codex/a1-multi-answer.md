codex
**Summary**  
- PROVED: Maintaining `STRONG(i)` ➔ `STRONG(i+1)` requires a fresh application of `good_floor_core`; base-only plus structural data is insufficient.  
- PROVED: The multi-threshold region is controlled uniformly by the single sorted-prefix majorization `∑_{j=1}^m R_{i+1}^{↓}[j] ≥ ∑_{j=1}^m (head'_{i+1}::ws_{i+1})^{↓}[j]` for every `1 ≤ m ≤ c`.  
- CONJECTURE (negative): There is no alternate once-only achiever route avoiding per-step `good_floor_core`; any such route would need a new invariant stronger than the green chain.

**Maintenance Step**  
- Removing `q_i` (with `q_i ≥ head'_i`) simultaneously loosens every binding rank in `(b+1, head'_{i+1}]`. The tight green chain `Dom(Mwidths.drop i, R_i)` gives control over thresholds above `M^{i+2}` but is silent on the `c`-block just below `head'_{i+1}`.  
- In that block the only available inequality tying together all ranks is `good_floor_core`: when restated in sorted-prefix form it bounds the deficit `δ_m = ∑_{j=1}^m (head'_{i+1}::ws_{i+1})^{↓}[j] - ∑_{j=1}^m R_{i+1}^{↓}[j]`.  
- Because the update deletes one of the potentially tight `c` elements, the deficit can become positive immediately after erasing `q_i`. Invoking `good_floor_core` reimposes `δ_m ≤ 0` for every `m`, restoring `STRONG(i+1)`.

**Multi-Threshold Coverage**  
- The thresholds that bind are exactly those whose ranks lie inside the `c`-block. Instead of checking each threshold, verify the single family  
  `∑_{j=1}^m R_{i+1}^{↓}[j] ≥ ∑_{j=1}^m (head'_{i+1}::ws_{i+1})^{↓}[j]` for `1 ≤ m ≤ c`.  
- This inequality is equivalent to the achiever statement `c·aS_m ≤ Sprefix(c+1)+(m-1)` after translating ranks to sorted-prefix sums. Thus one `good_floor_core` invocation simultaneously certifies every binding rank in the multi-threshold regime.

**Once-Only vs Per-Step `good_floor_core`**  
- Base-only propagation would require that the pair (green chain, base achiever) be closed under the update `R_i ↦ R_{i+1}`. Explicit instances respecting both hypotheses but violating `STRONG(i+1)` exist (the observed ≈42 % failures) because the update can drain the `c`-block without violating the green chain.  
- Therefore the extra fact needed to close the maintenance step is exactly the reapplication of the achiever inequality to the updated `c`-block; no weaker structural fact currently known suffices.  
- Any alternative once-only route must exhibit an invariant that (i) survives the `q_i` erasure, (ii) implies all `c` sorted-prefix bounds, and (iii) is derivable from the base achiever without invoking it again. No such invariant has been identified; in its absence the per-step use of `good_floor_core` stands as the only proved path.

**Circularity Check**  
- The maintenance proof consumes two independent inputs: (a) the green chain `Dom(Mwidths.drop i, R_i)` propagated by `maxPick_spec`, and (b) a fresh `good_floor_core` bound on the updated `c`-block. Neither is derived from the maintenance conclusion, so the argument is non-circular. If a new invariant is discovered, recheck that it does not implicitly depend on `STRONG(i+1)` before use.
tokens used
