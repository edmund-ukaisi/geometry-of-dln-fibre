codex
**Summary**
- The missing “−1” in the upward window comes from the β-block majorisation delivered by `good_floor_core`: in that range every element of `R_i` below `t` lies in the balanced split, and the floor bound forces at least that many suffix widths below `t`, so the +1 slack from the Dom chain cannot be realised.

**Mechanism in Hard Range**
- Fix the upward step with `head'_i < t ≤ M^{i+2} = head'_{i+1}` and assume `q_i ≥ t` and `t ≤ b+1`. Set `m := cLt(R_i,t)`; all `m` elements counted are β-block values ≤ `b+1`, hence `m ≤ c`.
- Apply `good_floor_core` at index `m`: writing `a_m` for the `m`th smallest width and `S(c+1)` for the prefix sum, the lemma states `c · a_m ≤ S(c+1) + (m-1)`. Since `q_i ≥ t` and `t` lies between `M^{i+1}` and `M^{i+2}`, we have `a_m < t ≤ b+1`.
- If the suffix had fewer than `m` entries below `t`, then among the first `c+1` widths there would be at most `(i+1)+(m-1)` values `< t`, forcing `a_m ≥ t` and contradicting the inequality above. Hence `cLt(ws_i,t) ≥ m`, and because `ws_{i+1}` removes only the `M^{i+2}` head (which is ≥ `t` in this range) we also have `cLt(ws_{i+1},t) = cLt(ws_i,t)`. Thus `cLt(R_{i+1},t) = m ≤ cLt(ws_{i+1},t)` supplies the “−1”.

**Induction Step**
- *Lower window (`t ≤ head'_i`)*: `STRONG(i)` already gives `cLt(R_i,t) ≤ cLt(ws_i,t)`; deleting `q_i` can only decrease the left-hand side, while `ws_{i+1}` differs from `ws_i` by removing `M^{i+2}`, giving `STRONG(i+1)` instantly.
- *Upward window (`head'_i < t ≤ head'_{i+1}`)*:
  - If `q_i < t`, then `cLt(R_{i+1},t) = cLt(R_i,t) - 1`, so the +1 slack from the Dom chain cancels and the target inequality holds.
  - If `q_i ≥ t`, the argument above shows `cLt(R_{i+1},t) = cLt(R_i,t) ≤ cLt(ws_i,t) = cLt(ws_{i+1},t)`, completing the step.
- Combine the two windows to obtain `STRONG(i+1)` from `STRONG(i)` without any appeal to counterexample search.

**Uniform Strengthening**
- A clean variant is to carry, alongside `STRONG(i)`, the β-floor conjunct  
  `BETA(i): ∀ t ≤ b+1, cLt(R_i,t) ≤ cLt(ws_i,t) + [t ≤ head'_i]`.  
  Base case: use `good_floor_core` with the initial pool (`i=0`) to witness equality for `t ≤ b+1`, so both `STRONG(0)` and `BETA(0)` hold.
- Maintenance: in the hard sub-case the proof above upgrades `BETA(i)` to `BETA(i+1)` with no extra case split, because once `t > head'_i` the indicator in `BETA` drops to zero and the `good_floor_core` bound forces tightness; when `t ≤ head'_i` the indicator persists and erasing `q_i` can only help.
- With `STRONG(i) ∧ BETA(i)` as the induction hypothesis, the upward extension is absorbed automatically, so the proof of `STRONG(i+1)` requires only the two easy subcases (erase decreases count vs. structural majorisation), eliminating ad hoc reasoning.

**Circularity Check**
- The proof uses `STRONG(i)` only on the sub-range that belongs to its hypothesis and invokes `BETA(i)` (secured via `good_floor_core`) for the new interval; neither argument assumes the conclusion for step `i+1`, so no circular dependency arises.
tokens used
