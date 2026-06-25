codex
**Route-A Maintenance**
- Your decomposition matches what the strong invariant forces: thresholds split into (i) legacy head range with immediate slack, (ii) the tight window where you pay the achiever/good_floor_core cost, and (iii) the fresh slice up to `head'_{i+1}` that relies on the telescope to show `q_i < t`. The “strengthen the IH” move does not erase the reasoning; it only cages it inside the invariant, so the analytical burden is still the same three-region split.

**Route-B Soundness**
- The proposed head monotonicity step is false in general: from `Dom(a::ws,R)` you can raise the head and *lose* dominance (e.g. `R=[2,1]`, `ws=[1]`, `a=2`, `a'=4`, where `Dom([2,1], [2,1])` holds but `Dom([4,1],[2,1])` fails at `t=3`). Hence the chain “Dom → raise head → maxPick_spec” has a missing lemma.
- To repair it you would need exactly the slack statement `cLt(R_i,t) ≤ cLt(ws_i,t)` on the interval `(M^{i+1}, head'_i]`, i.e. the strong-head restriction you were trying to avoid. Without that extra fact the maxPick witness ≥ `head'_i` is not guaranteed, so `q_i ≥ u_i` is unproved. The good_floor_core arithmetic would therefore reappear in the proof of this missing lemma, not just in the base case.
- With the gap acknowledged, the rest of your Route-B pipeline (maxPick_spec, le_maxPick, telescope update) is algebraically fine; the only unsound step is the monotonicity claim.

**Judgment**
- Because the maintenance proof for Route-B currently relies on an invalid monotonicity move, Route-A is the only invariant with a complete, trusted Lean proof. The deciding factor is the need for explicit slack control over the “new head” window: Route-A carries it as part of the invariant, whereas Route-B implicitly assumes it and therefore collapses until that lemma is supplied.

**Circularity Check**
- There is no circular dependence: `head'_i` depends only on earlier `q_k`, and the maintenance step uses `head'_i` from the induction hypothesis. The problem is the missing dominance lemma, not a circular definition.
tokens used
