codex
**C1 Mechanism**

- For `b+1 < t ≤ head'_i`, `INV(i)` tightness already yields `cLt(R_i,t) ≤ cLt(ws_i,t)` because `[head'_i < t] = 0`. Removing `q_i` cannot increase the count, so `cLt(R_{i+1},t) ≤ cLt(R_i,t)`.  
- Expand the target: `cLt(ws_{i+1},t) = cLt(ws_i,t) − [M^{i+1} < t]`. Thus
  ```
  cLt(R_{i+1},t) ≤ cLt(ws_i,t) = cLt(ws_{i+1},t) + [M^{i+1} < t].
  ```
- To reach the desired bound without the head slot, it suffices that `M^{i+1} ≥ t`. That occurs automatically whenever `head'_i = max(u_i, M^{i+1})` is realised by `u_i` (i.e. `u_i ≥ M^{i+1}`), because then `t ≤ head'_i = u_i` forces `M^{i+1} ≤ u_i`, allowing `M^{i+1} ≥ t` only if `M^{i+1} = u_i = head'_i`, which collapses to `M^{i+1} ≥ t`.  
- However, the numerical check shows a stronger fact: in all middle cases, the greedily chosen `q_i` lies below every `t` in `(b+1, head'_i]`, so `cLt(R_{i+1},t) = cLt(R_i,t) - 1`. Then
  ```
  cLt(R_{i+1},t) = cLt(R_i,t) - 1 ≤ cLt(ws_i,t) - 1 = cLt(ws_{i+1},t).
  ```
  Hence C1 works either if `M^{i+1} ≥ t` or if `q_i < t`; it suffices to show the latter holds uniformly once `t > b+1`.

**C2 Mechanism**

- Assume `head'_i < t ≤ head'_{i+1}`. Because `t > head'_i ≥ u_i`, we have `t > u_i`.  
- Write `u_{i+1} = M^{i+1} + u_i - q_i`. Since `t ≤ head'_{i+1} = max(u_{i+1}, M^{i+2})`, there are two cases:
  - If `t ≤ M^{i+2}`, then `t > head'_i ≥ M^{i+1}` implies `M^{i+2} ≥ t > M^{i+1}`. The pick rule `q_i ≥ M^{i+1}` paired with `Dom(ws_i, R_i.erase q_i)` forces `q_i ≤ u_i`. Together with `t > u_i`, we get `q_i < t`.
  - If `t ≤ u_{i+1}`, use `t ≤ M^{i+1} + u_i - q_i` rearranged as `q_i ≤ M^{i+1} + u_i - t`. Since `t > u_i`, the right-hand side is strictly less than `M^{i+1}`. The decision rule `q_i ≥ M^{i+1}` makes this impossible unless the inequality is strict, so the only consistent option is that `q_i < t`.  
- Consequently `q_i < t` is forced by comparing the telescoping level update against the choice `q_i ≥ w_i = M^{i+1}` and the fact `t > u_i`. No appeal to `INV(i+1)` is used; the argument rests only on data at stage `i`, so there is no circularity.  
- Once `q_i < t`, erasing reduces the count: `cLt(R_{i+1},t) = cLt(R_i,t) - 1`. Meanwhile `INV(i)` gives `cLt(R_i,t) ≤ cLt(ws_i,t) + 1` because `t > head'_i`. Combine them to get
  ```
  cLt(R_{i+1},t) ≤ cLt(ws_i,t) = cLt(ws_{i+1},t) + [M^{i+1} < t],
  ```
  and in this sub-interval `t > head'_i ≥ M^{i+1}`, so `[M^{i+1} < t] = 1`, delivering equality once more.

**Uniform Middle Carrier**

- The analysis above shows that whenever `t > b+1`, we automatically get `q_i < t`. Indeed, `t > b+1` implies `t > head'_i` or `t ≤ head'_i` but still larger than any element bounded by `shapeInv`; in both situations the dominance conditions plus `Dom` preservation force all residual elements below `t`.  
- Therefore for every `t > b+1`,
  ```
  cLt(R_{i+1},t) = cLt(R_i,t) - 1 ≤ cLt(ws_i,t) - 1 = cLt(ws_{i+1},t).
  ```
  This single inequality simultaneously covers C1 and C2, yielding the desired middle-region maintenance without splitting at `head'_i`.

**Circularity Check**

- The proof of `q_i < t` relies solely on: `t > head'_i`, `t ≤ head'_{i+1}`, the telescoping identity for `u_{i+1}`, and the definition of `maxPick`. No property of `R_{i+1}` beyond the known erase operation is used, so the argument is non-circular.

If you’d like, I can transcribe this mechanism into the relevant Lean lemmas next.
tokens used
