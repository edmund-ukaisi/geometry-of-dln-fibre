**1. PACKING**

Let `C_s = [[A_s,B_s],[D_s,E_s]]` and `P_k = [[p_k,q_k],[ell_k,*]]`.

For output `Q = schurChartRawGen C`, set for `0 ≤ s < L`:
```text
Q_s,11 = p_{s+1}
Q_s,12 = q_{s+1}
Q_s,22 = R_s = E_s - D_s p_{s+1}^{-1} q_{s+1}
Q_0,21 = ell_L = (P_L)_21
Q_s,21 = D_s                 for s ≥ 1
```

So the pattern is **not literally** “`C_s` top rows + prefix corner + `R_s`”. The top row is the **prefix-product** top row `(P_{s+1})_11,(P_{s+1})_12`; only for `s=0` is this also the top row of `C_0`. `recoverProductGen` should read
```text
[[p_L, q_L],
 [ell_L, ell_L p_L^{-1} q_L + R_0 R_1 ... R_{L-1}]]
```
from slot `L-1` top row, slot `0` lower-left, and the fold of the `22` slots.

**2. DOF CHECK**

Algebra fact: this exactly preserves coordinates. Each slot still contains `r^2 + r a_{s+1} + a_s r + a_s a_{s+1}` entries, with `a_s = H_s-r`; the bottom-left budget is `ell_L` once plus `D_s` for `s ≥ 1`.

The `nReg = r(H_0+H_L-r)` regular directions live in `(p_L,q_L,ell_L)`, i.e. final product `11/12/21`: slot `L-1` top row and slot `0` lower-left.

**3. INVERSE**

1. Read all `p_{s+1}, q_{s+1}, R_s`; set `p_0=I`, `q_0=0`, and `ell_L = Q_0,21`.
2. For `s=1,...,L-1`, read `D_s = Q_s,21`.
3. Recover
   ```text
   E_s = R_s + D_s p_{s+1}^{-1} q_{s+1}
   A_s = p_s^{-1}(p_{s+1} - q_s D_s)
   B_s = p_s^{-1}(q_{s+1} - q_s E_s)
   ```
   using only prefix pivots `p_s,p_{s+1}`.
4. Multiply the recovered suffix `S=C_1...C_{L-1}` and let `gamma=S_21` (`gamma=0` for `L=1`).
5. Set `A_0=p_1`, `B_0=q_1`, then
   ```text
   D_0 = (ell_L - R_0 gamma) p_L^{-1} p_1
   E_0 = R_0 + D_0 p_1^{-1} q_1.
   ```

**4. DEF STYLE**

INFERENCE: define the chart by the closed-form per-slot formula above, not by literally recursing with the `L=2` chart. The algebraic proofs can still be inductive, using the prefix-product recurrence and the Schur telescope from rungs 2-3. A recursive Lean definition is likely to concentrate dependent-width casts at every head/tail peel; the closed form concentrates casts in `partProd`, block projections, and a small number of prefix lemmas.

**5. SIMPLER OPTION**

INFERENCE: I would use this packing. It is already the simpler same-type design because `recoverProductGen` is just “read final regular blocks plus fold the `22` cores.” Packings that store `C_s` top rows avoid intermediate prefix rows in the output, but then the inverse/recover algebra becomes less triangular and loses the clean regular-direction readout.