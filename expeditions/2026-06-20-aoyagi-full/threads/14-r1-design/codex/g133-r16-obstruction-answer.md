**Verdict: none of Q1-Q3 fails, under the full all-pivot flag atlas described.** The remaining caveat is implementation-level: a Lean/formal atlas still has to carry the explicit branch/center data and the reduced-chain decrease proof.

**Q1: FACT.**  
Every admissible `t` is reachable. Put `t_0 = M[0]`. At stage `j`, the current tail chain has input width `t_{j-1}` and next width `M[j]`; choose the pivot branch where this first tail map has rank `t_j`. The active residual block has size
```text
(t_{j-1} - t_j)(M[j] - t_j),
```
with the first term `(M[0]-t_1)(M[1]-t_1)`. Summing over `j` gives exactly `Mval(M,t)`. Conversely, any such path records weakly decreasing ranks ending in `t_L=0`, hence an admissible `t`. So no admissible lower-codimension stratum is missed by the full pivot tree.

**Q2: FACT, as a divisorial statement.**  
Each exceptional coordinate enters the pulled-back loss with exponent exactly `2`, so `k_E=1`. The reason is multilinearity: the blow-up scales one active residual block linearly, hence the matrix product scales by `u`, and `F = ||product||^2` scales by `u^2`. Later Schur/transvection steps are unit-Jacobian and do not add more powers of the old exceptional coordinate. Residual cores may still vanish on subloci of the exceptional divisor, but later blow-ups introduce new coordinates, each again with `k=1`; this is not the same as one divisor having `k>=2`.

Checks on the named thin/asymmetric cases:
```text
M=(3,1,3):  Mval min = 3
M=(2,3,2):  Mval min = 4
M=(3,2,1):  Mval min = 2
M=(2,2,2,2,2): Mval min = 3
```
In each, the binding ratios are `Mval/2`, with `k=1`.

**Q3: FACT.**  
The descent terminates. At a nonterminal stage the reduced tail replaces a chain beginning with widths `(t_{j-1}, M[j], ...)` by one beginning with `(t_j, M[j+1], ...)`, or terminates if `t_j=0`. Since `t_j <= min(t_{j-1}, M[j])`, the measure “chain length, then sum of widths” strictly decreases. If no active minor/coordinate is available, the active residual block has size `0`; that is already terminal, not a stuck singular core.

So: **no concrete counterexample chain found; Q1-Q3 hold for the stated full pivot atlas.**