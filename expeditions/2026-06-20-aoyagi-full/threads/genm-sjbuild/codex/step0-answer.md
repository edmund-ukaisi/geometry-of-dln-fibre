**Q1.** Yes, for fixed rank. If `rank(Q_b)=r`, then  
`Gamma ↦ Gamma Q_b` is `p` copies of the row map `x ↦ x Q_b`, so its linear rank is `p*r` and its kernel has dimension `p*(q-r)`. Those kernel directions are genuinely absent from `||Gamma Q_b||_F^2`, hence only contribute bounded box volume.

Caveat: use the **actual rank on the chart/stratum**. Generic rank `r` is not enough if the chart also contains lower-rank degeneration without stratifying.

**Q2.** Let `N = M_cur`, `Λ = minAdm(N)`, `τ = min(N_2,...,N_L)`, `p=N_0-t`, `q=N_1-t`, `r=min(q,τ)`. For a nonzero corank block, the terminal is genuinely load-bearing iff

\[
p>0,\qquad r<q,\qquad p r < \Lambda .
\]

Equivalently, in closed width form,

\[
t<N_0,\qquad N_1-t>\tau,\qquad (N_0-t)\tau < \operatorname{minAdm}(N).
\]

Reason: if `r=q`, regimes B and A cover below/above `pq/2`. If `r<q`, A is unavailable, and B leaves an admissible open gap exactly when `pr/2 < Λ/2`.

**Q3.** Counting formal `t=0` branches too; if you only count pivot charts, delete the `t=0` entries. No load-bearing chart occurs.

`M=(3,3,4)`: `minAdm=8`. Charts: `(3,3,4), t=0,1,2,3`. Here `τ=4` and `q=3-t≤4`, so `r=q` always. Covered by A/B/base.

`M=(2,2,2,2)`: `minAdm=3`. Root charts `(2,2,2,2), t=0,1,2`; children `(s,2,2), t=0..s` for `s=0,1,2`. In every case `q=2-t≤2=τ` or `p=0`. Covered by A/B/base.

`M=(3,3,3,4)`: `minAdm=7`. Root charts `(3,3,3,4), t=0,1,2,3`; children `(s,3,4), t=0..s` for `s=0,1,2,3`. Root has `q≤τ=3`; children have `q=3-t≤4=τ`, or `p=0`. Covered by A/B/base.

So for all three chains: **no monomial terminal is reached**.

**Q4.** Yes: for these three chains, the statement  
`(1/2)*minAdm(remChain) <= monomialThreshold(terminal)` is vacuous **as a reached-terminal invariant**. It is not a proof about arbitrary terminal data that the route never visits.

For a load-bearing chart such as `(3,4,2), t=1`, the clean non-circular check is local: on the `rank(Q_b)=2` chart, combine the missing core variables with the Gamma image. The variables `Qtilde_p` contribute `2` dimensions and `Gamma ↦ Gamma Q_b` contributes `4`, giving Morse dimension `6 = minAdm(3,4,2)`, hence threshold `3`. For deeper toric leaves, the clean test is to compute the normal-crossing/Newton monomial threshold from the terminal exponents and compare it to `minAdm/2`; citing Aoyagi gives the external value `rlct = C/2`, but is circular if the goal is to prove that value. The paper’s global RLCT payoff is exactly this `C/2` statement for the square-Frobenius product loss. ([arxiv.org](https://arxiv.org/abs/2411.19920?utm_source=openai))