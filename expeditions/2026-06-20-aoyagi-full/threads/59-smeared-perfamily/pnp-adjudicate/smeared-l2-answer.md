**FACTS**

**Q1(a).** Off the pole, `P1ᵀ P1` invertible means `P1` has full column rank. Then

`P1 * Lam0 = P1 (P1ᵀP1)⁻¹ P1ᵀ P2`

is the orthogonal projection of `P2` onto `col(P1)`. Hence cancellation holds iff

`col(P2) ⊆ col(P1)`.

For a free generic `M0 x M1` matrix with `s > 0`, this is automatic exactly when `P1` generically spans the whole ambient column space `R^M0`, i.e.

`r = M0`.

Since `s > 0` means `r < M1`, the non-vacuous generic condition is:

`r = M0 < M1`.

If `r < M0`, cancellation fails generically. Exact example: take `M0=2, M1=2, r=1`, `P1 = (1,0)^T`, `P2 = (0,1)^T`. Then `Lam0 = 0`, so `P1 Lam0 = 0 ≠ P2`.

If `r > M0`, `det(P1ᵀP1)` is identically zero, so the off-pole chart is empty.

**Q1(b).** In the `L=2` front-bottleneck case, `r = min(M0, M1)` and `s = M1 - r`.

| case | `r` | `s` | shape of `P1` | cancellation |
|---|---:|---:|---|---|
| `M0 < M1` | `M0` | `M1-M0 > 0` | square `M0 x M0` | holds generically; `P1` invertible, so `col(P1)=R^M0` |
| `M0 = M1` | `M0=M1` | `0` | square, all of `A0` | vacuous; no `P2` |
| `M0 > M1` | `M1` | `0` | tall `M0 x M1` | vacuous; no `P2` |

There is no wide `P1` in the bottleneck case, since `r=min(M0,M1) ≤ M0`.

**Q1(c).** No. If `s > 0`, then `r < M1`. But if also `r = min(M0,M1)`, this forces `r = M0`, hence `P1` is square. A genuinely tall `P1` would require `r < M0`, so the minimum would have to be `r = M1`, which gives `s = M1-r = 0`.

So the adversarial tall/free/generic failure case exists only for a non-bottleneck split, not for the `L=2` bottleneck split with `s>0`.

**Q2(a).** Assume `δ > 0`, square `P1 ∈ R^{r x r}`, diagonal entries in `[δ/2, δ]`, off-diagonal entries bounded by `δ/8`, and entries of `P2` bounded by `δ/8`.

Let

`μ_r = 1/2 - (r-1)/8 = (5-r)/8`.

For `r ≤ 4`, `μ_r > 0`. Write `P1 = D + E`, with `D` diagonal. Then

`||E||₂ ≤ (r-1)δ/8`

and therefore

`σ_min(P1) ≥ δ/2 - (r-1)δ/8 = δ μ_r`.

Thus

`λ_min(P1ᵀP1) ≥ δ² μ_r²`.

Also,

`||P2||₂ ≤ δ sqrt(r s)/8`.

Since square full-rank `P1` gives

`(P1ᵀP1)⁻¹ P1ᵀ = P1⁻¹`,

the clean estimate is

`||Lam0||₂ ≤ sqrt(r s) / (5-r)`.

Entrywise, a sharper max-norm argument gives, for every entry,

`|Lam0_ab| ≤ 1 / (5-r)`, for `r ≤ 4`.

So for `r=2`, this gives `|Lam0_ab| ≤ 1/3`; for `r=4`, `|Lam0_ab| ≤ 1`.

**Q2(b).** The bound does **not** survive arbitrary `r` with the fixed `δ/8` off-diagonal conditioning.

For any `r ≥ 5`, set `q = 1/(2(r-1)) ≤ 1/8`, and take the exact matrix with diagonal `δ/2` and all off-diagonal entries `-qδ`. Then the all-ones vector is in the kernel, so `P1` is singular while satisfying the conditioning.

Worse, off the pole the inverse is unbounded. Take diagonal `(1/2+t)δ`, off-diagonal `-qδ`, with rational `t > 0`. Then the all-ones vector has eigenvalue `δ t`. If `P2 = (δ/8) * 1`, then

`Lam0 = P1⁻¹ P2 = (1/(8t)) * 1`,

so entries blow up as `t → 0`.

Thus the stated conditioning gives a uniform inverse bound only when

`1/2 > (r-1)/8`, i.e. `r ≤ 4`.

More generally, if off-diagonal entries are bounded by `βδ` and `P2` entries by `ηδ`, the same proof works under

`μ = 1/2 - (r-1)β > 0`,

with

`λ_min(P1ᵀP1) ≥ δ² μ²`,  
`|Lam0_ab| ≤ η / μ`.

The delta-scaling is exactly stable: inverse contributes `δ⁻¹`, `P2` contributes `δ`, so `Lam0 = O(1)` in `δ`. The obstruction is not delta; it is the missing `r`-dependent diagonal-dominance margin.