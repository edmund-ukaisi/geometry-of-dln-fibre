**Conclusion**

With only the stated tools and the single charge inequality, I do **not** see a valid bounded-domain route for the whole chart `U`. The obstruction is real: the `q`-pivot may go to zero inside the closure of `U`, and the A₀ Morse estimate that would feed the reduced-tail IH is not uniform there. That lower-rank boundary needs separate rank-stratum estimates or extra `minAdm` inequalities.

Here is the exact failure.

Write the product blockwise, using the chosen row/column split:
```text
P = [ B  E ]
    [ C  D ],      B = P[ρ,κ] invertible on U,
A₀ = [ X  Y ].
```

The measure-preserving shear from (T3),
```text
X' = X + Y C B⁻¹,
S  = D - C B⁻¹ E,
```
gives the exact identity
```text
A₀ P = [ X' B,  X' E + Y S ].
```
So there is no clean split yet; the cross term `X'E` is genuinely present.

One can remove the cross term by an orthogonal output change. Let `U₀ = [B E]`, choose orthogonal `O` with
```text
U₀ O = [G 0],   G Gᵀ = U₀ U₀ᵀ,
[0 S] O = [H Z].
```
Then after the shear `X'' = X' + Y H G⁻¹`,
```text
‖A₀P‖²_F = ‖X'' G‖²_F + ‖Y Z‖²_F.
```
This is the honest Morse/residual split. By (T4), `rank Z = rank S`, so `Z` is the reduced quotient block. But the Morse coefficient `G` degenerates exactly when the `q`-row block of `P` approaches rank `< q`.

If one now scales `R = X''G`, with `d = m₀q`, then for fixed `Y,Z`:
```text
∫ (‖X''G‖² + ‖YZ‖²)^(-c') dX''
 = |det G|^(-m₀) ∫_{R-domain} (‖R‖² + ‖YZ‖²)^(-c') dR.
```
Using (T1), when `c' > d/2`,
```text
≤ |det G|^(-m₀) · C_resid(d,c') · ‖YZ‖^(-2(c' - d/2)).
```
The desired reduced exponent would be
```text
s = c' - m₀q/2,
```
and the bookkeeping is fine:
```text
2s = 2c' - m₀q
   < minAdm(M) - m₀q
   ≤ minAdm(redTail).
```
So `s < ½ minAdm(redTail)`.

But analytically this estimate has the factor `|det G|^(-m₀)`. Nothing in the stated IH controls that factor. It blows up near the closure stratum where the largest `q`-minor tends to zero.

Avoiding the scaling does not solve it. The bounded estimate
```text
∫ (‖X''G‖² + w)^(-c') dX'' ≤ Vol · w^(-c')
```
is uniform in `G`, but it feeds exponent `c'`, not `c' - m₀q/2`, to the reduced block, and the charge inequality does not imply `c' < ½ minAdm(redTail)`.

The obstruction already appears in the scalar chart. Take `m₁=m_L=q=1`, so `P=a`, `U={a≠0}`, and `A₀=x∈[-1,1]^{m₀}`. Then
```text
frobSq(A₀P) = a² ‖x‖²,
```
hence
```text
J = (∫_{-1}^1 |a|^(-2c') da)
    (∫_{[-1,1]^{m₀}} ‖x‖^(-2c') dx).
```
The second integral is finite iff `c' < m₀/2`; the first is finite iff `c' < 1/2`. Thus the chart integral is finite iff
```text
c' < 1/2.
```
But the only allowed charge inequality gives merely
```text
minAdm(M) ≤ m₀q = m₀,
```
which, for `m₀>1`, does not imply `c' < 1/2`. The missing input is precisely a lower-rank/pivot-minor estimate.

A finite largest-minor cover does not fix this. Sets such as
```text
V_λ = { A' ∈ U : |Δ_λ(P)| = max_μ |Δ_μ(P)| }
```
are finite and measurable, since there are finitely many minors and the conditions are polynomial inequalities. They bound graph ratios, but not the magnitude of the largest minor. Along paths approaching rank `< q`, every `|Δ_λ| → 0`. In the scalar model the dyadic shells give
```text
∑_n ∫_{2^{-n-1}<|a|≤2^{-n}} |a|^(-2c') da
  ≍ ∑_n 2^{n(2c'-1)},
```
which diverges for `c' ≥ 1/2`. So the deepest boundary cannot be handled by a finite cover with summable constants.

What would be sufficient is an additional bounded-domain induction over lower-rank strata, or stronger hypotheses controlling the pivot degeneration. Away from that boundary, e.g. on `|det G| ≥ η > 0`, the route above is mechanisable: use the exact orthogonal split, apply (T1), then feed `s=c'-m₀q/2` to the reduced-tail IH. But on the whole open chart `U`, the constants necessarily blow up as the `q`-pivot collapses.