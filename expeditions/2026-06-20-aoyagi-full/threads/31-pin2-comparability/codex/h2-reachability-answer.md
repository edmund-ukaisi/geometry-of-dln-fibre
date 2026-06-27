**FACT**

Yes, the curve is reachable under the stated chart rules.

- `X1` can be chosen to make `P00 = I` exactly:
  \[
  A_1=A_0^{-1}(I-Y_0Z_1),\qquad X_1=A_1-I.
  \]
  For small `Y0,Z1` this is near `0` and invertible, and `X1` is a free spectator coordinate.

- `Z0 = -T0 Z1 A1^{-1}` is a valid free choice. It is a reg coordinate, but the loss reads `P10`, not the raw coordinate norm. This makes `P10=0`; the raw coordinate is only `Θ(t^2)` and costs nothing once the product block is nulled.

- `Y1 = A0^{-1}(E(t)-Y0T1)` is also valid. Taking `E(t)=Θ(t^3)` gives `P01=E(t)` and forces `Y1=Θ(t^2)`, again a legal reg-coordinate choice.

After these choices:
\[
S_{\rm reg}=\|E(t)\|_F^2.
\]
If `E(t)=λt^3E0`, then `Sreg = λ^2\|E0\|^2t^6`.

The per-layer Schur cores remain
\[
S_0=T_0+O(t^3),\qquad S_1=T_1+O(t^3),
\]
so generically `coreΦ = ||S0S1||² = Θ(t^4)`. The exact identity is
\[
R_{\rm core}=S_0(I-K)S_1,\qquad K=Z_1P_{00}^{-1}Y_0.
\]
Here `P00=I`, so `K=Z1Y0=Θ(t^2)`, hence
\[
R_{\rm core}-S_0S_1=-S_0KS_1=Θ(t^4),
\]
and generically
\[
\left|\|R_{\rm core}\|_F^2-\|S_0S_1\|_F^2\right|=Θ(t^6).
\]

For a fixed nonzero `λ`, `G/Sreg` tends to a finite constant. But `λ` is freely tunable, so the constants are not uniform; taking `λ→0` makes the ratio arbitrarily large. Stronger: taking `E(t)=0` gives `Sreg=0` while the gap is still generically `Θ(t^6)`, so the additive bound fails pointwise.

A scalar embedded witness makes this explicit:
\[
Y_0=Z_1=T_0=T_1=t,\quad A_0=1,\quad A_1=1-t^2,
\]
\[
Z_0=-\frac{t^2}{1-t^2},\qquad Y_1=-t^2+\lambda t^3.
\]
Then `P00=1`, `P10=0`, `P01=λt^3`, and
\[
\frac{G}{S_{\rm reg}}\to \frac{2}{\lambda^2}
\]
for `λ≠0`; for `λ=0`, `Sreg=0` and `G>0`.

**INFERENCE**

No hidden chart constraint blocks this path, given the grounding rule that the reads are free independent coordinates. `coreAbsorb` is a shear/change of variables, not a relation among `X1,Y0,Z1,T0,T1,Y1,Z0`. The path stays small, keeps `A0,A1,P00` invertible, and therefore lies in the ordinary determinant-open neighborhood such as `S5a`.

**FINAL**

The additive bound
\[
\left|\|R_{\rm core}\|_F^2-\mathrm{core}\Phi\right|\le C\,S_{\rm reg}
\]
does **not** survive on the real chart domain under these constraints. It is broken by a reachable curve. The failure is enabled by the spectator/gauge status of `Y0` and `Z1`, which create the middle factor `K=Z1P00^{-1}Y0` without being charged by `Sreg`; `X1` also helps by cancelling `P00` at no regular-energy cost.