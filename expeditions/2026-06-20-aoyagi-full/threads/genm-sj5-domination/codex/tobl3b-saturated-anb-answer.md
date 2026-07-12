Overall verdict: **CLOSES.** Under F1–F4, the \(a<b\) saturated shell has no extra Gram singularity and no charge deficit.

### Q1 — CLOSES

Let \(U\) denote the \(b-a\) surviving corank rows. At \(j=r=a\),

\[
p=a-r=0,\qquad q=b-r=b-a.
\]

Schematically, up to bounded Jacobians and additional nonnegative squares, the saturated contribution is

\[
\int
\det(Q_UQ_U^{T})^{-p/2}
\bigl(\mathcal L_{\mathrm{red}(t+r)}+R(U,Z,\ldots)\bigr)^{-e_r}
\,dU\,d(\text{deep variables}).
\]

Here

\[
-\frac p2=0,\qquad e_r=c'.
\]

Thus the apparent Gram factor is not a singular expression \(0^0\); it is literally the absent factor

\[
\det(Q_UQ_U^T)^0 := 1,
\]

as forced by F1’s zero-row case. Consequently,

\[
\int_{\Box_U}1\,dU=\operatorname{vol}(\Box_U)<\infty
\]

uniformly even when \(Q_U=0\), \(Z=0\), or \(Z\) genuinely loses rank.

The full loss may still be infinite on an exact zero slice. That is different from a divergent Gram weight: joint local integrability near that slice is what F4 addresses.

### Q2 — CLOSES

For \((3,4,4)\), \(t^*=1\), \(r=2\),

\[
e_r=c'<5<6
=\operatorname{carrierThreshold}(3,4).
\]

The surviving rows contribute either:

- a finite-volume nuisance integration, after dropping their nonnegative square terms; or
- variables already retained inside the reduced comparator.

They do not produce an additional determinant divisor. Hence the saturated term is controlled by the \((3,4)\) comparator IH, while F4 supplies the required joint integrability in the \(Z\to0\) tube.

So “surviving-corank weight \(\times\) comparator IH” is valid provided “weight” means the constant \(1\), not a hidden \(\det^{-1/2}\).

### Q3 — CLOSES

At every saturation boundary \(r=\min(a,b)\),

\[
(a-r)(b-r)=0.
\]

Therefore

\[
C_r=\minAdm(\operatorname{redChain}(t^*+r)M).
\]

F3 explicitly guarantees, by convexity telescoping,

\[
C_r\geq \minAdm(M),
\]

including when the freed corner is empty. In this example,

\[
C_r=12>10=\minAdm(3,4,4).
\]

Thus the zero corner is anticipated by the telescoping inequality; it does not create an undershoot.

### Q4 — CLOSES; no adversarial configuration exists under F1–F4

I cannot construct either requested obstruction:

- Setting \(Z=0\) makes every candidate Gram matrix singular, but its exponent is zero, so the surviving-row weight remains \(1\).
- The saturated charge cannot undershoot because that would directly contradict F3’s banked inequality.

An exact zero slice can have an infinite pointwise loss-power value, but F4 says its surrounding joint integral is finite. That is not an under-charge or surviving-row divergence.

### Q5 — CLOSES

Indeed,

\[
t^*+r
=t^*+\min(M_0-t^*,M_1-t^*)
=\min(M_0,M_1).
\]

Thus every \(j>r\) would give

\[
t^*+j>\min(M_0,M_1),
\]

so such cuts are illegal. Further rank degeneration is already lumped into \(S_r\) and handled by the Morse rescue, not by deeper cuts.

For \((3,4,4)\),

\[
t^*+r=1+2=3,
\]

and the recursion bottoms out at the leaf \((3,4)\), whose threshold \(6\) strictly exceeds \(c'<5\). The corner closes cleanly.