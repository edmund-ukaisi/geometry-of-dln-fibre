**KILL-CONDITION VERDICT: YES.**

For the `deepRank = 0` L=2 achiever, the binding radial divisor has exactly the headline ratio

\[
\frac{(M_0M_1-1)+1}{2}=\frac{M_0M_1}{2}=\frac{\minAdm(M)}2.
\]

There is no exponent mismatch.

**Collapsed Form**

For \(M=(M_0,M_1,M_2)\), `tStar = (0,0)` gives

\[
\minAdm(M)=Mval(0,0)=M_0M_1.
\]

The zero-rank achiever center is the stratum where the rank block

\[
E\in \operatorname{Mat}_{M_0\times M_1}
\]

vanishes. The leaf block has size

\[
\text{deepRank}\cdot M_2 = 0\cdot M_2=0,
\]

so there is no leaf pivot.

In local coordinates the singular part of the loss is

\[
F(E,G,\xi)=\|E\,G\|_F^2
\]

up to regular/invertible frame factors, where \(G\) denotes the downstream \(M_1\times M_2\) factor and \(\xi\) denotes spectator/frame variables. For \((1,1,2)\), this is the familiar scalar form

\[
F=e^2\|G\|^2,
\]

or, in a prior blow-up parametrisation, \(w_0^2w_1^2\|W_2\|^2\). The threshold is still \(1/2\).

**Blow-Up**

Let \(d=M_0M_1\). Blow up the full \(E\)-block radially with one pivot \(p\):

\[
E=z\,\bar E,\qquad \bar E_p=1.
\]

Then

\[
|\det D\phi|=|z|^{d-1}
\]

and

\[
F\circ\phi
= z^2\,\|\bar E\,G\|_F^2
= z^2 U(\bar E,G,\xi).
\]

Thus the pulled-back integrand has the binding one-variable factor

\[
|z|^{d-1}\,|z^2U|^{-c'}
= |z|^{d-1-2c'}\,U^{-c'}.
\]

At \(c'=d/2\),

\[
d-1-2c'=d-1-d=-1,
\]

so the \(z\)-integral is logarithmically divergent. For \(c'>d/2\), it is worse. Hence the radial divisor realizes exactly \(\frac12M_0M_1\).

**BOUNDED vs WALL**

Cheapest route:

1. **Thin specialization of the clean radial pattern, but on the zero-rank \(E\)-block.**  
   Use `pivotBlowupOn` on the \(M_0M_1\) active \(E\)-coordinates. Determinant is the generic `|u_p|^(M0*M1-1)`. Rate is the same `z²·U` homogeneity argument.

2. **Not the smeared square chart with `r=0`.**  
   The smeared chart needs a nonempty rank block and pivot (`0 < r`). At `r=0`, the top block is empty and the Gram/shear machinery has no pivot to bind.

3. **Not genuinely new chart math.**  
   It is new wiring/classification, not new analysis: no rational shear, no leaf LDU pivot, no new monomial calculation.

**Proven-Arithmetic vs Inference**

Proven/banked arithmetic:
- `deepRank = 0` gives the leaf term \(0\cdot M_2=0\).
- `minAdm = M0*M1` follows directly from `Mval_tStar_eq` at `tStar=(0,0)`.
- The active-count identity is the same `rBlock*cBlock` budget: only the first \(E\)-block survives.

Inference / still to formalise for this handler:
- The dedicated zero-rank collapsed-rate theorem `routeMCore (E-radial φ u) = z²·U`.
- The `U` a.e.-positivity/nonzero-polynomial witness, though it is the same all-ones/nonzero product style as the clean chart.
- Optional exact-finiteness below \(M_0M_1/2\) for the full pulled-back integral; the lower-bound atom only needs the logarithmic divergence at and above the headline rate.