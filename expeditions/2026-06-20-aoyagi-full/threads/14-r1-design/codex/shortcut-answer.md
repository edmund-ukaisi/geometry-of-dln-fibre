Labels: **FACT** = direct algebra or given setup. **INFERENCE** = structural conclusion from that algebra.

**Verdict**

**FACT:** The strong shortcut is **not geometrically correct as a terminal one-blow-up resolution for general `L >= 3`**. It already fails in the test case `(2,2,2,2), t=(1,0,0)`: the candidate blow-up gives `F = u^2 * U`, but `U` is not a unit on the chart.

**FACT:** The arithmetic value is still correct under your established theorem: `RLCT_core = (1/2) min_t Mval(t)`. The suspect part is the “single final blow-up gives a unit” mechanism, not the final value.

**L=3 Check**

**FACT:** For `(2,2,2,2)` and `t=(1,0,0)`, `Mval(t) = (2-1)(2-1) + (1-0)(2-0) = 3`.

**FACT:** Use the same incidence chart:
\[
A=\alpha\begin{pmatrix}1&a\\ b&ab+\delta\end{pmatrix},\quad
B=\begin{pmatrix}u-ar&v-as\\ r&s\end{pmatrix},\quad
C=\begin{pmatrix}p&q\\ m&n\end{pmatrix}.
\]
Then
\[
AB=\alpha\begin{pmatrix}
u&v\\
bu+\delta r&bv+\delta s
\end{pmatrix}.
\]

**FACT:** Blowing up the codim-3 center `{δ=u=v=0}` in the `δ`-chart,
\[
\delta=\rho,\quad u=\rho\xi,\quad v=\rho\eta,
\]
gives
\[
ABC=\alpha\rho
\begin{pmatrix}
\xi p+\eta m&\xi q+\eta n\\
b(\xi p+\eta m)+rp+sm&b(\xi q+\eta n)+rq+sn
\end{pmatrix}.
\]

**FACT:** Therefore
\[
F=\alpha^2\rho^2 U,
\]
where
\[
U=(\xi p+\eta m)^2+(\xi q+\eta n)^2+
(b(\xi p+\eta m)+rp+sm)^2+
(b(\xi q+\eta n)+rq+sn)^2.
\]

**FACT:** The Jacobian contribution of this final blow-up is `ρ^2`; including the first `A` incidence chart gives `|Jac| = |α|^3 |ρ|^2` up to units. Thus on any open set where `U` is a unit, the `ρ` divisor has `(k,h)=(1,2)` and ratio `3/2 = Mval(t)/2`.

**FACT:** But `U` is not globally a unit. For example, if `C=0`, then `U=0` for every exceptional direction. More generally, up to the invertible row operation `[[1,0],[b,1]]`, the condition is
\[
U=0 \iff 
\begin{pmatrix}\xi&\eta\\ r&s\end{pmatrix}C=0.
\]
So the exceptional divisor contains a nontrivial residual zero locus.

**Mechanism**

**FACT:** The candidate center `{δ=u=v=0}` is smooth and codim 3 in this chart. The failure is not the codimension count or smoothness of that center; the failure is that the pullback is `ρ^2` times a residual product-type sum of squares, not `ρ^2` times a unit.

**FACT:** Normal directions with  
\[
\begin{pmatrix}\xi&\eta\\ r&s\end{pmatrix}C=0
\]
see order strictly higher than 2. At `C=0`, the quadratic normal form is identically zero.

**INFERENCE:** The correct full-resolution picture is recursive: after this blow-up one must still resolve the residual `U`, which is essentially another matrix-product zero problem involving `[[ξ,η],[r,s]]` and `C`. This is exactly the kind of situation Aoyagi’s accumulated bookkeeping is designed for.

**FACT:** A generic open part of the divisor still gives the right binding ratio. For instance, at `ξ=η=0`, if `(r,s)C != 0`, then `U=(rp+sm)^2+(rq+sn)^2` is nonzero, so `U` is a unit locally.

**Bottom line**

**FACT:** The value `Mval(t)/2` is robust.

**FACT:** The statement “one codim-`Mval(t)` blow-up gives `F=u^2*unit`” is false as a global geometric/log-resolution claim for `L>=3`.

**INFERENCE:** The safe formulation is: one may see the binding ratio on a generic open piece, but the full geometry requires Aoyagi-style recursive blow-ups; collapsing that recursion into one terminal smooth blow-up misrepresents the geometry.