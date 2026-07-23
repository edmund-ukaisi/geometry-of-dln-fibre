Over the intended real polynomial ring, the raw parent residual cannot satisfy the single-\(e_2\) split.

Let
\[
x=u_{010},\quad y=u_{001},\quad z=u_{011}=u_{e_2},
\]
and write
\[
A_1=\begin{pmatrix}b_0&b_1\\d_0&d_1\end{pmatrix}
=\begin{pmatrix}u_{100}&u_{101}\\u_{110}&u_{111}\end{pmatrix}.
\]

The first pivot’s quotient and shear give
\[
A_0^\sharp=
\begin{pmatrix}
1&y\\
x&z-xy
\end{pmatrix},
\qquad
A_1^\sharp=
\begin{pmatrix}
b_0+xb_1&b_1\\
d_0+xd_1&d_1
\end{pmatrix}.
\]
The \(J=1\) shear has empty sums here. Direct multiplication yields
\[
A_1^\sharp A_0^\sharp=
\begin{pmatrix}
b_0+2xb_1&yb_0+zb_1\\
d_0+2xd_1&yd_0+zd_1
\end{pmatrix}. \tag{1}
\]

### Q1 — Fact: the raw split is impossible

The proposed center ideal is
\[
I=(z,b_0,d_0)=(u_{011},u_{100},u_{110}).
\]
If the split existed, every slot would belong to \(I\). For output row \(q\), with
\(c_{q0}=u_{2q0}\) and \(c_{q1}=u_{2q1}\), equation (1) gives
\[
F_{q0}=c_{q0}b_0+c_{q1}d_0
      +2x(c_{q0}b_1+c_{q1}d_1).
\]
Therefore
\[
F_{q0}\bmod I
=2x(c_{q0}b_1+c_{q1}d_1)\ne0.
\]
Thus slots \(0,2\notin I\). Equivalently, the coefficient of \(b_1=u_{101}\) is \(2xc_{q0}\), which is not divisible by \(z=u_{011}\), since it remains nonzero after setting \(z=0\).

Slots \(1,3\) do split:
\[
F_{q1}
=(yc_{q0})b_0+(yc_{q1})d_0
+z(c_{q0}b_1+c_{q1}d_1).
\]

### Q2 — Fact: origin of the \(2\)

For either row of \(A_1\), the first column calculation is
\[
(b_0+xb_1)\cdot1+b_1\cdot x
=b_0+
\underbrace{xb_1}_{\text{branch-(ii) shear}}
+
\underbrace{xb_1}_{\text{surviving }A_{0,10}}.
\]
Hence the two identical contributions add to \(2xb_1\). Branch (ii) transfers \(xA_{1,*1}\) into \(A_{1,*0}\), while the un-zeroed below-pivot entry \(A_{0,10}=x\) independently contributes the same term through ordinary matrix multiplication.

In the second column the branch-(i) term instead cancels:
\[
(b_0+xb_1)y+b_1(z-xy)=yb_0+zb_1.
\]
That is why only output column \(1\) factors through \(z=e_2\).

### Q3 — Fact: the clear that works

Set \(x=u_{010}=0\) at the source, so that the branch-(ii) shear also sees \(x=0\). Then
\[
\widetilde F_{q0}=c_{q0}b_0+c_{q1}d_0,
\]
\[
\widetilde F_{q1}
=(yc_{q0})b_0+(yc_{q1})d_0
+z(c_{q0}b_1+c_{q1}d_1).
\]
This is exactly the requested split, with coefficients independent of \(z,b_0,d_0\). Full input reduction is stronger than necessary; clearing only \(u_{010}\) suffices.

Ordering matters: merely setting the effective \(A_{0,10}\) to zero after the shear leaves
\[
(b_0+xb_1)\cdot1=b_0+xb_1,
\]
which still fails \(z\)-divisibility. The clear must occur before branch (ii), or must also remove its induced \(xA_{1,*1}\) contribution.

### Q4

The split-carrying object is the source-cleared residual \(F\!\mid_{u_{010}=0}\) (or an equivalent coupled normalization clearing both \(A_{0,10}\) and its induced branch-(ii) term), not raw `foldResid(p)` and not an \(A_0\)-only clear applied after the shear.

Whether the full Aoyagi “row-clear” is ordered in exactly this successful way is an inference about that construction; the algebra above proves the necessary condition.