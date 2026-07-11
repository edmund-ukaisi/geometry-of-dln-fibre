## Q1 — front-first exponent

Let
\[
T=s_2^2\|b_2\|^2+s_3^2\|b_3\|^2.
\]
For \(\nu>3/2\),
\[
\int_{\mathbb R^3}(\|x\|^2+T)^{-\nu}\,dx
=\pi^{3/2}\frac{\Gamma(\nu-\frac32)}{\Gamma(\nu)}
T^{\frac32-\nu}.
\]
Replacing \(\mathbb R^3\) by a fixed box changes this to comparability as \(T\to0\). Since \(s_1\asymp1\),
\[
\int_{\rm box}(s_1^2\|b_1\|^2+T)^{-c'}db_1
\asymp T^{-(c'-\frac32)}.
\]

Set
\[
a=c'-\frac32,\qquad \frac32<a<2,\qquad \lambda=\frac{s_3}{s_2}\le1.
\]
Then
\[
g(P)\asymp
s_2^{-2a}
\int_{\rm box^2}
\bigl(\|b_2\|^2+\lambda^2\|b_3\|^2\bigr)^{-a}
\,db_2db_3.
\]
A second Beta scaling gives
\[
\int_{\rm box}
(\|b_2\|^2+z^2)^{-a}db_2\asymp z^{3-2a}.
\]
Because \(3-2a>-3\), the remaining \(b_3\)-integral is finite, and hence
\[
g(P)\asymp s_2^{-2a}\lambda^{3-2a}
=s_2^{-3}s_3^{\,3-2a}.
\]
Thus
\[
\boxed{g(P)\asymp s_2^{-3}s_3^{-(2c'-6)}},
\qquad
\boxed{p=3,\quad q=2c'-6}.
\]

FACT: On the ordered chamber \(s_2\ge s_3\), the two exponents are unequal.

INFERENCE: The bookkeeping is asymmetric in the ordered variables. Globally, exchange symmetry is restored by writing
\[
g(P)\asymp
\max(s_2,s_3)^{-3}\min(s_2,s_3)^{-(2c'-6)}.
\]

Checks:
\[
s_2=s_3=\sigma
\quad\Longrightarrow\quad
g\asymp \sigma^{-3-(2c'-6)}
=\sigma^{-(2c'-3)},
\]
and, with \(s_2=\kappa\) fixed,
\[
g\asymp \kappa^{-3}s_3^{-(2c'-6)}
\asymp s_3^{-(2c'-6)}.
\]

## Q2 — symmetric compound majorant

Write \(\eta=2c'-6\), so \(0<\eta<1\).

### (i) Pointwise domination

The ratio is
\[
\frac{g}{(s_2s_3)^{-b}}
\asymp s_2^{b-3}s_3^{b-\eta}.
\]
The diagonal \(s_2=s_3=t\) forces
\[
t^{2b-(3+\eta)}=O(1),
\]
so necessarily
\[
b\ge\frac{3+\eta}{2}=c'-\frac32.
\]
This is also sufficient: if \(b\ge c'-\frac32\), then \(b-\eta>0\), and using \(s_3\le s_2\le1\),
\[
s_2^{b-3}s_3^{b-\eta}
\le s_2^{2b-3-\eta}
=s_2^{2(b-c'+\frac32)}
\le1.
\]
Therefore
\[
\boxed{g\le C(s_2s_3)^{-b}
\iff b\ge c'-\frac32}.
\]

### (ii) Integrability of the majorant

Using the Q3 density,
\[
d\mu\asymp
s_2^{D_2-D_1-1}s_3^{D_1-1}\ell(s_2)\,ds_3ds_2,
\qquad
\ell(s)=1+\log\frac{\kappa}{s}.
\]
Thus the majorant integral is
\[
M_b\asymp
\int_0^\kappa\int_0^{s_2}
s_2^{2-b}s_3^{-b}\ell(s_2)\,ds_3ds_2.
\]
The inner integral requires \(b<1\). When \(b<1\),
\[
M_b\asymp
\frac1{1-b}\int_0^\kappa
s_2^{3-2b}\ell(s_2)\,ds_2,
\]
whose outer condition is \(b<2\). Hence
\[
\boxed{M_b<\infty\iff b<1}.
\]

FACT: More generally the two conditions are
\[
b<D_1,\qquad 2b<D_2.
\]

### (iii) Comparison

Pointwise domination needs
\[
b\ge c'-\frac32>\frac32,
\]
whereas majorant integrability needs \(b<1\). There is no overlap.

INFERENCE:
\[
\boxed{\text{The symmetric }\sigma_{\min}(\wedge^2P)=s_2s_3
\text{ majorant cannot close this tube.}}
\]
This failure concerns the majorant, not the true asymmetric integral.

## Q3 — pushforward tube and threshold

Codimensions give the incremental powers
\[
s_3:\ D_1,\qquad
s_2:\ D_2-D_1.
\]
The supplied tie at the \(q=2\) stratum contributes one logarithm at the \(s_2\)-scale. Thus, for \(0<t_3\le t_2\le\kappa\),
\[
\boxed{
\mu\{s_2\le t_2,\ s_3\le t_3\}
\asymp
t_2^{D_2-D_1}t_3^{D_1}\ell(t_2)
}
\]
and hence
\[
\boxed{
\mu\{\cdots\}\asymp t_2^3t_3\ell(t_2),\qquad
d\mu\asymp s_2^2\ell(s_2)\,ds_3ds_2.
}
\]

FACT: The codimensions determine the powers. The supplied tied-component information supplies the logarithm; codimensions alone would not determine that multiplicity.

The true integral is
\[
\begin{aligned}
\int_{\rm cell}g\,d\mu
&\asymp
\int_0^\kappa\int_0^{s_2}
s_2^{-3}s_3^{-\eta}
s_2^2\ell(s_2)\,ds_3ds_2\\
&=
\frac1{1-\eta}
\int_0^\kappa s_2^{-\eta}\ell(s_2)\,ds_2,
\qquad \eta=2c'-6.
\end{aligned}
\]
It converges exactly when
\[
\eta<1
\iff 2c'-6<1
\iff
\boxed{c'<\frac72}.
\]
Equivalently,
\[
\boxed{\frac72=\frac{D_2+d_2}{2}
=\frac{4+3}{2}}.
\]

At \(c'=7/2\), the inner integral already contains
\[
\int_0^{s_2}\frac{ds_3}{s_3}=\infty.
\]
The tied-component logarithm does not move the strict threshold; it only strengthens endpoint divergence.

Final verdict: the true corank-2 rung is finite for \(c'<7/2\), but it is not closable through the symmetric \(\wedge^2\)-compound minimum-singular-value weight. It requires the joint two-singular-value pushforward density, equivalently an asymmetry-respecting argument.