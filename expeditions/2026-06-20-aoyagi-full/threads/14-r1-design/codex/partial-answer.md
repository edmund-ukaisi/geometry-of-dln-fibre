**FACT (derived):** The RLCT at the origin of

\[
G=\|TC^3\|_F^2+\delta^2\|RC^3\|^2
\]

with \(T\in \operatorname{Mat}_{2\times 2}\), \(R\in \operatorname{Mat}_{1\times 2}\), \(C^3\in \operatorname{Mat}_{2\times 2}\), \(\delta\in \mathbb R\), is

\[
\boxed{\operatorname{RLCT}_0(G)=2.}
\]

**FACT (derived):** This equals the predicted value

\[
\frac12 Mval(2,1,0)=\frac12\left((3-2)(3-2)+(2-1)(2-1)+(1-0)(2-0)\right)=2.
\]

**Resolution Argument**

**FACT (derived):** Blow up the \(C^3=0\) locus. Since \(C^3\) has 4 entries, write locally

\[
C^3=\rho \bar C,\qquad \bar C\neq 0.
\]

Then

\[
G=\rho^2\left(\|T\bar C\|^2+\delta^2\|R\bar C\|^2\right),
\]

and the radial variable contributes candidate threshold \(4/2=2\). It remains to check that the residual factor has RLCT at least \(2\) on the exceptional divisor.

**FACT (derived):** If \(\bar C\) has rank \(2\), multiplication by \(\bar C\) is locally invertible on row vectors, so the residual is equivalent to

\[
\|T'\|^2+\delta^2\|R'\|^2.
\]

Its RLCT is \(2+\frac12=\frac52\), hence it does not lower the candidate \(2\).

**FACT (derived):** The only delicate case is \(\operatorname{rank}\bar C=1\). In the chart

\[
\bar C=\begin{pmatrix}1&u\\ v&w\end{pmatrix},\qquad \varepsilon=w-uv,
\]

for a row \((p,q)\),

\[
(p,q)\bar C=(A,Au+B\varepsilon)
\]

after the analytic change \(A=p+qv,\ B=q\). Thus the residual ideal is equivalent to

\[
(A_1,A_2,\varepsilon B_1,\varepsilon B_2,\delta E,\delta\varepsilon F).
\]

So the residual sum of squares is equivalent to

\[
A_1^2+A_2^2+\varepsilon^2(B_1^2+B_2^2)+\delta^2E^2+\delta^2\varepsilon^2F^2.
\]

The two linear generators \(A_1,A_2\) contribute \(1\). The remaining monomial ideal

\[
(\varepsilon B_1,\varepsilon B_2,\delta E,\delta\varepsilon F)
\]

has Newton constraints

\[
v_\varepsilon+v_{B_1}\ge \frac12,\quad
v_\varepsilon+v_{B_2}\ge \frac12,\quad
v_\delta+v_E\ge \frac12,\quad
v_\varepsilon+v_\delta+v_F\ge \frac12.
\]

The minimum of the sum of weights is \(1\), achieved for example by \(v_\varepsilon=v_\delta=\frac12\). Therefore the residual RLCT is

\[
1+1=2.
\]

Combining with the \(\rho^2\) divisor gives

\[
\operatorname{RLCT}_0(G)=\min(2,2)=2.
\]

**FACT (derived):** The sharing of the \(C^3\)-variables matters. For the lower-depth core alone,

\[
\|TC^3\|^2
\]

the same rank-one exceptional chart gives residual ideal

\[
(A_1,A_2,\varepsilon B_1,\varepsilon B_2),
\]

whose RLCT is

\[
1+\frac12=\frac32.
\]

The extra term \(\delta^2\|RC^3\|^2\) contributes the generator \(\delta E\) after the \(C^3\)-blow-up, raising the residual threshold from \(\frac32\) to \(2\). It is not irrelevant.

**INFERENCE:** The partial-rank peel does **not** preserve the clean rank-one recursion pattern “one divisor times a fresh lower-depth core in disjoint variables.” The value survives:

\[
\operatorname{RLCT}_0(G)=2=\frac12Mval(2,1,0),
\]

but the geometry is genuinely coupled through \(C^3\). The partial-rank branch is not just a disjoint divisor plus a fresh \((L-1)\)-core; the \(\delta R C^3\) term changes the residual rank-one chart exactly enough to push the threshold from \(3/2\) to \(2\).