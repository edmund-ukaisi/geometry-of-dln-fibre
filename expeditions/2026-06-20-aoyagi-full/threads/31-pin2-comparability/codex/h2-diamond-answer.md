**FACT: (♦) is false as stated.**  
There is an exact small-germ counterexample with positive denominator.

Take `r=M0=M2=1`, `M1=2`, and

\[
A_0=A_1=1,\quad
Y_0=\begin{pmatrix}0&t\end{pmatrix},\quad
Z_1=\begin{pmatrix}t\\0\end{pmatrix},
\]

\[
Y_1=-t^2,\quad Z_0=-t^2,\quad
T_0=\begin{pmatrix}t&-t^3\end{pmatrix},\quad
T_1=\begin{pmatrix}0\\t\end{pmatrix}.
\]

Then all free coordinates tend to `0`, and `P00=1`, so the pivot condition is perfect. The Schur cores are

\[
S_0=T_0-Z_0Y_0=\begin{pmatrix}t&0\end{pmatrix},
\qquad
S_1=T_1-Z_1Y_1=\begin{pmatrix}t^3\\t\end{pmatrix}.
\]

Thus

\[
S_0S_1=t^4,\qquad \mathrm{core}\Phi=t^8.
\]

But the regular blocks cancel exactly:

\[
P_{00}-1=0,\qquad
P_{01}=Y_1+Y_0T_1=-t^2+t^2=0,
\]

\[
P_{10}=Z_0+T_0Z_1=-t^2+t^2=0.
\]

So `Sreg=0`. Meanwhile

\[
K=Z_1Y_0=
\begin{pmatrix}
0&t^2\\
0&0
\end{pmatrix},
\]

and

\[
S_0KS_1=t^4=S_0S_1.
\]

Therefore

\[
R_{\mathrm{core}}=S_0(I-K)S_1=0,
\]

so

\[
\mathrm{Score}=0,\qquad
|\mathrm{Score}-\mathrm{core}\Phi|=t^8.
\]

The denominator is

\[
S_{\mathrm{reg}}+\mathrm{core}\Phi=t^8.
\]

Hence the ratio is identically `1`, not `o(1)`. No function `η(t)→0` can make `(♦)` true on the stated free-coordinate germ.

**Why the trace regrouping cannot close it.**  
The exact regrouping is

\[
\langle S_0S_1,\;S_0Z_1P_{00}^{-1}Y_0S_1\rangle
=
\operatorname{tr}\!\left(
S_1S_1^\top S_0^\top S_0 Z_1P_{00}^{-1}Y_0
\right).
\]

The middle factor `S1 S1ᵀ S0ᵀ S0` sits between `Y0` and `Z1`; it does not reduce to `Y0Z1`. In the counterexample,

\[
Y_0Z_1=0,\qquad P_{00}-I=0,
\]

but

\[
Z_1Y_0\neq 0
\]

is a nilpotent rank-one map that sends the large component of `S1` into the direction seen by `S0`. That is exactly the missing matrix-core effect.

**INFERENCE / repair.**  
A clean one-step estimate exists only for a stronger denominator containing the middle regular pieces

\[
U:=S_0Z_1,\qquad V:=Y_0S_1.
\]

With `τ=max` free-coordinate size and bounded `‖P00^{-1}‖op`,

\[
D=-UP_{00}^{-1}V,
\]

so

\[
|\mathrm{Score}-\mathrm{core}\Phi|
\le
C\tau^2\left(\|S_0S_1\|_F^2+\|S_0Z_1\|_F^2+\|Y_0S_1\|_F^2\right).
\]

This gives the expected `η=O(τ²)`, but it is not controlled by `Sreg+coreΦ`: the example has `Sreg=0` while `S0Z1` and `Y0S1` are both nonzero.

So the honest answer is: no focused Cauchy-Schwarz/trace proof of `(♦)` exists under the stated hypotheses. The statement needs either extra geometric restrictions excluding the tilted-kernel path, or the denominator must be enlarged / the core replaced by the global Schur core. For Lean, formalizing the counterexample is small, maybe 50-100 LoC; proving a repaired middle-energy inequality is also modest. Proving the stated `(♦)` is impossible without changing hypotheses.