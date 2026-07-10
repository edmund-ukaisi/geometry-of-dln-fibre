I get the stated threshold `lambda = 7/2` on the `t=(1,0,0)` branch. Two adjudications:

- `t=(1,0,0)` is a minimizer, not the unique minimizer. For example `t=(2,0,0)` and `t=(2,1,0)` also sum to `7`.
- The native local model is not `F ~ (u0 u1)^2` with independent divisors. It is `F ~ u0^2 U0 + u1^2 U1`; after blowing up the corner, the Jacobian powers add while the loss order stays `2`.

This matches the general DLN statement that the squared Frobenius product has RLCT equal to half the relevant codimension/minimum, and uses the real-RLCT integrability convention. ([arxiv.org](https://arxiv.org/abs/2411.19920?utm_source=openai))

**1. Exact Schur Peel**

Write

\[
A_0=\begin{pmatrix}a&B\\ C&D\end{pmatrix},
\qquad
Q=A_1A_2=\begin{pmatrix}Q_p\\ Q_b\end{pmatrix},
\]

with `a` a unit on this pivot chart, `B` `1x2`, `C` `2x1`, `D` `2x2`, `Q_p` `1x4`, `Q_b` `2x4`. Define

\[
\widetilde Q_p=Q_p+a^{-1}BQ_b,
\qquad
\Gamma=D-Ca^{-1}B.
\]

Then exactly

\[
A_0Q=
\begin{pmatrix}
a\widetilde Q_p\\
C\widetilde Q_p+\Gamma Q_b
\end{pmatrix},
\]

so

\[
\|A_0Q\|_F^2
=
|a|^2\|\widetilde Q_p\|_F^2
+
\|C\widetilde Q_p+\Gamma Q_b\|_F^2.
\]

The only appearances of `a^{-1}` are in the row shear `Q_p -> Q_p+a^{-1}BQ_b` and the Schur complement `Γ=D-Ca^{-1}B`.

**2. No Determinant-Inverse In The Jacobian**

Use the coordinate changes

\[
D\mapsto \Gamma=D-Ca^{-1}B
\]

and

\[
A_1\mapsto A_1^\sharp
=
\begin{pmatrix}1&a^{-1}B\\0&I_2\end{pmatrix}A_1.
\]

The first is an affine shear in the four `D` variables, hence Jacobian `1`. The second left-multiplies the three columns of `A1` by a unipotent `3x3` matrix of determinant `1`, hence Jacobian `1^3=1`. Since `a,B,C` are kept as coordinates, the full Jacobian matrix is block triangular, so no hidden determinant factor appears.

With `A_1^\sharp=\binom{v}{W}`, one has

\[
A_0A_1A_2
=
\begin{pmatrix}1&0\\ C/a&I_2\end{pmatrix}
\begin{pmatrix}a v\\ \Gamma W\end{pmatrix}A_2.
\]

The left matrix is invertible with determinant `1`. For RLCT/integrability it may be removed as a bounded invertible linear recombination of the generators. Thus the clean local model is

\[
G \sim \|vA_2\|_F^2+\|\Gamma WA_2\|_F^2.
\]

There is no unavoidable determinant-inverse. A determinant inverse only appears if one unnecessarily normalizes by a non-unit pivot or uses an inverse frame as a coordinate map. On the pivot chart, all such pivots are units; using unipotent shears avoids exceptional determinant factors natively.

**3. Boundary 0, Then Boundary 1**

Blow up the `2x2` corank block:

\[
\Gamma
=
u_0
\begin{pmatrix}
1&\beta\\
\gamma&\gamma\beta+\delta
\end{pmatrix}.
\]

This chart has

\[
d\Gamma = |u_0|^{4-1}\,du_0\,d\beta\,d\gamma\,d\delta
=|u_0|^3(\cdots).
\]

Unit-triangular reduction gives

\[
\begin{pmatrix}1&0\\-\gamma&1\end{pmatrix}
\begin{pmatrix}
1&\beta\\
\gamma&\gamma\beta+\delta
\end{pmatrix}
\begin{pmatrix}1&-\beta\\0&1\end{pmatrix}
=
\begin{pmatrix}1&0\\0&\delta\end{pmatrix},
\]

and both triangular matrices have determinant `1`. Absorbing the right one into `W` is again determinant `1` on `W`. Thus

\[
G\sim
\|vA_2\|^2
+
u_0^2\left(\|w_1A_2\|^2+\delta^2\|w_2A_2\|^2\right).
\]

Boundary 0 charge: `4`; Jacobian power: `3`; loss order in the residual summand: `2`.

Now blow up the boundary-1 row `v in R^3`:

\[
v=u_1\bar v,
\qquad
dv=|u_1|^{3-1}du_1\,d\bar v
=|u_1|^2(\cdots).
\]

Then

\[
G\sim
u_1^2\|\bar vA_2\|^2
+
u_0^2\left(\|w_1A_2\|^2+\delta^2\|w_2A_2\|^2\right).
\]

Boundary 1 charge: `3`; Jacobian power: `2`; loss order: `2`.

Boundary 2 has `t=0`, hence charge `(0-0)(4-0)=0`. On the generic downstream chart, `A2` supplies units/nondegenerate row coefficients and introduces no exceptional divisor. Degenerate `A2` charts are other rank-profile strata; they do not lower this branch’s value.

**4. The Crux: Sum, Not Min**

Near the binding corner, after choosing a generic downstream frame, the active model is

\[
G \sim u_0^2U_0+u_1^2U_1,
\qquad U_0,U_1>0\text{ analytic units},
\]

with measure factor

\[
|u_0|^3|u_1|^2\,du_0du_1.
\]

Looking at `u0=0` or `u1=0` separately gives the misleading `4/2` and `3/2`. The binding zero lies at the corner `u0=u1=0`. Blow up that corner, say

\[
u_1=u_0\tau.
\]

Then

\[
|u_0|^3|u_1|^2\,du_0du_1
=
|u_0|^3|u_0\tau|^2|u_0|\,du_0d\tau
=
|u_0|^6|\tau|^2\,du_0d\tau,
\]

while

\[
G=u_0^2(U_0+\tau^2U_1).
\]

So the terminal divisor has Jacobian power `6`, loss order `2`, and threshold

\[
\frac{6+1}{2}=\frac72.
\]

This is exactly the accumulated charge

\[
4+3+0=7.
\]

In “diag(b)” language, the final exceptional coordinate divides both old boundary coordinates: in this chart `u0=e`, `u1=eτ`. Thus the row multipliers are like `b_corank=e` and `b_pivot=eτ`, not a false single term `(u0u1)^2`. The shared downstream `A2` keeps these summands in one product ideal, so the zero condition is simultaneous at the same corner; the codimensions add on the terminal exceptional divisor.

**5. General Pattern**

For widths `M=(M0,...,ML)` and rank profile `t`, the generic charge pieces are

\[
q_0=(M_0-t_0)(M_1-t_0),
\]

\[
q_j=(t_{j-1}-t_j)(M_{j+1}-t_j)\quad (j\ge 1),
\]

with terminal zero-rank convention as appropriate. Each positive `q_j` comes from a radial blow-up of a block of that many variables, giving Jacobian power `q_j-1` and loss order `2`.

The M-generic facts are: Schur complements use pivot inverses only as unit coefficients; unipotent shears have determinant `1`; successive active radial variables are resolved by blowing up their common corner, producing terminal Jacobian power

\[
\sum_j q_j-1
\]

and loss order `2`, hence branch threshold

\[
\frac12\sum_j q_j.
\]

Specific to `(3,3,3,4)` is the literal `2x2` Schur residual at boundary 0 and the `1x3` row blow-up at boundary 1. The exponent mechanism itself is generic.