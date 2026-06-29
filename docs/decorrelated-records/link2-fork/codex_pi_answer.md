1. For `L : R ⊕ C ⊕ S → R`,
\[
\operatorname{regStraightenTotalCLM2}(L)(\delta r,\delta c,\delta s)
=
(L_R\delta r+L_C\delta c+L_S\delta s,\delta c,\delta s).
\]
Its block matrix is
\[
\begin{pmatrix}
L_R & L_C & L_S\\
0 & I_C & 0\\
0 & 0 & I_S
\end{pmatrix}.
\]
So it is invertible iff the **reg-block** `L_R : R → R` is invertible. The `core` and `spec` blocks are top-row off-diagonal entries, hence do not affect the determinant. Explicit inverse:
\[
(y_R,y_C,y_S)\mapsto
(L_R^{-1}(y_R-L_Cy_C-L_Sy_S),y_C,y_S).
\]

2. Let
\[
T:=D(A^{-1})(0),\qquad
T(\delta r,\delta c,\delta s)
=
(\delta r,\delta c-Dg(0)(\delta r,\delta s),\delta s).
\]
Then
\[
D_{E_{\mathrm{full}}}=D_E\circ T.
\]
On the reg block:
\[
D_{E_{\mathrm{full}}}(\delta r,0,0)
=
D_E(\delta r,-Dg(0)(\delta r,0),0).
\]
Using the atom,
\[
D_E(0,\delta c,0)=0,
\]
the core contribution vanishes, so
\[
D_{E_{\mathrm{full}}}(\delta r,0,0)
=
D_E(\delta r,0,0).
\]
Since the reg-block of `D_E` is `I_R`,
\[
(D_{E_{\mathrm{full}}})_R = I_R.
\]
So the core-shear’s reg-to-core mixing does **not** corrupt the reg block; the atom kills it.

3. Therefore
\[
\operatorname{regStraightenTotalCLM2}(D_{E_{\mathrm{full}}})
\]
is invertible because its reg block is `I_R`. Also `D(A^{-1})(0)` is unipotent/block triangular with identity diagonal, hence invertible when `Dg(0)` exists. Thus
\[
D\widetilde\pi(0)
=
\operatorname{regStraightenTotalCLM2}(D_{E_{\mathrm{full}}})\circ D(A^{-1})(0)
\]
is an invertible linear isomorphism.

The exact reduction is:

- `Dg(0)` exists so that `D(A^{-1})(0)` is the stated linear map;
- the atom holds: `D_E|_C = 0`;
- the reg-block `D_E|_R : R → R` is invertible, and in your setup it is `I_R`.

4. Strict-derivative invertibility is only a **linearized** statement. It does not by itself make `π̃` a genuine `C^∞` local diffeomorphism.

For `π̃` to be a `C^∞` local diffeomorphism by the usual inverse-function theorem / right-equivalence argument, the nonlinear map itself must be `C^∞` near `0`. Since
\[
\widetilde\pi(q)=(E(A^{-1}q),(A^{-1}q).2),
\]
this requires `A^{-1}` to be `C^∞` near `0`, hence requires `g` to be `C^∞` near `0` in the relevant variables. Mere strict differentiability of `g` at `0`, even with invertible strict derivative of `π̃`, gives an invertible tangent map but not a `ContDiff` local diffeomorphism.

So: **yes, the strict derivative is an iso under the block conditions above; no, that alone is not enough for the rlct right-equivalence diffeomorphism step unless the nonlinear shear is sufficiently smooth.**