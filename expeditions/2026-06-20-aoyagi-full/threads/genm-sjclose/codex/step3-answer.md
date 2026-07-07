**Q1.** No, not for the first peel from the banked `corankStep` form with arbitrary fixed downstream `Q`.

Let rows split as `t ⊕ p`, columns as `t ⊕ q`, and `Q : Matrix (t ⊕ q) n ℝ`. Define

\[
\widetilde Q_p := Q_p + A^{-1} B Q_b,\qquad
\Gamma := D - C A^{-1}B,\qquad
X := C\widetilde Q_p,\qquad R := Q_b .
\]

Then the exact residual is

\[
\operatorname{frobSq}\big((u\cdot {\rm fromBlocks}\ A\ B\ C\ D)Q\big)
=
u^2\Big(
\operatorname{frobSq}(A\widetilde Q_p)
+
\operatorname{frobSq}(X+\Gamma R)
\Big).
\]

The second term expands as

\[
\operatorname{frobSq}(X+\Gamma R)
=
\operatorname{frobSq}(X)
+2\,{\rm tr}(\Gamma R X^T)
+{\rm tr}\big(\Gamma(RR^T)\Gamma^T\big).
\]

So `Γ` is isotropic only under special extra conditions such as `RRᵀ = I` and no cross term, which are not available for a general downstream product. Thus there is no exact identity of the form

\[
\operatorname{frobSq}(X+\Gamma Q_b)=\operatorname{frobSq}(\Gamma)+W
\]

with `W` independent of `Γ`.

The pure `frobSq Δ + W` shape is only exact when the downstream factor already has a literal identity channel. If

\[
Q^\sharp =
\begin{bmatrix}
I_r & 0\\
0 & Z
\end{bmatrix},
\qquad
A_0^\sharp = [\,\Delta\ \ E\,],
\]

then

\[
\operatorname{frobSq}(A_0^\sharp Q^\sharp)
=
\operatorname{frobSq}\big([\,\Delta\ \ E Z\,]\big)
=
\operatorname{frobSq}(\Delta)+\operatorname{frobSq}(EZ).
\]

Here `W := frobSq (E·Z)`. This is the actual pure-peel mechanism: a literal block-diagonal identity summand, not Schur elimination of the anisotropic residual.

**Q2.** They are two different endpoints.

For the `(2,2,2)` terminal,

\[
{\rm blockForm}\ q\ u\ (ua_1)\ (ua_2)\ (ua_3)
=
u^2\Big((qa_1+a_3)^2+(q+a_2)^2+a_1^2+1\Big),
\]

and the bracket is a positive unit because it is `≥ 1`.

If one writes the Schur variable as

\[
\Gamma := a_3-a_2a_1,
\]

then the bracket becomes

\[
1+a_1^2+(q+a_2)^2+\big((q+a_2)a_1+\Gamma\big)^2,
\]

still cross-coupled. It is not the pure shape `frobSq Γ + W`.

So the general degenerate-strata recursion terminates on `monomial × unit ≥ 0`, not on a final pure `frobSq Δ + W` peel. Pure peels apply to genuine identity-channel free blocks; the coupled Schur recursion ends by finding a normalized pivot contribution giving a positive unit.

**Q3.** The clean exact STEP-3 identity is a product identity with unit factors absorbed into adjacent factors.

Let

\[
D'_J =
\begin{bmatrix}
1 & \beta\\
\gamma & E
\end{bmatrix}
:
(1\oplus p)\times(1\oplus q),
\]

where `β : 1×q`, `γ : p×1`, `E : p×q`, and define

\[
D_{J+1}:=E-\gamma\beta.
\]

Set

\[
L(\gamma):=
\begin{bmatrix}
1&0\\
\gamma&I_p
\end{bmatrix},
\qquad
R(\beta):=
\begin{bmatrix}
1&\beta\\
0&I_q
\end{bmatrix},
\qquad
B(D_{J+1}):=
\begin{bmatrix}
1&0\\
0&D_{J+1}
\end{bmatrix}.
\]

Then

\[
D'_J
=
L(\gamma)\,B(D_{J+1})\,R(\beta).
\]

Hence for any compatible upstream factor `P` and downstream factor `Z`,

\[
\operatorname{frobSq}\big(PD'_JZ\big)
=
\operatorname{frobSq}\big((P L(\gamma))\,B(D_{J+1})\,(R(\beta)Z)\big).
\]

This is exact because the matrices inside `frobSq` are equal. No Frobenius invariance under `L` or `R` is being used.

“Absorbed” means:

\[
P^+ := P L(\gamma),
\qquad
Z^+ := R(\beta)Z.
\]

The left unit is absorbed into the adjacent upstream factor; the right unit is absorbed into the adjacent downstream factor. If the current block is the leading factor and there is no upstream `P`, then `L(γ)` cannot be deleted. It remains in the norm and produces the cross-coupled residual.

**Q4.** Derived: the banked `corankStep` plus the two pure peels do not close the general recursion by themselves, because the needed exact isotropic `Γ` identity is false in general.

Inference: proving the STEP-3 identity above plus a single-layer or `(2,2,2)` instance is bounded: roughly 10-25 local Lean lemmas if the block APIs and your banked Frobenius split lemmas are available.

Inference: closing full `sjJointResolution` over opaque widths is a genuine multi-week mountain. The hard part is not this matrix identity; it is the recursive carrier bookkeeping, chart transitions, unit absorption at boundaries, exponent accounting, and proving the terminal monomial-unit cases uniformly.

**VERDICT:** the pure peels are right only for literal identity-channel free blocks; the general degenerate recursion needs the monomial×unit endpoint.