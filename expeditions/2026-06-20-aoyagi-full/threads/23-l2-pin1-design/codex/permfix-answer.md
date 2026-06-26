**Verdict.** Fact: An output-coordinate permutation cannot make a singular \(F\) invertible. Fact: A pivot-aligned permutation of the terminal column split can make \(F\) invertible for every rank-\(r\) target, but only if it is used globally in the last interface/frame/target normalization, not merely on the residual outputs.

**(a) Algebra**

Fact: Write \(p=H_0-r\), \(q=H_L-r\). To avoid conflict with the target matrix, write the right frame called \(B\) in the prompt as \(Q\):

\[
Q=\begin{pmatrix}Q_{11}&Q_{12}\\ Q_{21}&Q_{22}\end{pmatrix}.
\]

With ordinary matrix multiplication and \(Y\in \mathbb R^{r\times q}\), the dimensionally consistent formula is

\[
F(X,Y,Z)=
\left(
A_{11}X+A_{12}Z+YQ_{21},\quad
YQ_{22},\quad
A_{21}X+A_{22}Z
\right).
\]

If the Lean convention stores \(Y\) transposed, this appears as left multiplication; the condition is unchanged.

Fact: The linear part comes from

\[
A\begin{pmatrix}X&0\\ Z&0\end{pmatrix}
+
\begin{pmatrix}0&Y\\0&0\end{pmatrix}Q
=
\begin{pmatrix}
A_{11}X+A_{12}Z+YQ_{21} & YQ_{22}\\
A_{21}X+A_{22}Z & 0
\end{pmatrix}.
\]

The omitted first-last interaction is quadratic in \((X,Y,Z)\), so it has strict derivative \(0\).

Fact: Reorder domain as \((X,Z,Y)\) and codomain as \(((11),(21),(12))\). Then

\[
(X,Z)\mapsto A\binom{X}{Z}
\]

is left multiplication by \(A\) on \(r\) columns, and

\[
Y\mapsto YQ_{22}
\]

is right multiplication by \(Q_{22}\) on \(r\) rows. Therefore

\[
\det F=\det(A)^r\det(Q_{22})^r
\]

up to only the harmless basis-order sign; with the matching domain/codomain block swaps above, the signs cancel.

Fact: Since \(A\) is invertible in the setup,

\[
F \text{ is invertible}
\iff
Q_{22}\in \operatorname{GL}_q(\mathbb R).
\]

Equivalently, if \(\rho=\operatorname{rank}(Q_{22})\), then

\[
\operatorname{rank}F=rH_0+r\rho,
\]

so full rank \(rH_0+rq\) occurs exactly when \(\rho=q\).

**(b) Output Permutations**

Fact: If \(P_{\mathrm{out}}\) is a permutation matrix on residual coordinates, the modified map is \(P_{\mathrm{out}}F\), hence

\[
\det(P_{\mathrm{out}}F)=\det(P_{\mathrm{out}})\det(F)=\pm\det(F).
\]

So output permutations preserve rank and invertibility. They cannot turn a bad \(Q_{22}\) into an invertible diagonal block in any meaningful algebraic sense.

**(c) What Must Be Permuted**

Fact: Permuting only residual outputs is inert for invertibility.

Fact: Permuting the terminal column split is non-inert. Let \(V\in \mathbb R^{r\times H_L}\) be the last row factor and choose pivot columns \(J\) with \(V_J\in \operatorname{GL}_r\). Let \(\Pi_J\) move those columns to the first \(r\) positions, so

\[
V\Pi_J=[V_J\;V_K].
\]

If \(Q'\) satisfies

\[
(V\Pi_J)Q'=[I_r\;0],
\]

then the lower-right block \(Q'_{22}\) is invertible.

Fact: This does not depend on choosing a special normal-form frame. The last \(q\) columns of \(Q'\) form a basis of \(\ker(V\Pi_J)\). The block \(Q'_{22}\) is invertible exactly when projection \(\ker(V\Pi_J)\to \mathbb R^q\) is an isomorphism, equivalently when \(\ker(V\Pi_J)\cap \mathbb R^r_{\mathrm{pivot}}=0\), equivalently when \(V_J\) is invertible.

Fact: Frame choice alone, with the old fixed split, cannot fix the problem. For a fixed first-\(r\) split, \(Q_{22}\) is invertible iff the first \(r\) columns of \(V\) are independent. If they are not, every valid right-normal-form frame has singular \(Q_{22}\).

**(d) Propagation And Consistency**

Fact: A terminal column-split permutation must be used everywhere the terminal \(H_L\)-coordinate split appears: the last-layer right normal form, the residual block decomposition, and the target normalization.

Fact: There is no mathematical inconsistency if the same pivot set is used. For target \(T=UV\) with \(U\) full column rank,

\[
\operatorname{rank}(T_J)=\operatorname{rank}(UV_J)=\operatorname{rank}(V_J).
\]

Thus pivot columns of \(T\) are exactly pivot columns of \(V\). With \(Q_L=\Pi_JQ'\),

\[
P_0TQ_L
=
(P_0U)(V\Pi_JQ')
=
\begin{pmatrix}I\\0\end{pmatrix}
\begin{pmatrix}I&0\end{pmatrix}
=
\operatorname{corM}.
\]

Inference: In the formalisation, the genuine fix should package the terminal permutation/pivot choice as shared data. If the target normalization and last-layer frame independently choose pivots, they can refer to different block decompositions.

**(e) Genuine Fix**

Fact: The proposed “output permutation” fix fails.

Fact: The genuine minimal fix is: choose a rank-\(r\) pivot column set \(J\) of the target, use the induced terminal column permutation \(\Pi_J\) to define the \(r\oplus(H_L-r)\) split, and construct/use the last right frame against \(V\Pi_J\). Then every valid right-normal-form frame has invertible \(Q'_{22}\), and

\[
\det F_J=\det(A)^r\det(Q'_{22})^r\ne 0.
\]

Fact: If one is allowed to choose an explicit frame, take

\[
Q'=
\begin{pmatrix}
V_J^{-1} & -V_J^{-1}V_K\\
0 & I_q
\end{pmatrix},
\]

so \((V\Pi_J)Q'=[I_r\;0]\) and \(Q'_{22}=I_q\). But the proof only needs \(Q'_{22}\) invertible, not this special choice.