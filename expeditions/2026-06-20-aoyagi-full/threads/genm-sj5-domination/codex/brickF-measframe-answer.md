## 1. PART (i) VERDICT

[FACT] [STANDARD] Yes: Weyl’s inequality \(\max_i|\lambda_i(A)-\lambda_i(B)|\leq\|A-B\|_{\mathrm{op}}\) makes the sorted-eigenvalue map continuous, hence its composition with \(A:X\to\operatorname{Sym}_N(\mathbb R)\) is Borel.

## 2. PART (ii) VERDICT

[FACT] **LABOUR.** There is an explicit Borel diagonalizer. No measurable-selection theorem is required; standard Borelness of \(X\) is not even needed.

## 3. THE DEGENERATE-BLOCK ARGUMENT

[FACT] Let \(\alpha=(m_1,\ldots,m_r)\) be a composition of \(N\), and put \(s_a=m_1+\cdots+m_a\). Define the multiplicity stratum
\[
S_\alpha=
\left\{
A:
\begin{array}{l}
\lambda_{s_{a-1}+1}=\cdots=\lambda_{s_a}\quad(1\leq a\leq r),\\
\lambda_{s_a}>\lambda_{s_a+1}\quad(a<r)
\end{array}
\right\}.
\]
There are finitely many such strata. They are Borel because they are defined by equalities and strict inequalities between continuous eigenvalue functions. They are also semialgebraic by Tarski–Seidenberg, although that is unnecessary for measurability.

On \(S_\alpha\), write
\[
\mu_a=\lambda_{s_{a-1}+1}.
\]
The orthogonal projection onto the \(\mu_a\)-eigenspace is
\[
P_a(A)=
\prod_{b\ne a}
\frac{A-\mu_b(A)I}{\mu_a(A)-\mu_b(A)}.
\]
The denominators are nonzero on \(S_\alpha\). By the finite-dimensional spectral theorem, \(P_a\) is symmetric, idempotent, and has rank \(m_a\). Its entries are continuous on \(S_\alpha\).

Now resolve the \(O(m_a)\)-ambiguity deterministically. For each ordered subset
\[
I=(i_1<\cdots<i_{m_a})\subseteq\{1,\ldots,N\},
\]
put
\[
V_I(P_a)=\big[P_ae_{i_1}\ \cdots\ P_ae_{i_{m_a}}\big],
\qquad
d_I(P_a)=\det(V_I^{\mathsf T}V_I).
\]
Because the columns of \(P_a\) span its \(m_a\)-dimensional range, some \(I\) has \(d_I>0\). Choose the lexicographically first such \(I\). This is a finite case-split:
\[
C_I=\{d_I>0\}\cap\bigcap_{J<I}\{d_J=0\},
\]
so every \(C_I\) is Borel.

On \(C_I\), apply ordered Gram–Schmidt:
\[
w_j=v_j-\sum_{\ell<j}q_\ell(q_\ell^{\mathsf T}v_j),
\qquad
q_j=\frac{w_j}{\|w_j\|}.
\]
Every denominator is positive because \(d_I>0\). Gram–Schmidt is continuous on the open locus of linearly independent tuples. It can cease to extend continuously when a residual norm vanishes; here those are precisely pivot-cell boundaries. Switching formulas there may create jumps, but a finite Borel pasting remains Borel.

Concatenating the resulting frames,
\[
U(A)=[Q_1(A)\mid\cdots\mid Q_r(A)],
\]
gives
\[
A=U(A)\operatorname{diag}(\lambda_1(A),\ldots,\lambda_N(A))U(A)^{\mathsf T}.
\]

Thus every ingredient is continuous on each Borel cell, and there are finitely many cells. Multiplicity-pattern jumps are handled by finite Borel pasting. No null set is discarded—no measure was supplied—and no continuum-valued choice occurs.

## 4. THE DIABOLICAL POINT

[FACT] Put
\[
A(x,y)=
\begin{pmatrix}x&y\\y&-x\end{pmatrix},
\qquad r=\sqrt{x^2+y^2}.
\]
For \(r>0\),
\[
P_+=\frac{A+rI}{2r},
\qquad
P_-=\frac{rI-A}{2r}.
\]
The lexicographic column-pivot construction gives \(U=[u_+\mid u_-]\), where
\[
u_+=
\begin{cases}
\dfrac{(r+x,y)^{\mathsf T}}{\sqrt{2r(r+x)}},&r+x>0,\\[6pt]
e_2,&x<0,\ y=0,
\end{cases}
\]
and
\[
u_-=
\begin{cases}
\dfrac{(r-x,-y)^{\mathsf T}}{\sqrt{2r(r-x)}},&r-x>0,\\[6pt]
e_2,&x>0,\ y=0.
\end{cases}
\]
At \((0,0)\), the sole eigenspace is \(\mathbb R^2\), so the construction gives \(U(0,0)=I\).

The exact discontinuity locus of this \(U\) is
\[
\{(x,y):y=0\}.
\]
On the negative \(x\)-axis, \(u_+\) changes sign across the cut; on the positive \(x\)-axis, \(u_-\) does. At the origin the directional limits differ. Away from the \(x\)-axis the formulas are analytic. All branch sets are Borel, hence \(U\) is Borel despite having no continuous extension around the conical intersection.

## 5. WHICH CANDIDATE

1. [FACT] **(c), best.** Use eigenvalue equalities for the strata; discriminants and subresultants are avoidable. The discriminant alone does not encode the full ordered multiplicity pattern.

2. [FACT] **(b), second.** This is the correct projection formula, but “other distinct eigenvalues” must be implemented using the finite stratification from (c).

3. [FACT] **(a), last.** It works mathematically if contours are chosen deterministically from spectral gaps, but introduces parameter-dependent complex contour integration and resolvent bookkeeping. It hides no selection theorem, but is an unnecessary analytic primitive for Lean.

## 6. CHEAPEST KILL

[FACT] The sharp test is the Möbius rank-one projector
\[
P(\theta)=\frac12
\begin{pmatrix}
1+\cos\theta&\sin\theta\\
\sin\theta&1-\cos\theta
\end{pmatrix}.
\]
It has no continuous unit section, but
\[
\frac{P(\theta)e_1}{\|P(\theta)e_1\|}
\]
away from \(\theta=\pi\), patched by \(e_2\) at \(\theta=\pi\), is Borel. Thus the strongest finite-dimensional topological obstruction does not produce a measurable obstruction. Replacing “Borel” by “continuous” would flip the verdict immediately; under the stated finite-dimensional Borel hypotheses, it does not.