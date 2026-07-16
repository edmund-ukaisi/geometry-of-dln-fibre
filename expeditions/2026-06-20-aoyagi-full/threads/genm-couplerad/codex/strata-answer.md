The actual loss has a single relevant width \(d=\rho-b\): both degenerating blocks are controlled by \(Q(z)\Pi\). Thus \(A\), not \(B\), is the deep locus—but an intermediate rank stratum can be more restrictive than \(A\).

### 1. Deep loci

Since \(z\mapsto zZ\Pi\) and \(z\mapsto zZ\) have rowwise ranks \(d\) and \(\rho\),

\[
\operatorname{codim}A=ud=u(\rho-b),\qquad
\operatorname{codim}B=u\rho.
\]

Also \(B\subseteq A\), strictly when \(b>0\) generically.

At a generic point of \(A\), a transverse perturbation has \(Q(z)\Pi=\delta R\) with \(\operatorname{rank}R=u\). Then:

- the \([P\mid B]\)-block loses \(u\) coefficient directions, replicated over \(u\) rows: \(u^2\) eigenvalues scale as \(\delta^2\);
- the \(C\)-block loses \(u\) directions in each of its \(a\) rows: \(au\) eigenvalues scale as \(\delta^2\).

Hence

\[
k=u(u+a),\qquad
\mathcal P=2q-\rho_0+k=2q-ub.
\]

Using \(A\),

\[
2q-ub<ud
\quad\Longleftrightarrow\quad
\boxed{2q<u\rho}.
\]

Using \(B\) alone would give \(2q<u(\rho+b)\), which is weaker. Moreover, \(B\) has no additional vanishing eigenvalues: the extra \(ub\) transverse directions only change coefficients already protected by the fixed full-rank \(Q_b\). Thus \(A\) binds between these two loci.

### 2. Intermediate strata

For corank \(\ell\),

\[
k_\ell=\ell(u+a),\qquad
c_\ell=\ell(d-u+\ell),
\]

so the condition is \(2q<\phi(\ell)\), where

\[
\boxed{\phi(\ell)
=\rho_0+\ell^2+(d-2u-a)\ell}.
\]

Put

\[
h:=2u+a-d.
\]

Then \(\phi(\ell)=\rho_0+\ell^2-h\ell\), and the minimizing integer is the integer nearest \(h/2\), clipped to \([1,u]\). Explicitly,

\[
\min_{1\le\ell\le u}\phi(\ell)=
\begin{cases}
u\rho, & d\le a,\\[2mm]
\rho_0-\left\lfloor\dfrac{(2u+a-d)^2}{4}\right\rfloor,
& a+1\le d\le 2u+a-2,\\[3mm]
\rho_0+d-2u-a+1,
& d\ge 2u+a-1.
\end{cases}
\]

For \(u>1\):

- \(d\le a\): \(A\) (\(\ell=u\)) is the unique degeneration binder.
- \(d=a+1\): \(\ell=u\) and \(\ell=u-1\) tie.
- \(d\ge a+2\): an intermediate \(\ell<u\) is strictly tighter than \(A\).
- If \(d\ge2u+a-1\), even the best degeneration condition is no tighter than generic inner integrability.

Thus, including the generic-stratum requirement \(2q<\rho_0\),

\[
\boxed{I<\infty\iff
2q<\min\!\left\{\rho_0,\min_{1\le\ell\le u}\phi(\ell)\right\}}
\]

under the supplied transverse-stratum criterion. Equality is divergent.

### 3. Width caveat

For the stated loss, the premise that the first block is governed by \(\operatorname{rank}(zZ)\) is false. Write

\[
Q=A_zQ_b+Q\Pi,\qquad
A_z=QQ_b^\top(Q_bQ_b^\top)^{-1}.
\]

The invertible change \( \widetilde B=B+PA_z\) gives

\[
PQ+BQ_b=P(Q\Pi)+\widetilde BQ_b.
\]

Since \(Q\Pi\) is row-orthogonal to \(Q_b\),

\[
\|PQ+BQ_b\|_F^2
=\|P(Q\Pi)\|_F^2+\|\widetilde BQ_b\|_F^2.
\]

Therefore both degenerations coincide algebraically on the rank strata of \(Q\Pi\); no two-parameter correction is needed, and the \(\phi(\ell)\) above is the correct one.

Hypothetically, if the first block truly depended on \(\operatorname{rank}Q\), one would need coranks

\[
\alpha=\operatorname{corank}Q,\qquad
\beta=\operatorname{corank}(Q\Pi),
\]

with \(0\le\alpha\le\beta\le u\) and \(\beta-\alpha\le b\). Under generic flag transversality,

\[
c_{\alpha,\beta}
=\beta(d-u+\beta)+\alpha(b-\beta+\alpha),
\]

and the corrected condition would be

\[
2q<
\rho_0-u\alpha-a\beta+c_{\alpha,\beta}.
\]

That two-parameter alternative does not apply to the given \(f\).