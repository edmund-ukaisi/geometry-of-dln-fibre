## Q1 — Step B

Direct answer: B is not merely four calls to banked lemmas. Its radial exponents are standard polar geometry, but the bridge to the exact clean corner formula contains an unbanked chart/CoV and a coercivity obligation.

- **(b1) Schur split and depth reduction: mechanical/banked.** The raw integral reaches the freed Schur form by [`gammaPeelIntegral_schurShearFree_eq`](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFreedPeel.lean:78). The factorization \(Q=\widetilde A_1A_2\) and identification with
  \[
  \|PvA_2\|_F^2+\|(Cv+\Gamma W)A_2\|_F^2
  \]
  are already banked in [`gammaPeelIntegral_sjGoodMap_eq`](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJGoodCoords.lean:95). Exposing \(v\) as an integration variable additionally needs row splitting, Tonelli reordering, and the banked translation atom; that composition is plumbing, not new algebra.

- **(b2) The two radial powers are standard polar CoVs.** A \(2\times2\) real matrix is simply \(\mathbb R^4\) after a measure-preserving flatten. Applying [`lintegral_radial_polar_factor`](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJRadialPolar.lean:49) with \(N=4\) gives \(r^3\,dr\); applying it to \(v\in\mathbb R^3\) gives \(s^2\,ds\). No eigenvalue, singular-value, or bespoke “matrix radial” lemma is needed.

- **But polar coordinates do not produce**
  \[
  \widehat\Gamma=\begin{pmatrix}1&\beta\\ \gamma&\gamma\beta+\delta\end{pmatrix}.
  \]
  Polar gives \(\Gamma=r\omega\), \(\omega\in S^3\). Normalizing an entry of \(\omega\) to \(1\) requires a finite angular pivot cover. Equivalently, the projective blow-up
  \[
  (u,\beta,\gamma,\delta)\mapsto
  u\begin{pmatrix}1&\beta\\ \gamma&\gamma\beta+\delta\end{pmatrix}
  \]
  has Jacobian \(|u|^3\), but this is a separate, presently unbanked CoV. The exponent is standard; the chart is new infrastructure.

- **(b3) Unit-clear algebra is standard, but its measure/norm use is not automatic.** The identity
  \[
  L\widehat\Gamma R=\operatorname{diag}(1,\delta),\qquad \det L=\det R=1,
  \]
  is ordinary Schur elimination and follows from the banked Schur machinery. Absorbing \(R\) into the integrated \(W\)-variable is a determinant-one fiber shear, subject to domain tracking.

  However,
  \[
  \|\widehat\Gamma WA_2\|_F^2
  =\|L^{-1}\operatorname{diag}(1,\delta)R^{-1}WA_2\|_F^2
  \]
  is not equal to
  \[
  \|w_1A_2\|^2+\delta^2\|w_2A_2\|^2
  \]
  merely because \(\det L=1\). A non-orthogonal determinant-one matrix does not preserve Frobenius norm. What is valid is a coercive comparison, uniformly on a quantitatively bounded angular chart. The same issue occurs when removing the \(Cv\) cross-term.

- **(b4) Reading off \(U_0,U_1\) therefore needs a proved comparison**, plus control of the shifted-box domains and outer parameters. It is not presently a definitional rewrite. Also, the current Lean [`cornerSlice334Integral`](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorner334.lean:159) is a \(2\times q\) endpoint; the literal \(3\times4\) \(A_2\)-casting is not stated there.

**FACT:** b1 and the radial Jacobian exponents are banked; the matrix block needs no special polar theory. The exact angular/projective chart, its domain transport, and the coercive unit-clear-to-\(U_0,U_1\) bridge are not banked.

**INFERENCE:** B is standard mathematics, not a research wall, but it contains a genuine new measure/chart construction. It is not pure lemma-assembly.

## Q2 — provenance of \(\det M\ne0\)

Direct answer: it does not follow from the \(A_0\) pivot chart, nor from the currently banked good-chart hypotheses.

After the tail shear, write
\[
\widetilde A_1=\begin{bmatrix}v\\W\end{bmatrix},\qquad
v=u_1\bar v.
\]
The unit-clear replaces \(W\) by \(W'=R^{-1}W\), preserving its row rank. Up to row permutation and determinant-one row operations,
\[
M=\begin{bmatrix}w_1\\w_2\\\bar v\end{bmatrix}.
\]
For \(u_1\ne0\),
\[
\det M\ne0
\quad\Longleftrightarrow\quad
\operatorname{rank}\begin{bmatrix}v\\W\end{bmatrix}=3
\quad\Longleftrightarrow\quad
\det\widetilde A_1\ne0.
\]

Thus full rank of the entire resolved front factor would supply \(\det M\ne0\), because the intervening shears preserve rank. But that is an additional tail/front condition, not a consequence of the pivot minor of \(A_0\).

The banked good-chart theorem assumes only \(P\) left-invertible and \(W,A_2\) right-invertible; see [`sjGoodMap_injective`](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJGoodLoss.lean:76). These allow
\[
W=\begin{bmatrix}e_1\\e_2\end{bmatrix},\qquad \bar v=e_1,
\]
for which all stated good-chart inverses exist but \(\det M=0\).

For fixed rank-two \(W\), the bad directions \(\bar v\in\operatorname{rowspan}W\) form a measure-zero great circle in \(S^2\). That can prove \(\det M\ne0\) almost everywhere, but it does not make the casting bound uniform. The casting Jacobian is
\[
|\delta\,a_{\rm piv}\det M|^4.
\]
A pointwise clean-box bound therefore carries the reciprocal factor
\[
|\delta\,a_{\rm piv}\det M|^{-4},
\]
which is generally nonintegrable near \(\det M=0\). Merely deleting the zero set does not control its neighbourhood.

**FACT:** \(\det M\ne0\) is equivalent to full rank of the stacked resolved front rows. The current pivot/good-chart hypotheses do not imply it.

**INFERENCE:** it must be supplied by a separate full-rank/quantitative sector and complement argument, or avoided by using the joint `sjGoodMap` endpoint rather than the \(A_2\)-casting.

## Q3 — verdict and likely failure

For a fixed quantitatively nondegenerate cell—pivot bounded away from zero, a chosen angular entry bounded away from zero, uniformly coercive triangular factors, and \(|\delta a_{\rm piv}\det M|\) bounded below—B is buildable as roughly seven pieces:

1. good-coordinate equality;
2. row split and \(v\)-translation;
3. matrix flatten and \(\Gamma\)-polar CoV;
4. finite angular/projective cover;
5. unit-clear and fiberwise \(W\)-shear;
6. \(v\)-polar CoV;
7. coercive corner comparison and domain enclosure.

The whole bare pivot chart is not closed by those calls: it still requires degeneration sectors and uniform integration of the outer/angular parameters. This is consistent with the remaining named per-chart gap [`sjJointResolution`](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJResolution.lean:797).

The single most likely B failure is the passage **(b3)→(b4)**: treating determinant-one triangular elimination as though it preserved Frobenius energy and yielded the clean \(U_0,U_1\) exactly. It yields an exact matrix factorization, but only a norm comparison, whose uniform constant must be proved.

**FACT:** the proposed literal bridge is currently absent.

**INFERENCE:** there is no bespoke matrix-radial mathematics missing, but there is a real unbanked chart/coercivity construction.

Final verdict: the literal body \(B+C+\) clean coordinates is buildable-as-labour only after adding quantitative sector/complement control. As currently stated, it is not a mechanical completion of the banked lemmas. And \(\det M\ne0\) is a separate obligation—not free from the \(A_0\) pivot chart or the existing \(P/W/A_2\) good-chart assumptions.