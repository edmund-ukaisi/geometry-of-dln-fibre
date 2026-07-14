### Q1

**YES.** [DERIVED-HERE] After fixed row/coordinate permutations, take a sector where the first row dominates and write  
\[
n=(1,p,q),\quad f_1=(-p,1,0),\quad f_2=(-q,-pq,1+p^2),\quad D=1+p^2+q^2,
\]
\[
r=an,\qquad s=\ell n+w(f_1+t f_2),\qquad g=x+(\ell/a)y,
\]
where \(A_0=(x\ y)\), \(|p|,|q|,|t|\le1\); the sibling residual chart swaps \(f_1,f_2\).
The full rational map has
\[
|\det D\Phi|=|a|^2|w|(1+p^2)D,
\quad
L=Da^2\|g\|^2+(1+p^2)(1+Dt^2)w^2\|y\|^2.
\]
Hence \(L\ge a^2\|g\|^2+w^2\|y\|^2\). Row dominance gives \(|\ell/a|\le1\), so \(g\) remains in a fixed enlarged box.
Finite row, coordinate, residual-pivot, and sign sectors cover everything up to null sets.
Thus qPeel receives \((h_a,h_w)=(2,1)\), \((m_a,m_w)=(2,2)\), giving
\[
\tfrac12[(2+1)+(1+1)]=\tfrac52,\qquad 2\le2,\quad1\le2.
\]

### Q2

**YES — removable.** [DERIVED-HERE] For \(G=\begin{psmallmatrix}\alpha&\beta\\ \beta&\delta\end{psmallmatrix}\),
\[
x'=x+\frac{\beta}{\alpha}y
\quad\Longrightarrow\quad
L=\alpha\|x'\|^2+\left(\delta-\frac{\beta^2}{\alpha}\right)\|y\|^2.
\]
This is rational \(LDL^{\mathsf T}\) congruence, not spectral diagonalization.
On the sector \(\alpha\ge\delta\), Cauchy–Schwarz gives \(|\beta/\alpha|\le1\), controlling the transformed box.
The projective residual chart in Q1 resolves the remaining quadratic coefficient without eigenvectors.
[DERIVED-HERE] Facts 1–3 are correct, but Fact 3 rejects only the stated LU comparator—not this orthogonal-residual comparator.
No SVD, eigenvalue density, Haar measure, or variable orthogonal CoV is forced.

### Q3

**NO — not as stated.** [DERIVED-HERE] For entrywise boxes the exact identity is
\[
I(c)=\iint\langle M,G\rangle^{-c}\,d\nu_0(M)\,d\nu_1(G),
\]
where \(\nu_i\) are Gram-map pushforwards, not constant multiples of cone Lebesgue measure.
The unrestricted cone integral also needs a cutoff to avoid divergence at infinity.
[RECALLED] For orthogonally invariant balls/Gaussians, Wishart gives density
\(\det(G)^{(z-s-1)/2}\); here the exponent is zero, but the three-dimensional fibre remains.
Thus a Gram-only reduction from the box requires a pushforward/fibre computation.
[INFERENCE] The resulting cone singularity admits elementary Cholesky/projective resolution, but Q1 more cheaply bypasses the pushforward entirely.

### Q4

**MODERATE.** [INFERENCE] The finite rational chart above uses only the banked general Jacobian CoV, fixed permutations, product-box enlargement, and qPeel.
The decisive point is its Jacobian charge \(|a|^2|w|\), which exactly matches two three-dimensional deep blocks.
The cheapest overturning test is the one-sector certificate:
\[
\det D\Phi=a^2w(1+p^2)D,\quad n\perp f_i,\quad |\ell/a|\le1.
\]
[DERIVED-HERE] Exact symbolic differentiation verifies the determinant and orthogonality; these identities are suitable for `ring`/`norm_num`-style Lean proofs.

### Q5

**YES.** The \((3,2,3)\) arithmetic is unusually exact.
[DERIVED-HERE] For \(s=2\) and general \(z\), the same flag gives
\[
(h_1,h_2)=(z-1,z-2),\qquad (m_1,m_2)=(x-1,x-1).
\]
For \(s\le z\), a full row flag similarly suggests \(h_i=z-i\).
Nonzero Wishart determinant powers merely repackage these monomial Jacobian weights; they do not themselves force spectral density.
For \(s\ge3\), however, \(\sum_i(h_i+1)\) need not equal \(\minAdm(x,s,z)\), and gates \(z-i\le x-1\) may fail.
Multiple residual directions therefore require a new binding-rank/sector analysis; the present MODERATE verdict does not automatically generalize.

**SINGLE CRUX:** The LU cross term is chart-specific, not invariant.  
A dominant-row rational Gram–Schmidt chart yields \(|a|^2|w|\) and the exact qPeel data \((h,m)=((2,1),(2,2))\).  
Therefore route C closes at \(c<5/2\) without any SVD/Wishart/Stiefel density.