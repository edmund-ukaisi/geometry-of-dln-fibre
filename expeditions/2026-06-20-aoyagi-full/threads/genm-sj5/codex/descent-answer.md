### Q1

**Derived: yes, as threshold accounting.**

\[
\frac12\minAdm(3,3,3,4)
=\frac12\cdot4+\frac12\cdot3
=2+\frac32=\frac72.
\]

Thus the shifted exponent is \(s=c'-2<3/2\). The \(3/2\) is the reduced-chain \((1,3,4)\) contribution. It is a charge decomposition, not yet a factorisation of the integral.

The front-only threshold \(\approx3\) fails to recover the full reduced-tail contribution; numerically it loses \(1/2\) overall, rather than literally omitting all \(3/2\).

### Q2

**Architecture inference: choose Route A, but only as a decorated/rank-flag recursion. The advertised plain-IH version of A is invalid. Route B duplicates that resolution.**

The unit-Jacobian normal-slice CoV straightens the **rank locus**, not the coupled loss. After the threaded shear, the exact loss has the form

\[
\|\widetilde R\alpha\|^2+\|\widetilde RB+\widetilde SZ\|^2,
\]

not \(\|R\|^2+\|Z\|^2\). Cleaning the first term via \(R=\widetilde R\alpha\) introduces the unbounded Jacobian \(|\det\alpha|^{-m}\).

Equivalently, in the freed-\(\Gamma\) coordinates,

\[
w=\|P\widetilde vA_2\|^2,\qquad Q_b=YA_2;
\]

both terms still share \(A_2\). A unit-Jacobian shear cannot turn them into independent reduced-chain variables.

Therefore:

- the CoV does **not** make the residual a genuine undecorated reduced-chain box integral;
- the coupling must be carried through a simultaneous rank-flag/monomial descent;
- a faithful Route B would have to reconstruct essentially the same full flag resolution, so it is less economical.

### Q3

**Derived: the plain `hIH(redChain)` is insufficient as a black box. Strictness does not resolve zero slack.**

Suppose the post-peel integral contains

\[
H\,F_{\rm red}^{-s},\qquad s=c'-2<\lambda:=3/2,
\]

with unbounded coupled decoration \(H\). Hölder would require exponents \(r,r'\) satisfying

\[
rs<\lambda,\qquad H\in L^{r'}.
\]

Necessarily,

\[
r'>\frac{\lambda}{\lambda-s}.
\]

As \(c'\uparrow7/2\), hence \(s\uparrow\lambda\), the required moment \(r'\to\infty\). The Gram/pivot decorations have only a finite moment range. Thus the strict inequality gives pointwise slack for each \(c'\), but not the arbitrarily high weight-integrability needed near the endpoint.

The decoration must record:

- exceptional/radial divisors;
- their Jacobian exponents;
- the vanishing order of each loss generator along each divisor;
- which generators share a divisor;
- the current rank/pivot chart and bounded unit coefficients.

At a terminal chart the ledger gives an explicit monomial integral, and the accumulated charges add to \(7\). A plain outer IH may still be invoked **after** this decoration has been completely discharged. If recursion enters a shorter chain while the weight remains, the recursive hypothesis itself must be Gram/monomial-decorated.

**Status inference:** bounded, not a mathematical wall, because the flag is finite and the terminal monomial estimates exist. But it is a substantial unbuilt resolution—not plumbing. The plain-IH single-peel architecture is genuinely blocked.

### Q4

The proposed structure is essentially right, with three important corrections.

1. **Pivot energy \(w>0\).**  
   The zero locus may be null, but a.e. positivity proves only that the inner \(\Gamma\)-integral is finite a.e. It does not prove its outer integral is finite: the fibre bound may blow up as \(w\to0\). Resolve and integrate the neighborhoods of \(\{w=0\}\) jointly in \((A',x,\Gamma)\).

2. **\(Q_bQ_b^\top\) positive definite.**  
   Use a finite minor/rank-flag cover. On full-row-rank cells bounded away from the rank boundary, the conditional atom applies. On rank \(r<b\), PosDef must not be asserted: integrate only the \(ar\) active \(\Gamma\)-directions, keep the kernel directions inside their bounded box, and recurse along the rank flag. In bottleneck widths this rank-deficient branch is generic, not negligible.

3. **\(c'>ab/2\).**  
   This cannot be supplied by integrating \(A'\); it is an exponent condition. Branch explicitly:

   - if \(c'>ab/2\), use the full-rank Morse atom where applicable;
   - if \(c'\le ab/2\), use the bounded-\(\Gamma\) estimate
     \[
     \int_{\Gamma\text{-box}}(w+E)^{-c'}\le |\Gamma\text{-box}|\,w^{-c'},
     \]
     then resolve the resulting outer \(w^{-c'}\) singularity jointly;
   - on rank \(r\), the active threshold is \(ar/2\), not \(ab/2\);
   - equality is logarithmic for the whole-space atom and must remain in the bounded/corner branch.

So the correct measure-level architecture is: rank-stratified neighborhood cover, active-rank atoms on good cells, bounded-box branches elsewhere, and joint monomial resolution of \(w\), rank degeneration, and pivot degeneration.