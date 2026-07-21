### 1. CONFIRM

**Definite fact.** Complete the witness with \(b=q=1\) and \((\mathrm{coreGen}\circ g)(v)=\mathrm{resid}(v)=v_1\). The shear has determinant \(1\), and

\[
\mathrm{stepMap}(u)=(u_0,u_0u_1+u_2,u_2).
\]

At \(u=(0,0,1)\), the pulled-back left side is \(1\), while every child RHS term contains \(b'(u)=u_0=0\). Hence no \(q'\), continuous or otherwise, exists. Neither determinant \(1\) nor \(\phi(0)=0\) controls the exceptional hyperplane with nonzero spectators.

### 2. REFUTE as a complete fix

**Definite fact.** Your order diagnosis correctly identifies the first obstruction: if the blow-up is outermost and the shear fixes the pivot, then

\[
(\mathrm{blockBlowupMap}\circ\mathrm{blockShear})(u)_i
\]

is divisible by \(u_p\) for every center coordinate.

However, this still does **not** prove the stated child invariant. Even with \(\phi=0\), take \(\mathrm{resid}(v)=v_p\), \(b=q=1\). Then the pulled-back left side is \(u_p\), whereas

\[
b'\,\mathrm{resid}'=u_p\cdot u_p=u_p^2.
\]

Equality would require \(q'=1/u_p\). Thus your vanishing-locus test misses an order-of-vanishing obstruction caused by retaining the pure pullback residual.

### 3. CONFIRM

**Definite fact.** Your witness is injective on \(u_0\ne0\):

\[
u_1=\frac{(\mathrm{stepMap}(u))_1-u_2}{u_0}.
\]

Nevertheless it fails to preserve the center ideal. Injectivity away from the exceptional divisor has no implication for divisibility along that divisor.

### 4. REFUTE: FIX-B is sufficient geometrically, but neither minimal nor sufficient for the stated formula

**Definite fact.** The minimal uniform geometric condition is the pullback-ideal inclusion

\[
\mathrm{stepMap}^{*}\langle v_i:i\in S\rangle\subseteq\langle u_p\rangle.
\]

For shear-after-blow-up this is exactly  
\(\phi_i\circ\mathrm{blockBlowupMap}\in\langle u_p\rangle\) for every \(i\in S\). FIX-B implies this but is stronger than necessary.

To make the invariant honest, one must additionally use the **strict transform**

\[
\mathrm{resid}_j\circ\mathrm{stepMap}=u_p\,\overline{\mathrm{resid}}_j,
\qquad
\mathrm{resid}'_j:=\overline{\mathrm{resid}}_j,
\]

or else omit the extra \(u_p\) from \(b'\). No constraint on \(\phi\) alone repairs the stated “extra \(u_p\) plus pure pullback residual” formulation.