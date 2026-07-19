Verdict: **false with witness for the pure-pivot `chartMap`; true with conditions for the faithfully source-gauged/incidence-normalized composite.** The Case 1(1) Jacobian accumulation does not increase the product’s divisor valuation.

1. **Divisor power**

For \(L=2\), the normalized chart is

\[
C^1=\alpha
\begin{pmatrix}1&a\\ b&ab+\rho\end{pmatrix},
\qquad
C^2=
\begin{pmatrix}\rho\xi-ar&\rho\eta-as\\ r&s\end{pmatrix}.
\]

Direct multiplication gives

\[
C^1C^2=\alpha\rho
\begin{pmatrix}
\xi&\eta\\ b\xi+r&b\eta+s
\end{pmatrix}.
\]

Thus \(\alpha,\rho\) each have exact valuation \(1\) in the product and valuation \(2\) in the loss.

For \(L=3\), write

\[
Y=\begin{pmatrix}1&0\\ b&1\end{pmatrix}
  \begin{pmatrix}\xi&\eta\\r&s\end{pmatrix}.
\]

The first peel gives \(C^1C^2C^3=\alpha\rho\,YC^3\). Apply the same normalized construction to \((Y,C^3)\):

\[
Y=\alpha'
\begin{pmatrix}1&a'\\b'&a'b'+\rho'\end{pmatrix},
\quad
C^3=
\begin{pmatrix}
\rho'\xi'-a'r'&\rho'\eta'-a's'\\r'&s'
\end{pmatrix}.
\]

Then

\[
C^1C^2C^3
=\alpha\rho\alpha'\rho'
\begin{pmatrix}
\xi'&\eta'\\
b'\xi'+r'&b'\eta'+s'
\end{pmatrix}.
\]

Hence all four displayed divisors occur exactly once in the product.

More generally, Aoyagi’s terminal normal form is

\[
Q\,\mathrm{prod}\,P=\operatorname{diag}(b_1,\ldots,b_m),
\qquad
b_1=\prod_{\widetilde t(u)=0}u,\qquad b_1\mid b_i .
\]

After extracting \(b_1\), the first diagonal entry is \(1\). Therefore no terminal \(u\) divides the remaining matrix, so its product valuation is exactly \(1\).

Case 1(1) changes the Jacobian exponent because several coordinates are replaced by \(u\) times ratios. It does not add a second copy of \(u\) to \(b_1\). The reused divisor must be enumerated once by `divCoord`; its accumulated multiplicity belongs in `divExp`.

2. **No terminal-divisor leak after normalization**

The normalized \(L=3\) residual is

\[
R=\xi'^2+\eta'^2+(b'\xi'+r')^2+(b'\eta'+s')^2.
\]

It contains no terminal divisor. On a divisor hyperplane it remains positive whenever the Morse coordinates are nonzero. Its vanishing at
\(\xi'=\eta'=r'=s'=0\) is the intended Morse zero and does not violate the squeeze because `baseForm` also vanishes there.

For a fully diagonal, `resRank = 0` leaf,

\[
R=\left\|Q^{-1}\operatorname{diag}
  \left(1,\frac{b_2}{b_1},\ldots\right)P^{-1}\right\|_F^2,
\]

so \(R>0\). On a uniformly conditioned box it is bounded away from zero.

Pure pivot composition alone has no such guarantee. For example, repeated use of one pivot can give

\[
x=ur,\qquad r=us \quad\Longrightarrow\quad x=u^2s.
\]

Extracting only \(u^2\) from \(x^2\) leaves \(u^2s^2\), which vanishes on \(u=0\). Thus “exactly once” does not follow from `pivotChart` mechanics alone.

3. **Exact residual squeeze**

Let \(|b'|\le B\). The Gram matrix controlling \(R\) is

\[
G(b')=
\begin{pmatrix}1+b'^2&b'\\b'&1\end{pmatrix},
\]

whose eigenvalues are

\[
\lambda_\pm(b')
=\frac{2+b'^2\pm |b'|\sqrt{b'^2+4}}2.
\]

Therefore

\[
\lambda_-(B)\,
(\xi'^2+\eta'^2+r'^2+s'^2)
\le R\le
\lambda_+(B)\,
(\xi'^2+\eta'^2+r'^2+s'^2).
\]

For the usual ratio box \(B=1\),

\[
lo=\frac{3-\sqrt5}{2},\qquad
hi=\frac{3+\sqrt5}{2}.
\]

If a final radial blow-up makes `baseForm = 1`, writing

\[
Z'=\tau\begin{pmatrix}1&q_1\\q_2&q_3\end{pmatrix},
\]

gives \(R\ge\lambda_-(B)>0\); on \(|q_i|\le1\), \(R\le4\lambda_+(B)\).

For general \(Q,P\), the exact necessary condition is uniform conditioning on the source box:

\[
\inf_K\sigma_{\min}(Q^{\pm1})>0,\qquad
\inf_K\sigma_{\min}(P^{\pm1})>0,
\]

with finite corresponding upper bounds. Polynomial unipotent shears satisfy this on bounded boxes. For merely “regular” local normalizations, the box closure must remain inside their unit domain. Nondegeneracy only at the origin is not enough for a whole-box bound.

4. **Pure `chartMap` fails; normalization is load-bearing**

Omitting the incidence shear already fails at \(L=2\). The corresponding pure pivots give

\[
C^1=\alpha\begin{pmatrix}1&a\\b&\rho\end{pmatrix},
\qquad
C^2=\begin{pmatrix}\rho\xi&\rho\eta\\r&s\end{pmatrix},
\]

hence

\[
C^1C^2
=\alpha
\begin{pmatrix}
\rho\xi+ar&\rho\eta+as\\
\rho(b\xi+r)&\rho(b\eta+s)
\end{pmatrix}.
\]

At \(\rho=0\),

\[
F=\alpha^2a^2(r^2+s^2),
\]

which is generally nonzero. For instance
\(\alpha=a=r=\tfrac12\), with all other displayed variables zero, gives \(F=1/64\), whereas the claimed right-hand side containing \(\rho^2\) is zero.

Repeating the pure construction at depth two yields

\[
\mathrm{prod}=\alpha\alpha'K C^3,
\]

where

\[
K=
\begin{pmatrix}
\rho+ab'&\rho a'+a\rho'\\
\rho(b+b')&\rho(ba'+\rho')
\end{pmatrix},
\qquad
C^3=\begin{pmatrix}\rho'\xi'&\rho'\eta'\\r'&s'\end{pmatrix}.
\]

At \(\rho=0\),

\[
F=\alpha^2\alpha'^2a^2\rho'^2
\big((b'\xi'+r')^2+(b'\eta'+s')^2\big),
\]

again generally nonzero. Thus the depth-two pure fold does not acquire the claimed \(\rho^2\) factor.

Even when pure radial pivots force common scalars from both matrices, their residual can retain a determinantal zero:

\[
\begin{pmatrix}1&1\\0&0\end{pmatrix}
\begin{pmatrix}1&0\\-1&0\end{pmatrix}=0.
\]

All ratios lie in \([-1,1]\), so a constant-base lower bound fails on the full pivot box.

Finally, the image-preservation assertion requires transforming the domain:

\[
(\beta\circ g^{-1})(g(D))=\beta(D).
\]

It is not generally true with the old domain \(D\) left unchanged. Thus `chartMap`, `srcBox`, and the final Morse-coordinate assignment must all incorporate the per-edge source gauges coherently.

**Conclusion:** `LeafPullback` is false for the present pure-\(\beta\) fold. It holds for the faithfully gauged composite, with transformed source domains, unique terminal-divisor coordinates, correctly aligned Morse coordinates, and uniformly bounded \(Q,P\) condition numbers.