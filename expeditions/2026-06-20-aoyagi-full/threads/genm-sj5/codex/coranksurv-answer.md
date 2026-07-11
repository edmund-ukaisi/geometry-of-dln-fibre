Let
\[
f(A)=\det\bigl((AZ_{\mathrm{deep}})_{\mathrm{id},e_c}\bigr).
\]
Choose \(e_r,e_c\) so that \(\det((Z_{\mathrm{deep}})_{e_r,e_c})\ne0\). For the row-selection matrix \(A_0\), we have
\[
f(A_0)=\det((Z_{\mathrm{deep}})_{e_r,e_c})\ne0.
\]
Thus \(f\) is a nonzero polynomial in the entries of \(A\).

### Q1 — AG-FREE

[DERIVED] The genericity is entirely over the free Euclidean variable
\[
A\in \mathbb R^{b\times m}.
\]
For fixed \(Z_{\mathrm{deep}}\), the exceptional set lies in the zero set of the single nonzero polynomial \(f\). Its Lebesgue-nullity follows from the elementary real-analysis theorem that a nonzero real polynomial has a null zero set, typically proved by induction and Fubini.

There is no varying point of an algebraic variety, no irreducible-component decomposition, and no comparison of generic ranks between components. Although \(f\ne0\) also defines a Zariski-open subset of the ambient affine space, that observation is unnecessary.

### Q2 — AG-FREE

[DERIVED] The implication
\[
b\le \operatorname{rank}(Z_{\mathrm{deep}})
\quad\Longrightarrow\quad
\exists e_r,e_c,\ 
\det((Z_{\mathrm{deep}})_{e_r,e_c})\ne0
\]
is elementary finite-dimensional linear algebra: matrix rank equals the largest size of a nonzero minor. It can be proved using bases, Gaussian elimination, or independence of selected rows followed by selection of independent columns.

The one-hot matrix \(A_0\) then merely selects those rows:
\[
(A_0Z_{\mathrm{deep}})_{i,k}
=(Z_{\mathrm{deep}})_{e_r(i),k}.
\]
No generic-rank or component theorem is hidden here.

### Q3 — AG-FREE

[DERIVED] The inclusion is sound:
\[
\{A:\operatorname{rank}(AZ_{\mathrm{deep}})<b\}
\subseteq
\{A:f(A)=0\}.
\]
Indeed, rank \(<b\) forces every \(b\times b\) minor to vanish, hence in particular the one fixed minor indexed by \(e_c\).

The deficient locus is generally the common zero set of all \(b\)-minors, but equality with the chosen hypersurface is not required. Containment in one null hypersurface is sufficient. Conversely, \(f(A)\ne0\) gives rank \(\ge b\), while the \(b\)-row bound gives rank \(\le b\).

The \(b=0\) case is harmless: rank is automatically \(0\), and the empty determinant is \(1\). A Lean implementation using \(b-1\) should split this case or avoid subtraction.

### Q4 — AG-FREE

[DERIVED] The statement is exactly correct:
\[
\operatorname{rank}(Z_{\mathrm{deep}})\ge b
\quad\Longrightarrow\quad
\operatorname{rank}(AZ_{\mathrm{deep}})=b
\quad\text{for a.e. }A.
\]
The hypothesis is also necessary for this conclusion, since
\[
\operatorname{rank}(AZ_{\mathrm{deep}})
\le \operatorname{rank}(Z_{\mathrm{deep}}).
\]

**AG wall avoided: YES.**

[INFERRED] Residual concerns are purely formalization-level: correctly transporting nullity through the finite-coordinate flattening, handling \(b=0\), and ensuring the chosen minor is fixed from \(Z_{\mathrm{deep}}\) before quantifying over \(A\). A literal audit of incidental transitive Lean imports would require the actual source file, but no algebraic-geometric argument is mathematically required.