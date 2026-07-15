## 1. STATEMENT SHAPE

Let
\[
K_P=I_b\otimes P,\qquad K_D=D^\top\otimes I_u,\qquad
G=K_PK_P^\top+K_DK_D^\top .
\]

1. **Vectorised front map** — rank #1.
   \[
   \operatorname{vec}(PU+BD)=K_P\operatorname{vec}(U)+K_D\operatorname{vec}(B).
   \]
   Self-contained, true without invertibility. Mathlib v4.29 has exactly `Matrix.vec` and `Matrix.kronecker_mulVec_vec`.

2. **Front-Gram expansion** — rank #2.
   \[
   G=I_b\otimes(PP^\top)+(D^\top D)\otimes I_u.
   \]
   Self-contained, purely algebraic, no invertibility needed.

3. **Front-Gram positivity** — rank #3.
   \[
   \operatorname{PosSemidef}(G).
   \]
   Again no invertibility needed. Under `IsUnit P` or `IsUnit D`, a cheap later strengthening is `PosDef G`.

Use the name `frontGram`, not `frontCovariance`, unless a probabilistic covariance theorem is also present.

## 2. DET ROUTE

Defer the determinant product. The realistic single-thread boundary is the three lemmas above. The commuting-factor lemma
\[
AC=CA=(D^\top D)\otimes(PP^\top)
\]
is inexpensive, but does not remove the spectral bookkeeping.

For a later determinant module, avoid generic simultaneous diagonalisation. Use the tensor structure:

1. Diagonalise \(PP^\top\) and \(D^\top D\) separately using `IsHermitian.eigenvectorUnitary`.
2. Tensor the two unitary changes of basis.
3. Prove the conjugated sum is
   \[
   \operatorname{diagonal}\bigl((j,i)\mapsto \beta_j+\alpha_i\bigr).
   \]
4. Apply `Matrix.det_units_conj` and `Matrix.det_diagonal`.

First state
\[
\det G=\prod_{j,i}(\alpha_i+\beta_j),
\]
where \(\alpha,\beta\) are the Hermitian eigenvalues. Connecting these to Mathlib’s `LinearMap.singularValues` is another layer: that API uses \(T^\ast T\), while the \(P\)-factor here is \(PP^\top\).

The vec bridge is needed to identify \(G\) with the Gram of the actual map, but not to prove the determinant identity itself.

## 3. VACUITY CHECK

The bare Kronecker identity is an honest lemma if named `frontGram_eq_kroneckerSum` or `kronecker_gram_expansion`.

It is insufficiently grounded if named as the covariance of \(L(U,B)=PU+BD\). Since the exact vec API already exists, include the vectorisation lemma; it removes that semantic gap at low cost.

## 4. PITFALLS

- `Matrix.vec X` is indexed by `b × u`: column index first. This matches \(D^\top\otimes I_u\). Avoid converting prematurely to `Fin (b*u)`.
- `kroneckerMap_transpose` is oriented as
  \[
  A^\top\otimes B^\top=(A\otimes B)^\top;
  \]
  rewrites often need the reverse direction. PSD lemmas primarily use conjugate transpose `ᴴ`; over `ℝ`, simplify carefully to transpose.
- `det_kronecker` concerns a product \(A\otimes B\), not the Kronecker sum. Its cardinal exponents are also crossed. It does not directly advance \(\det(A+C)\).