1. **VERDICT: TRUE.** No extra hypothesis is needed.

2. **Construction and mechanism.** Choose H2 witnesses \(a,b\), and define
\[
c'_i :=
\begin{cases}
b_i,& i\in S,\\
0,& i\notin S.
\end{cases}
\]

Let \(P_0u\) reset every \(X\)-coordinate to \(0\), and \(P_i u\) reset \(X\) to the \(i\)-th unit vector.

- H1 implies \(F(P_0u)=0\), since every \(S\)-coordinate vanishes.
- H2 and invariance under \(X\) give \(F(P_0u)=a(u)\), hence \(a\equiv0\).
- For \(x\in X\setminus S\), H1 gives \(F(P_xu)=0\), while H2 gives \(F(P_xu)=b_x(u)\). Hence \(b_x\equiv0\).
- Therefore H2 reduces to
  \[
  F(u)=\sum_{i\in S}b_i(u)u_i.
  \]
- For \(i\in S\), H2 already gives that \(b_i\) ignores \(X\), hence ignores \(S\).
- H1 makes \(F\) continuous. Moreover,
  \[
  b_i(u)=F(P_i u)-F(P_0u),
  \]
  so \(b_i\) is continuous because \(P_i,P_0\) are continuous.

The mechanism is **fiberwise uniqueness of an affine function in freely variable \(X\)-coordinates**. It does not require \(F\) to be polynomial: fixing coordinates outside \(X\), one evaluates the affine expression at \(0\) and the coordinate unit vectors.

3. **Counterexample:** not applicable. The extra vanishing needed for the intercept and \(X\setminus S\) slopes is already forced by H1.

4. **ALTERNATIVE.** Re-proving the crux directly is probably less Lean friction if this bridge is used only once. First derive
\[
F(v)=\sum_{i\in S}b_i(v)v_i
\]
as above, without proving continuity. Since \(b_i\) ignores \(X\), and \(\sigma u,\tau u\) agree off \(S\), their \(b_i\)-values agree. Then use the center-map relation
\[
(\sigma u)_i=u_p(\tau u)_i\qquad(i\in S)
\]
and factor \(u_p\) through the finite sum.

H2 alone is insufficient: H1 is still needed to kill \(a\) and the \(X\setminus S\) terms.