All three modules are faithful. One arithmetic caveat: the “divide by 2” interpretation in Module 3 must occur in `ℝ` or `ℚ`, as appropriate for the real exponent `q`, not via natural-number floor division.

## Module 1 — FAITHFUL

Under \(H=\tau V\) with \(\tau>0\),

\[
dH=\tau^N\,dV,\qquad
\|H\|^2+\tau^2=\tau^2(\|V\|^2+1).
\]

Thus the integrand contributes \(\tau^{-2q}\), giving the factor

\[
\tau^N\tau^{-2q}=\tau^{N-2q}.
\]

So the exponent and its direction are correct.

Radially, the unit integral behaves at infinity like

\[
\int^\infty r^{N-1-2q}\,dr,
\]

which converges exactly when \(2q>N\) for \(N\ge1\). The origin causes no singularity. For \(N=0\), the integral is finite for every \(q\), but \(2q>N\) remains a valid sufficient condition. Since necessity is explicitly not claimed, this is faithful.

`chart4_unit_lintegral_lt_top` is only an implication; neither its name nor statement suggests an `iff`.

The hypotheses are satisfiable, for example \(\tau=1\), \(q=N+1\). Finally, allowing arbitrary \(q\) in the scaling theorem is sound: lower-integral change of variables does not require integrability. If the unit integral is `⊤`, the scale factor is nevertheless strictly positive and finite, so the right side remains `⊤`; there is no `0 * ⊤` ambiguity.

## Module 2 — FAITHFUL

The statements exactly express finite-cell integrability plus coverage up to a null set.

No measurability assumptions are missing. Mathlib’s unconditional theorem is precisely

\[
\int_{\bigcup_i C_i}^{-} f\le\sum_i\int_{C_i}^{-}f,
\]

proved through the measure inequality `restrict_iUnion_le`. It applies to arbitrary sets and arbitrary nonnegative functions.

Moreover,

\[
\mu(D\setminus U)=0,\qquad U=\bigcup_i C_i,
\]

implies \(D\subseteq U\) almost everywhere: the exceptional set is exactly \(D\setminus U\). Consequently, the restricted measure on \(D\) is bounded by that on \(U\), giving the first integral inequality.

There is no secret exact-cover requirement. For example, under Lebesgue measure one may take \(D=\{0\}\) and every cell empty: coverage is not literal, but it holds up to null sets.

The hypotheses are plainly satisfiable, and a finite sum of ENNReal values strictly below `⊤` is below `⊤`.

## Module 3 — FAITHFUL

Write \(A=M_0\), \(B=M_1\), \(b=B-u\), and \(d=M_2-b\). Over \(\mathbb Z\),

\[
\begin{aligned}
C_{\ell,s}+ab
&=ub+A\ell +(A-s)(u-\ell-s)+s(M_2-b-\ell)+(A-u)b\\
&=Ab+A\ell+Au-A\ell-As-su+s\ell+s^2+sM_2-sb-s\ell\\
&=AB-As-Bs+s^2+sM_2\\
&=(A-s)(B-s)+sM_2.
\end{aligned}
\]

Both \(\ell\)-terms cancel exactly.

The gate direction is correct. From

\[
\minAdm(M)\le C_{\ell,s}+ab
\]

one obtains, after coercion to an ordered field,

\[
T_1=\frac{\minAdm(M)-ab}{2}\le\frac{C_{\ell,s}}2.
\]

Hence \(q<T_1\) implies \(q<C_{\ell,s}/2\), exactly the condition for

\[
\int_0^\varepsilon r^{C_{\ell,s}-1-2q}\,dr
\]

to converge. Literal natural-number `/ 2` would introduce flooring and should not be called an equivalent reformulation, but the Lean gate itself contains no such mistake.

Using the full minimum makes \(T_1\) no larger than a feasibility-restricted minimum. It therefore permits fewer \(q\)-values and is conservative, not an overclaim.

`clsCodim_gate` is strictly per feasible \((u,\ell,s)\). It asserts no equality of minima, enumeration completeness, coverage, or aggregate claim.

All natural subtractions are protected:

- `hu` controls \(M_0-u\) and \(M_1-u\);
- `hs` and `hu` control \(M_0-s\) and \(M_1-s\);
- `hℓs` controls \(u-\ell-s\);
- `hbℓ` controls both \(M_2-(M_1-u)\) and the subsequent subtraction of \(\ell\).

Thus the integer expansion transfers validly to `ℕ`. The hypotheses are non-vacuous; for example \(M=(2,2,1)\), \(u=1\), \(\ell=0\), \(s=1\) satisfies all of them.

Finally, `minAdm_le_ab_add_uM2` is the candidate \(t=u\) in `minAdm_arity3`. Its `hb` hypothesis is stronger than needed for that inequality, but it is satisfiable and causes neither overclaim nor vacuity.