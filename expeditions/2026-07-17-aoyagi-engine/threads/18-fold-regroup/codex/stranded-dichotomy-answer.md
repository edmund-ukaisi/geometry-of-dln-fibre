The headline Jacobian identity is false in general. The correct result uses the full ledger; the analytic filtering is valid only when extracting the RLCT.

### Q1. False

For the witness \(E_A=6,\widetilde t_A=0\) and \(E_B=2,\widetilde t_B=1\),

\[
|\det D\pi|
=|z_A|^{6-1}|z_B|^{2-1}
=|z_A|^5|z_B|.
\]

The analytic-filtered expression is only \(|z_A|^5\). These differ, for example, whenever \(z_A\neq0\) and \(0<|z_B|<1\). Thus this is not even an almost-everywhere identity.

### Q2. Honest Jacobian identity

Let

\[
D=A\sqcup S,\qquad
A=\{k:\widetilde t_k=0\},\qquad
S=\{k:\widetilde t_k>0\},
\]

where \(D\) is the full ledger of divisors actually born through blow-ups. Then

\[
\boxed{
|\det D\pi(w)|
=
\prod_{k\in D}|z_k(w)|^{E_k-1}
}
\]

or, equivalently,

\[
\boxed{
|\det D\pi|
=
\underbrace{\prod_{a\in A}|z_a|^{E_a-1}}_{J_{\mathrm{an}}}
\underbrace{\prod_{s\in S}|z_s|^{E_s-1}}_{J_{\mathrm{str}}}.
}
\]

The stranded factor is not a unit when some \(E_s>1\), so it cannot be omitted from an exact identity.

### Q3. RLCT-inertness

Under the stated bounded-residual hypothesis, the stranded factors do not change the smallest pole.

Precisely, suppose on the source box

\[
F\circ\pi(w)
=
U(w)\prod_{a\in A}|z_a(w)|^2,
\qquad 0<c\le U(w)\le C.
\]

Then the local zeta integral has integrand

\[
U(w)^{-\lambda}
\prod_{a\in A}|z_a|^{E_a-1-2\lambda}
\prod_{s\in S}|z_s|^{E_s-1}.
\]

Since \(U^{-\lambda}\) is bounded above and below for fixed real \(\lambda\), integrability reduces to the monomial factors. For each analytic divisor,

\[
\int_0^R z_a^{E_a-1-2\lambda}\,dz_a<\infty
\quad\Longleftrightarrow\quad
\lambda<\frac{E_a}{2}.
\]

For each stranded divisor,

\[
\int_0^R z_s^{E_s-1}\,dz_s
=\frac{R^{E_s}}{E_s}<\infty
\]

because \(E_s\ge1\), with no dependence on \(\lambda\). Hence

\[
\boxed{\operatorname{RLCT}_{\text{leaf}}
=\min_{a\in A}\frac{E_a}{2}}
\]

with value \(+\infty\) if \(A=\varnothing\). In the witness, both the full and filtered integrals have their first pole at \(\lambda=6/2=3\).

The bounded-away-from-zero condition is essential. Merely having divisor order zero is insufficient: for \(F(x,y)=x^2+y^2\), a weight \(|x|^{E-1}\) changes the threshold from \(1\) to \((E+1)/2\), even though \(F|_{x=0}=y^2\) is not identically zero.

### Q4. Correct consumers

The leaf theorem should state:

\[
|\det D\pi|
=
\prod_{k\in D}|z_k|^{E_k-1}
=
J_{\mathrm{an}}J_{\mathrm{str}},
\]

where \(D\) is the full ledger.

Then:

- **Jacobian identity:** reads the full ledger \(D=A\sqcup S\).
- **Loss factorization:** reads only the analytic ledger \(A\):
  \[
  F\circ\pi=U\prod_{a\in A}|z_a|^2.
  \]
- **RLCT pole:** may discard \(S\) only after applying the inertness argument, and reads
  \[
  \min_{a\in A}E_a/2.
  \]

Thus analytic filtering preserves the RLCT read, not the Jacobian identity.