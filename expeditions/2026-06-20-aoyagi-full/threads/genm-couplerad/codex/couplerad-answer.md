The proposed conclusion is not valid in the stated generality. The uncharged model has a clean additive codimension, but the determinantal charge can lower it below `FLOOR`; moreover, when the bottleneck is internal, even the uncharged local model need not dominate `FLOOR`.

There are also two literal issues:

- The charge formula must have \(h\le k\), since \(e_1+\cdots+e_h\) is otherwise undefined. I use
  \[
  H_k=\{\max(0,b-s),\ldots,\min(b,k)\}.
  \]
  This repair is already needed for the second requested example at \(k=1\).
- No actual list of blow-up maps or charts was supplied, so completeness of a particular resolution cannot be certified.

## 1. Exact per-stratum codimension

Put
\[
s=\rho-k,\qquad d=p-k+1=\operatorname{exc}+1,\qquad
\beta_i=d+2(k-i).
\]

Normalize the loss valuation to one:
\[
f\ge \tfrac12,\qquad e_i+g_i\ge\tfrac12.
\]
At the minimum,
\[
f=\tfrac12,\qquad g_i=\max(0,\tfrac12-e_i).
\]
Set \(x_i=2e_i\). Then
\[
0\le x_1\le\cdots\le x_k
\]
and the codimension is
\[
C_k=us+\inf_x\left[
\sum_i\bigl(\beta_i x_i+u(1-x_i)_+\bigr)-2\gamma(x/2)
\right].
\]

Using the maximum defining \(\gamma\),
\[
C_k
=
us+\min_{h\in H_k}\inf_x
\left[
\sum_i\bigl((\beta_i-a1_{i\le h})x_i+u(1-x_i)_+\bigr)
+2h(s-b+h)
\right].
\]

Define
\[
B_k(r)=ur+(k-r)\bigl(d+k-r-1\bigr),\qquad 0\le r\le k.
\]

The recession condition is important. The infimum is \(-\infty\) if, for some \(h\in H_k\) and \(r<h\),
\[
(k-r)(d+k-r-1)-a(h-r)<0. \tag{R}
\]

When all these recession coefficients are nonnegative, the ordered polyhedron has minimizing vertices
\[
(x_1,\ldots,x_k)=(\underbrace{0,\ldots,0}_{r},
\underbrace{1,\ldots,1}_{k-r}),
\]
and the exact answer is
\[
\boxed{
C_k
=
u(\rho-k)+
\min_{\substack{h\in H_k\\0\le r\le k}}
\left[
B_k(r)+2h(\rho-k-b+h)-a(h-r)_+
\right].
}
\tag{1}
\]

Thus the charged answer cannot be expressed only in terms of \(u,\rho,k,p\): it genuinely depends on \(a,b\).

Without the charge,
\[
\boxed{
C_k^{(0)}
=
u(\rho-k)+
\sum_{j=0}^{k-1}\min\bigl(u,p-k+1+2j\bigr).
}
\tag{2}
\]

### Additivity proof

For every normalized ray,
\[
\beta_i e_i+ug_i
\ge
\min(\beta_i,u)(e_i+g_i)
\ge \frac12\min(\beta_i,u),
\]
and
\[
usf\ge\frac{us}{2}.
\]
Hence \(2N\ge C_k^{(0)}\). Equality is obtained by taking \(e_i=0\) when \(\beta_i>u\) and \(e_i=\tfrac12\) when \(\beta_i<u\). Since \(\beta_i\) decreases with \(i\), these choices respect the ordering.

So:

- Uncharged codimension: **YES, additive**.
- Full charged codimension: **NO, not generally additive**, because \(\gamma\) couples the first \(h\) singular directions.

### Does it always dominate `FLOOR`?

**No.**

There are two separate counterexamples.

1. Internal bottleneck, even without the charge:

   Take
   \[
   (M_0,M_1,M_2,M_3,M_4)=(4,4,10,3,10),\quad u=3,
   \]
   so \(a=b=1,\rho=3,\operatorname{exc}=0\). At \(k=3\),
   \[
   C_3^{(0)}=\min(3,5)+\min(3,3)+\min(3,1)=7.
   \]
   But the given recursion yields
   \[
   \operatorname{minAdm}(3,10,3,10)=9.
   \]
   Thus the local measure stated in the question is missing enough deep-stratum codimension to reach the floor when \(\rho<\min(M_2,n)\).

2. Charge lowering an endpoint-bottleneck floor:

   Take
   \[
   (M_0,M_1,M_2,M_3)=(6,8,5,5),\quad u=5,
   \]
   so \(a=1,b=3,\rho=5\). Then
   \[
   \mathrm{FLOOR}=\operatorname{minAdm}(5,5,5)=19.
   \]
   At \(k=5\), \(s=0\), and necessarily \(h=3\). Choosing \(r=2\) in (1),
   \[
   B_5(2)=5\cdot2+3^2=19,\qquad
   -a(h-r)=-1,
   \]
   so
   \[
   C_5=18<19.
   \]

Therefore the charge can genuinely lower the minimum below the floor.

Condition (R) can even make the supplied formal ray infimum \(-\infty\). For example \(u=\rho=10,k=2,a=8,b=1,d=1\) gives \(4-8<0\). If this behavior was not intended, the stated \(\gamma\) is missing hidden angular/pivot exponents or a Jacobian contribution.

## 2. What the atoms can prove without SVD

For the uncharged loss, (A) peels the \(us\)-dimensional surviving block and shifts
\[
q\longmapsto c=q-\frac{us}{2}.
\]
The required lost-block codimension is therefore
\[
R_k=\max(0,\mathrm{FLOOR}-us).
\]

Atom (B), applied to the front factor with \(u\) rows, only handles
\[
c<\frac u2,
\]
so by itself it certifies at most \(u\) units of lost codimension.

Let the raw reduced product be
\[
F_{u\times r}\,D_{r\times c},
\qquad
r=M_2-s,\quad c=n-s.
\]
Atom (C) can be used directly, possibly after transposition, exactly when
\[
\boxed{u=r\quad\text{or}\quad r=c.} \tag{3}
\]

Thus the proposed A+B+C route reaches the uncharged floor on stratum \(k\) when

\[
C_k^{(0)}\ge\mathrm{FLOOR}
\]
and either
\[
R_k\le u,
\]
or the square condition (3) holds.

In the endpoint-bottleneck situation:

- If \(M_2\le n\), then \(r=k\). Failure occurs when
  \[
  M_2\ne n\quad\text{and}\quad u\ne k.
  \]
- If \(M_2\ge n\), then \(r=p=k+\operatorname{exc}\). Failure occurs when
  \[
  M_2\ne n\quad\text{and}\quad u\ne p.
  \]

Across all strata, the precise problematic set is
\[
\boxed{
\mathrm{FLOOR}-u(\rho-k)>u,\quad
M_2\ne n,\quad
u\ne M_2-(\rho-k).
}
\]
There the stated atoms do not provide the needed rectangular corank recursion. A new rectangular-first-factor lemma or an SVD-based reduction is needed.

## 3. Is reaching the floor merely a construction problem?

**No, not universally.**

- In the two counterexamples above, the honest exponent is below the floor, so no correct chart construction can repair it.
- In the two requested numerical examples, the exponent equals the floor, so there is no analytic obstruction. Exact RLCT equality is unnecessary: a chartwise lower bound \(C_{\text{chart}}\ge\mathrm{FLOOR}\) suffices.
- Nevertheless, no specific atlas was supplied, so completeness is not proved. An ordered singular-value sector alone does not cover collision faces, zero singular values, or vanishing pivot minors.

For the second requested example, the exponent is adequate but the stated atom library has a genuine construction gap: a rectangular corank step is required on \(k=2,3,4\).

## 4. The raw determinantal charge

Verdict:

- “Raw Schur treatment always preserves the floor”: **NO**.
- “The charge forces SVD”: **NO**.
- “The charge is always dominated”: **NO**.

SVD is not analytically necessary because Cauchy–Binet gives
\[
\det(Q_bQ_b^\top)=
\sum_{|I|=b}\det(Q_{b,I})^2.
\]
Thus the charge can be resolved using raw minor-pivot and Schur-complement charts. But all pivot and blow-up Jacobians must be retained, and atom (C), as stated, contains no charged determinantal estimate.

Under formula (1), exact floor domination is equivalent to the recession conditions plus
\[
\boxed{
B_k(r)+2h(s-b+h)-a(h-r)_+
\ge
\mathrm{FLOOR}-us
}
\tag{4}
\]
for every \(h\in H_k\) and \(0\le r\le k\).

The two requested examples satisfy (4). The counterexample \((6,8,5,5),u=5\) does not.

## Requested numbers

| Widths and \(u\) | \(k\) | \(us\) | Lost codim | Charged \(C_k\) | Raw square status |
|---|---:|---:|---:|---:|---|
| \((4,4,4,4),u=3\) | 1 | 9 | 1 | 10 | square |
|  | 2 | 6 | 4 | 10 | square |
|  | 3 | 3 | 7 | 10 | square |
|  | 4 | 0 | 10 | 10 | square |
| \((3,4,5,4),u=2\) | 1 | 6 | 2 | 8 | square front factor |
|  | 2 | 4 | 4 | 8 | non-square |
|  | 3 | 2 | 6 | 8 | non-square |
|  | 4 | 0 | 8 | 8 | non-square |

Here
\[
\operatorname{minAdm}(3,4,4)=10,\qquad
\operatorname{minAdm}(2,5,4)=8.
\]

For the second example, \(r=k+1\) and \(u=2\), so only \(k=1\) has \(u=r\). Atom (B) also suffices only there because the residual requirement is \(2k\), exceeding \(u=2\) for \(k\ge2\).

Finally, the critical Jacobians are:

- the Vandermonde contribution \(2(k-i)\);
- the rectangular SVD factor \(\sigma_i^{p-k}\);
- \(dW_i=\sigma_i^{-u}\,d(\sigma_iW_i)\);
- the \(w^{us/2}\) Jacobian behind the Morse shift;
- every pivot/minor power in raw Schur charts.

Dropping either SVD measure factor lowers the computed codimension and can spuriously produce failure; dropping \(dW_i=\sigma_i^{-u}dP_i\) usually spuriously improves convergence. The claimed resolution is therefore not complete or sound until those chart maps and Jacobians are explicitly supplied.