## Overall verdict

**v3 does not clear the “no false frontier statements” bar.** Target 4 is false as stated, and the same counterexample kills two other Object-A frontiers.

## 1. Change of variables

**VERDICT: GAP, not an explicit counterexample.**  
**Definitions VERIFIED; sufficiency INFERRED/unresolved.**

Both `rlctAt` and `wrlctAt` are genuinely local neighborhood-filter germs. Hence certifying `unit` only near `0` is sufficient.

The unresolved issue is localization of covering preimages. `hcover`

\[
\forall^\mathrm{eventually}_{w\to x_0}\ \exists u,\ g(u)=w
\]

does not say that \(u\to0\), nor that any neighborhood of \(0\) covers a neighborhood of \(x_0\).

The sharp near-counterexample is

\[
g(x,y)=(x,xy),\qquad F(X,Y)=X.
\]

It satisfies every relevant field except pointwise `hcover`:

- analytic, \(g(0)=0\);
- injective off the null line \(x=0\);
- \(|\det Dg|=|x|=\operatorname{jacWeight}(1,0)\);
- \(F\circ g=x\), so the monomial/ideal fields hold.

But

\[
\operatorname{rlct}_0(X^2)=\frac12,
\]

whereas locally at the source

\[
\int |x|(x^2)^{-c}\,dx\,dy
=\int |x|^{1-2c}\,dx\,dy
\]

has threshold \(1\). Preimages \(y=Y/X\) escape every source neighborhood. This map misses only \((0,Y\ne0)\), so it fails the actual `hcover`.

Thus this is not an all-hypothesis kill, but it proves that global/a.e. coverage is insufficient. The missing proof must derive local filter-surjectivity from analyticity, full `hcover`, and a.e. injectivity. A direct field such as

\[
\mathcal N(x_0)\le \operatorname{map}(g,\mathcal N(0))
\]

would close the issue explicitly.

## 2. Monomial rule

**VERDICT: SOUND-as-stated — VERIFIED.**

Take

\[
e_0=(1,2,1),\qquad e_1=(2,3,4),\qquad h=(3,0,5).
\]

The chain holds because \(e_0\le e_1\) coordinatewise. Factoring the dominant monomial gives a unit nonzero at zero, and the weighted integrand is comparable to

\[
|x|^{3-2c}|y|^{-4c}|z|^{5-2c}.
\]

Its integrability conditions are

\[
c<2,\qquad c<\frac14,\qquad c<3,
\]

so the threshold is \(1/4\), exactly the axis formula.

For any coupled valuation \(v=(a,b,c)\),

\[
\frac{4a+b+6c}{2(a+2b+c)}
\]

is the weighted average of \(2,\frac14,3\), with weights \(a,2b,c\). It cannot be below \(1/4\). The chain hypothesis genuinely removes coupled Newton improvements.

## 3. `exists_coreResolution`

**VERDICT: GAP/over-strong monument — VERIFIED mismatch, no formal nonexistence proof.**

The paper states a minimum over resolution charts. The record instead asks for one analytic map \(\mathbb R^D\to\mathbb R^D\) whose image covers a full neighborhood.

The smallest stress case is \(N=1\), \(d=(1,2)\). Its QIP has the single feasible value

\[
qipMin=1(1+2-1)=2.
\]

The intended ideal is \(\langle x,y\rangle\). Its first blow-up has charts

\[
(u,v)\mapsto(u,uv),\qquad (u,v)\mapsto(uv,u).
\]

Each principalizes the ideal and has Jacobian weight \(|u|\), but neither covers a neighborhood; both charts are required jointly. Thus the paper’s construction does not directly inhabit this single-chart record.

Conversely, the theorem underconstrains its witness: arbitrary \(D,M,F\) are existentially chosen, with no equation identifying \(F\) with flattened DLN product entries. Therefore an exotic synthetic witness is not excluded. I cannot certify “no structure exists,” but the stated monument does not faithfully express the cited construction.

## 4. `rlctAt_mono_of_ae_le`

**VERDICT: COUNTEREXAMPLE — VERIFIED.**

Identify \(\mathbb R^{\mathrm{Fin}\,1}\) with \(\mathbb R\), and define

\[
K(t)=
\begin{cases}
0,&t\le0,\\
t^4,&t>0,
\end{cases}
\qquad
K'(t)=
\begin{cases}
t^{10},&t<0,\\
t^2,&t\ge0.
\end{cases}
\]

Near zero, \(0\le K\le K'\), \(K'\) is measurable, and its admissible exponents are bounded.

Because `negPow` uses `Real.rpow`, \(0^{-c}=0\) for \(c>0\). Hence

\[
\operatorname{rlctAt}(K,0)=\frac14,
\]

while

\[
\operatorname{rlctAt}(K',0)
=\min\left(\frac1{10},\frac12\right)
=\frac1{10}.
\]

The claimed conclusion becomes \(1/4\le1/10\), false.

The hypothesis is topological `Eventually`, not measure-theoretic “a.e.” It needs an a.e.-nonzero/strict-positivity guard on \(K\), or a different extended-valued negative-power definition.

This also kills:

- `rlctAt_sumSqFam_le_of_germRepresents`;
- `wrlctAt_sumSqFam_le_of_germRepresents` with \(W=1\).

Indeed take

\[
F(t)=
\begin{cases}
t^5,&t<0,\\
t,&t\ge0,
\end{cases}
\qquad
a(t)=\max(t,0),\qquad G=aF.
\]

Then `GermRepresents G F 0` via continuous coefficient \(a\), but

\[
\operatorname{rlct}(G^2)=\frac14>\frac1{10}
=\operatorname{rlct}(F^2).
\]

## 5. Sorry audit

| File | Executable `sorry` | Raw `sorry` substrings |
|---|---:|---:|
| `IdealInvariance.lean` | 6 | 8 |
| `MonomialRLCT.lean` | 3 | 3 |
| `ProductResolution.lean` | 4 | 4 |
| `Engine.lean` | 0 | 0 |
| `Order.lean` | 0 | 0 |
| `LearningCoefficient.lean` | 1 | 4 |
| **Total** | **14** | **19** |

The raw 19 includes two docstring occurrences and three `sorryAx` substrings. The claimed real count of 15 is wrong; it is 14.

Guard status:

- `not_divChain_coupled_example`: **proved, no sorry**.
- `no_unit_forces_axis_jac_coupled`: **not proved**; its proof is exactly `sorry` at line 173. Its statement also uses equality for all \(u\), whereas the record certificate is only eventual near zero.

`Engine.lean` and `Order.lean` contain zero local sorries. Engine’s assembled theorem still depends on sorried upstream results.

## Remaining sorried-statement scan

- `eventually_sumSqFam_le_of_germRepresents`, constant scaling, and weight-one: sound.
- All three monomial statements: sound.
- The two derived Resolution value statements remain contingent on the CoV gap and currently route through false one-sided weighted invariance.
- The Jacobian obstruction statement is true but unproved.
- `exists_coreResolution` is an over-strong/underconstrained interface rather than a verified construction.

Ranked defects:

1. **Kill:** Object-A monotonicity and both one-sided ideal-invariance statements are false.
2. **Serious gap:** CoV lacks explicit local source coverage/properness.
3. **Serious fidelity gap:** single-chart existence does not match the paper’s atlas/minimum-over-charts construction.
4. **Audit failure:** one negative guard is sorried; executable-sorry count is 14, not 15.