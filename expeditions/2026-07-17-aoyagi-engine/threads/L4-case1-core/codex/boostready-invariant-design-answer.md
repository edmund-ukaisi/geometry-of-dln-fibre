The minimal stable strengthening is not “the extra coefficients are divisible by the pivot.” It is a termwise `diag(b)`/residual-path normal form. Divisibility is only its case11 corollary.

One correction forced by the definitions: `blockBlowupCoordQuot` does not add a pivot factor to center coordinates; it sets the pivot to `1`. Pivot factors are added by `blockBlowupMap` in the δ=0 branch.

## 1. The invariant

Write \(F_{p,j}=\operatorname{foldResid}(p)_j\), \(s=p.\mathrm{conState}\), and let \(\mathcal D_s\) be the active divisors. For \(d\in\mathcal D_s\), write \(b_d\) for its birth-corner coordinate.

For a threshold \(t\), define the suffix diagonal
\[
D_d(t)=\operatorname{diag}(1,\ldots,1,
\underbrace{u_{b_d},\ldots,u_{b_d}}_{\text{indices }\ge t}).
\]

The state should determine a canonical matrix word
\[
W_s(u)=R_{N-1,s}(u)\,D_{N-1,s}(u)\cdots
R_{1,s}(u)\,D_{1,s}(u)\,R_{0,s}(u),
\tag{NF-word}
\]
where:

- each \(D_{\ell,s}\) is the product of the suffix diagonals dictated by the active divisors and their thresholds at wire \(\ell\);
- the \(R_{\ell,s}\) are the canonical unit-pivot residual/Schur matrices;
- no \(R_{\ell,s}\) depends on an active birth coordinate \(u_{b_d}\);
- the first-clear matrix \(R_{L,s}\) contains the current block coordinates literally and linearly;
- the cleared stages are represented by the usual elementary factors
  \[
  L_c(\gamma),\qquad U_c(\beta),\qquad
  S_{rq}=u_{rq}-u_{rc}u_{cq}.
  \]

The invariant is:

\[
\boxed{
P(p):\quad
F_{p,j}(u)=\operatorname{slot}_j(W_s(u))
\quad\text{for every residual slot }j.
}
\tag{ChainNF}
\]

Equivalently, and slightly weaker, expand the matrix word into paths:
\[
F_{p,j}(u)
 =
 \sum_{\tau\in\operatorname{Paths}_s(j)}
 q_{s,j,\tau}(u)
 \prod_{d\in\mathcal D_s}u_{b_d}^{\,\varepsilon_{s,d}(\tau)}.
\tag{PathNF}
\]
Here:

- \(q_{s,j,\tau}\) is the product of the non-diagonal residual-matrix entries selected by \(\tau\);
- \(q_{s,j,\tau}\) ignores every active birth coordinate;
- \(\varepsilon_{s,d}(\tau)\) counts the suffix branches of the \(d\)-chain crossed by \(\tau\).

`PathNF` is the weakest form I would carry in Lean: equality of the individual matrices is unnecessary, but the compatible path labels and their threshold crossings are necessary.

At a fresh layer \(L\), include the already-banked support conjunct
\[
\sum_{i\in\operatorname{blockCoords}(L)}
  \nu_i=1
\]
for every monomial exponent \(\nu\) occurring in \(F_{p,j}\). This is the polynomial form of `hslot`. Thus the complete carried invariant is the existing fold invariant conjoined with `PathNF`; the genuinely new content is `PathNF`.

At a case11 δ=1 node, the b-chain arithmetic must give, for the divisor \(d_*\) whose birth coordinate is the outgoing pivot,
\[
\varepsilon_{s,d_*}(\tau)=
\begin{cases}
0,&\operatorname{col}(i_\tau)<\mathrm{runLen},\\
1,&\operatorname{col}(i_\tau)\ge\mathrm{runLen},
\end{cases}
\tag{case11-chain}
\]
where \(i_\tau\) is the unique current-block coordinate selected by \(\tau\).

Grouping the path expansion by \(i_\tau\) then gives
\[
F_{p,j}
 =
 \sum_{i\in\mathrm{partialBlock}}\alpha_i(u)u_i
 +
 u_{\mathrm{pivot}}
 \sum_{i\in\mathrm{extraBlock}}\beta_i(u)u_i.
\]
The \(\alpha_i,\beta_i\) are polynomials, hence continuous. After removing the unique current-block factor and the prescribed pivot factor, they contain neither a partial-block coordinate nor the pivot, so they ignore `ed.center`.

At the root, the diagonal word is empty and \(R_{\ell,\mathrm{root}}=C^{(\ell)}\); hence `PathNF` is exactly the usual compatible-index expansion of `coreGen`.

## 2. Preservation

For a real edge \(s\to s'\), the required master lemma is
\[
W_s(T_eu)=W_{s'}(u).
\tag{step-word}
\]

- δ=0 pullback:
  `blockBlowupMap` multiplies precisely the selected center entries by the pivot, which inserts or advances the corresponding suffix diagonal; the oracle’s threshold update is exactly the b-chain bookkeeping. For case2/case12, the canonical shear supplies the Schur identity; for case11/rollover the shear is the identity.

- δ=1 strict transform:
  `blockBlowupCoordQuot` evaluates the pivot at \(1\), hence dehomogenizes/removes the consumed diagonal factor. The canonical shear changes the residual block to
  \(S_{rq}=u_{rq}-u_{rc}u_{cq}\); the next-state threshold table identifies the remaining word. Again case11/rollover have no shear.

The local algebra behind case2/case12 is just
\[
L_c(\gamma)
\begin{pmatrix}1&0\\0&S\end{pmatrix}
U_c(\beta)
=
\begin{pmatrix}
1&\beta\\
\gamma&S+\gamma\beta
\end{pmatrix},
\]
so the minus sign in `canonShearOf` is exactly what is required.

## 3. Hardest step and missing facts

The single hardest lemma is not the polynomial algebra. It is the combinatorial transport statement
\[
\varepsilon_{s',d}(\tau')
 =
 \varepsilon_{s,d}(\tau)
 +\#(\text{entries selected from the blow-up center}),
\]
with the corresponding reset in the δ=1 branch, followed by the specialization `(case11-chain)`.

That requires the actual center/threshold transition table for case2, case11, case12, and rollover. Those transition rules were not transcribed, so preservation across all four cases cannot be concluded from the supplied facts alone.

A model of the transcription showing this gap uses \((2,2,2)\). Put
\[
a=u_{(0,0,0)},\quad z=u_{(0,1,0)},\quad
x=u_{(1,0,0)},\quad y=u_{(1,0,1)}.
\]
One core slot is
\[
F_{\rm root}=xa+yz.
\]
Take a δ=1 case2 edge with pivot \(a\). The canonical shear only changes the layer-0 strict interior, which this polynomial does not use, and the quotient sets \(a=1\). Thus at the child
\[
F=x+yz.
\]
Let that child be a layer-1 first-clear state with earlier divisor birth \(a\), run length \(1\), partial column \(0\), and extra column \(1\). Then `hslot` holds, but the extra coefficient is \(z\), not \(a\) times something. At \(a=x=0\), \(y=z=1\), the proposed target would vanish while \(F=1\).

This is not claimed to be a trace of Aoyagi’s actual oracle. It proves that the missing threshold/center transport law is logically essential; `IsRealBranch` alone does not supply it unless the oracle definitions force it.

A weaker marginal invariant also fails to induct: \(F=(x+z)y\) is separately affine in the current and future blocks, but a pullback with center \(\{b,x\}\) gives \((bx+z)y\), whose \(y\)-coefficient has neither exact \(b^0\) nor exact \(b^1\) provenance. Compatible residual paths are what rule this out.

## 4. Verdict

This is bounded and elementary once the four-case threshold-transport table is available: roughly 20–30 mathematical lemmas, perhaps 30–50 Lean helpers including `Finset` and cast bookkeeping. No genuinely new machinery beyond finite matrix sums and polynomial identities is needed.

However, it does require reopening the global fold induction: add `PathNF` as a new conjunct, or prove an equivalent parallel theorem
```lean
IsRealBranch p → ChainNF p
```
by the same path induction. It cannot be obtained locally from the existing `hslot`. The canonical-shear pin removes the algebraic obstruction; the remaining obligation is the oracle’s b-chain threshold arithmetic.