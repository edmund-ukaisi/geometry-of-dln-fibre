## 1. Component dimensions [exact]

Write
\[
a=\operatorname{rank}A_1,\qquad b=\operatorname{rank}A_2,\qquad
r=\operatorname{rank}(A_1A_2).
\]
Since
\[
r=b-\dim(\operatorname{im}A_2\cap\ker A_1),
\]
the exact \((a,b,r)\)-stratum has codimension
\[
C(a,b,r)
=(3-a)^2+(3-b)(4-b)+(b-r)(a-r).
\]
The last term is the Grassmannian incidence codimension. Feasibility requires \(a+b-r\le3\).

| \(s\) | Generic \((a,b,r)\) on component | Description | Codim | Dim |
|---|---:|---|---:|---:|
| 0 | \((0,3,0)\) | \(A_1=0\) | 9 | 12 |
| 0 | \((1,2,0)\) | geometric: \(\operatorname{im}A_2=\ker A_1\) | **8** | **13** |
| 0 | \((2,1,0)\) | geometric: \(\operatorname{im}A_2=\ker A_1\) | 9 | 12 |
| 0 | \((3,0,0)\) | \(A_2=0\) | 12 | 9 |
| 1 | \((1,3,1)\) | \(\operatorname{rank}A_1\le1\) | **4** | **17** |
| 1 | \((2,2,1)\) | geometric: \(\dim(\operatorname{im}A_2\cap\ker A_1)=1\) | **4** | **17** |
| 1 | \((3,1,1)\) | \(\operatorname{rank}A_2\le1\) | 6 | 15 |
| 2 | \((2,3,2)\) | \(\operatorname{rank}A_1\le2\) | **1** | **20** |
| 2 | \((3,2,2)\) | \(\operatorname{rank}A_2\le2\) | 2 | 19 |

Therefore
\[
\boxed{\operatorname{codim}V_0=8,\quad
\operatorname{codim}V_1=4,\quad
\operatorname{codim}V_2=1.}
\]

For \(s=1\), there are two dominant irreducible components.

## 2. Free versus reduced-layer codimension [exact]

\[
\begin{array}{c|c|c|c}
s & (3-s)(4-s)&\mu(3-s,3-s,4-s)&\operatorname{codim}V_s\\ \hline
0&12&\min(9,8,9,12)=8&8\\
1&6&\min(4,4,6)=4&4\\
2&2&\min(1,2)=1&1
\end{array}
\]

Thus the product codimension equals the reduced-tail layer minimum, not the free-matrix codimension.

The proposed general formula is

\[
\boxed{
\operatorname{codim}\{\operatorname{rank}(A_1\cdots A_{L-1})\le s\}
=\mu(M_1-s,\ldots,M_L-s)
}
\]
for \(0\le s\le\min_iM_i\). [conjectural in this generality]

Its geometric justification is that one splits off an \(s\)-dimensional transmitted identity channel; the normal slice is the zero-product problem on widths \(M_i-s\).

## 3. Tube exponent [exact for this chain]

Lebesgue measure on the entire parameter space is infinite, so interpret this inside a fixed compact region, or under a smooth probability density positive near the relevant strata.

There is no smaller power exponent here:

\[
\begin{array}{c|c|c}
q=s+1&\text{small-ball order}&\text{power exponent}\\ \hline
1&C_0t^8&8\\
2&C_1t^4\log(1/t)&4\\
3&C_2t&1
\end{array}
\]

Thus the power exponent equals \(\operatorname{codim}V_s\), but the literal form \(Ct^{\operatorname{codim}}\) fails for \(s=1\) because of the logarithm.

The log comes from the reduced normal model
\[
X_{2\times2}Y_{2\times3}.
\]
Its two layer minima \(4,4\) tie. If \(\alpha_1\ge\alpha_2\) are the singular values of \(X\), the transition region \(\alpha_2\lesssim t\lesssim\alpha_1\) contributes
\[
t^4\int_t^1\frac{d\alpha_1}{\alpha_1}
=t^4\log(1/t).
\]

At deeper strata \(\sigma_q\) can indeed vanish quadratically in parameter distance, but here those strata do not lower the leading power. In general, codimension alone does not rule out a smaller exponent; multiplicity must be checked separately.

## 4. Front-peel inequality [exact]

Yes. Put \(j=q-1\) in the assumed minimum:

\[
\begin{aligned}
\operatorname{minAdm}(M_0,\ldots,M_L)
&\le M_0(q-1)+\mu(M_1-q+1,\ldots,M_L-q+1)\\
&=M_0(q-1)+
\operatorname{codim}\{\operatorname{rank}(\text{tail product})\le q-1\}.
\end{aligned}
\]

So the desired inequality is precisely the \(j=q-1\) term, provided that index is admissible.