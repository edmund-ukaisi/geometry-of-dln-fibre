## Q1 — Verdict: the PIVOT criterion

**FACT.** The pivot criterion is an iff statement for reaching the reduced comparator:

\[
u\rho\ge \operatorname{minAdm}(u,M_2,\ldots,M_L).
\]

Its failure is therefore a genuine obstruction to this head-split route.

**FACT.** The corank condition \(\mathrm{floor}\ge a+b\) is iff only for the cheap single-shell bound. Its failure does not imply divergence of the corank integral; the supplied co-minimizer result can prove finiteness beyond it.

**INFERENCE.** The route-specific boundary is the pivot criterion alone, not the corank criterion or their union. This does not contradict finiteness of \(I(M,c)\): it says only that this comparator/chart argument cannot deliver the required reduced threshold.

Scope caveat: if the supplied assertion about true corank finiteness covers only \(j=0\), the behavior of proper nonbinding shells \(j>0\) is under-specified. Even then, failure of the cheap corank inequality cannot be called divergence.

## Q2 — Verdict: co-minimizers do not rescue PIVOT

### \(M=(2,1,2)\)

**FACT.** The possible cuts are \(t=0,1\):

\[
\begin{aligned}
t=0 &: (2-0)(1-0)+\operatorname{minAdm}(0,2)=2+0=2,\\
t=1 &: (2-1)(1-1)+\operatorname{minAdm}(1,2)=0+2=2.
\end{aligned}
\]

Thus both \(0\) and \(1\) bind, and \(\rho=\min(1,2)=1\).

- At \(t=0\):
  \[
  t\rho=0=\operatorname{minAdm}(0,2).
  \]
  PIVOT passes. Here \((a,b)=(2,1)\), so the stated co-minimizer hypothesis applies, but only to CORANK.

- At \(t=1\):
  \[
  t\rho=1<\operatorname{minAdm}(1,2)=2.
  \]
  PIVOT fails. Here \((a,b)=(1,0)\), so there is no proper corank block and the co-minimizer hypothesis does not apply.

If the \(t=0\) resolution covers all shells, its \(j=1\) shell is \(u=1\) and encounters the same pivot failure.

### \(M=(3,2,3)\)

**FACT.**

\[
\begin{array}{c|c}
t & (3-t)(2-t)+3t\\ \hline
0&6\\
1&2+3=5\\
2&0+6=6
\end{array}
\]

Hence \(t^*=1\) is the unique binding cut and \(\rho=\min(2,3)=2\). But

\[
t^*\rho=2<\operatorname{minAdm}(1,3)=3.
\]

Thus PIVOT fails. Here \((a,b)=(2,1)\), so the co-minimizer hypothesis applies, but it cannot change the actual generic pivot rank \(\rho=2\). Indeed, the cheap three-width corank test already passes:

\[
\mathrm{floor}=M_2=3=a+b.
\]

There is also a terminology issue: if “deep rank” literally means ordinary rank of the stated \(M_2\times M_L\) matrix, the claimed bound \(a+b+1=4\) is impossible for both the \(2\times2\) and \(3\times3\) examples above. It must denote another resolution-rank statistic; otherwise that parenthetical premise is inconsistent. This does not affect the pivot calculation, where \(\rho\) was explicitly defined as actual matrix rank.

## Q3 — Verdict: NO

Under the stated reading that every shell \(u=t^*+j\), including \(j=0\), must be covered, the smallest counterexample is

\[
\boxed{(2,1,2)}.
\]

### General end argument

Let

\[
R_f=\min(M_2,\ldots,M_L).
\]

**FACT.** If \(M_1\ge R_f\), then \(\rho=R_f\), and permutation invariance plus the \(t=0\) recursion choice gives

\[
\operatorname{minAdm}(u,M_2,\ldots,M_L)
 \le uR_f=u\rho.
\]

Hence the front pivot criterion holds for every shell. Therefore front failure requires

\[
M_1<R_f.
\]

Similarly, back failure requires

\[
M_{L-1}<\min(M_0,\ldots,M_{L-2}).
\]

For at least four widths, simultaneous failure would imply both

\[
M_1<M_{L-1}
\quad\text{and}\quad
M_{L-1}<M_1,
\]

which is impossible. Thus two-ended obstructions occur only among three-width chains.

### Exact three-width family

Write \(M=(x,y,z)\). For every positive shell \(u\),

\[
\operatorname{minAdm}(u,z)=uz,\qquad \rho=\min(y,z).
\]

Thus the front fails exactly when \(y<z\), and the back fails exactly when \(y<x\). Consequently the complete two-ended family is

\[
\boxed{y<\min(x,z)}.
\]

These are precisely strict interior-waist triples. Their palindromic subfamily is \((r,s,r)\) with \(s<r\); reversal cannot help. Positivity makes \((2,1,2)\) the smallest member.

### Alternative shell readings

If only one chosen binding main shell \(j=0\) is tested, then

\[
F(t)=xy+t^2+(z-x-y)t.
\]

Allowing the best binding cut, both ends are unavoidably bad exactly when

\[
y<\min(x,z),\qquad |x-z|\le y-2.
\]

The smallest example is then \((3,2,3)\).

If every binding minimizer’s \(j=0\) chart must be covered, the condition becomes

\[
y<\min(x,z),\qquad |x-z|\le y-1,
\]

and \((2,1,2)\) is again smallest. The supplied wording explicitly includes \(j=0\), so the primary verdict is the first one.

## Q4 — Verdict: reversal is sound

Define reversed factors by

\[
B_i=A_{L-1-i}^{\mathsf T}.
\]

Then

\[
B_{L-1}\cdots B_0
=A_0^{\mathsf T}\cdots A_{L-1}^{\mathsf T}
=(A_{L-1}\cdots A_0)^{\mathsf T}=P^{\mathsf T}.
\]

Transpose and factor reversal merely permute scalar coordinates. Therefore:

- the cube \([-T,T]\) is preserved exactly;
- \(\|P^{\mathsf T}\|_F^2=\|P\|_F^2\);
- the zero target maps to itself;
- the linear map has determinant \(\pm1\), hence absolute Jacobian \(1\).

Thus \(I(M,c)=I(\operatorname{reverse}M,c)\), as an equality of extended nonnegative integrals, even if either side is infinite. For a nonzero target one would need to transpose the target as well.