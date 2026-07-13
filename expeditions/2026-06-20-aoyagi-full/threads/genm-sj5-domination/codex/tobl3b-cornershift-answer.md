### Q1 [exact]

Let \(m=M_2-j\). PSD monotonicity gives
\[
\det(A_{\rm cor}ZZ^\top A_{\rm cor}^\top)^{-a/2}
\le \varepsilon^{-ab}\det(XX^\top)^{-a/2},
\qquad X=A_{\rm cor}U_s\in\mathbb R^{b\times m}.
\]
Thus the output has rows \(b\), columns \(M_2-j\), and exponent \(a\). It converges iff \(a<M_2-j-b+1\). At the anchor this is rows \(2\), columns \(2\), exponent \(2\), while \(2-2+1=1\), so it diverges. When \(m>b\), Cauchy–Binet gives a sum over strong \(b\)-minors, not one determinant of a rectangular block.

### Q2 [exact]

Relative to Q1, rows must decrease by \(j\) and the exponent by \(j\); columns are already correct. The bare bordered-Gram identity changes none of these quantities. For an actual row CoV, writing \(q_b=\lambda Y+v\) with \(Y=(q_1,\ldots,q_{b-1})\) and \(v\perp\operatorname{rowspan}Y\) gives \(dq_b=\det(YY^\top)^{1/2}d\lambda\,dv\). Consequently
\[
\det(G_b)^{-a/2}dq_b
=\det(G_{b-1})^{-(a-1)/2}\|v\|^{-a}d\lambda\,dv,
\]
so the residual Gram has rows \(b-1\), unchanged columns, and exponent \(a-1\). The Jacobian is \(\det(G_{b-1})^{1/2}\), not the full strong minor; moreover the transverse factor and generally unbounded \(\lambda\)-fibres remain. At the anchor \(v\in\mathbb R\) and \(\int|v|^{-2}dv=\infty\), so this does not supply a bounded constant.

### Q3 [exact]

At the anchor, with weak singular value \(s\), Cauchy–Binet locally gives \(\det(QQ^\top)\asymp u^2+s^2v^2\). Integrating through a generic strong-minor zero yields \(\int du/(u^2+s^2v^2)\asymp s^{-1}|v|^{-1}\), so the weak-singular-value power is \(s^{-1}\). In fact the full weight is already infinite for every \(s>0\), since its rows/columns/exponent are \(2/3/2\) and the convergence test requires \(2<3-2+1=2\); the remaining divergence is logarithmic. Thus \(s^{-1}\) is the coefficient under a rank cutoff, not a finite asymptotic for \(\mathrm{Wenn}\). With one row and exponent \(1\), weak elimination gives rows \(1\), columns \(2\), exponent \(1\), and \(1<2\), so that integral stays bounded as \(s\to0\).

### Q4 [inference]

Weak-direction elimination accounts only for columns \(M_2\to M_2-j\). A fixed-cut Schur CoV formally changes rows \(b\to b-j\) and exponent \(a\to a-j\), but it also leaves transverse singular factors and uncontrolled coefficient fibres; the listed tools do not bound them. A valid direct mechanism is instead to re-peel at \(t^*+j\), where the definitions themselves give corank rows \(b-j\) and corner height—and hence determinant exponent—\(a-j\). Row reindexing merely permutes rows and cannot delete \(j\) of them. Without permission to change the cut, an additional measure-disintegration theorem controlling those fibres and transverse factors is required; none is banked.

### Q5 [inference]

At the re-indexed cut \(t^*+j\), PSD monotonicity directly produces rows \(b-j\), columns \(M_2-j\), and exponent \(a-j\). Thus bordered-Gram is unnecessary if the shell argument legitimately re-peels at that cut. Its true role is diagnostic: it exposes the formal Gram/Jacobian bookkeeping and the leftover transverse divergence, but it does not prove the fixed-cut domination asserted in the prior note.

VERDICT: bordered-Gram is NOT load-bearing; the corner-shrink is a re-peel at \(t^*+j\) followed by PSD weak-direction elimination.