## Q1

**VERDICT: claim correct.**  
**Hypothesis:** the integrand is nonnegative Lebesgue-measurable; it may be unbounded or \(+\infty\).  
For each \(A\), the determinant-zero locus is null, so its integral is \(0\), and the extended integrals are exactly equal.  
Divergence near it is charged to surrounding positive-measure neighborhoods, never to the null set itself.  
**Most likely error:** confusing “unbounded near a null set” with “nonzero integral over that null set.”

## Q2

**FACT:** As stated, no universal threshold follows: \(ZZ^\top\succ0\) does not ensure \([Q_p;Z]\) has full row rank.  
**FACT (assuming that transversality):** put \(r=u+a\), so \(m=ru\); then \(L\asymp\lVert C\rVert^2+\lVert DA\rVert^2\).  
**FACT:** \(\displaystyle \sup c'=\frac{m+\tau}{2},\quad \tau=\min_{0\le q\le\min(a,b)}\!\bigl[rq+(a-q)(b-q)\bigr]=ab+\min_q q(q+u-b).\)  
**INFERENCE:** \(\tau=ab\) iff \(a=0\) or \(b\le u+1\); e.g. \(u=1,a=b=3,m=4\) gives \(\sup c'=6\), not \(6.5\).  
**FACT:** near generic corank one, \(p=m+r(b-1)\), \(\beta(c')=(c'-p/2)_+\), and \(J(A)\asymp g^{-\beta}\), with a logarithm at equality.  
**FACT:** its normal codimension is \(d=a-b+1\) (one only if \(a=b\)); outer convergence is \(2\beta<d\).  
**VERDICT:** the claimed threshold is incorrect generally; deeper rank strata can make it smaller, never larger.