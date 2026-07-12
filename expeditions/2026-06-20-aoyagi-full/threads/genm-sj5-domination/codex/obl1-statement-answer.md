Verdict: choose **(A)**, but the claimed uniformity on “top \(M_2-1\) singular values bounded below” is false as stated.

1. After the absorption shear, (A) is the correct fibrewise interface. Writing \(Y=A_{\mathrm{cor}}\), \(Q_p=XZ\), and
\[
B=P X+B_{12}Y,
\]
gives
\[
P\widetilde Q_p=BZ,\qquad
C\widetilde Q_p+\Gamma Q_b=CP^{-1}BZ+\Gamma(YZ).
\]
Thus \(w=\|BZ\|_F^2\) is genuinely independent of \(Y\) once \(B,Z\) and the other outer parameters are fixed. The map \((X,Y)\mapsto(B,Y)\) is triangular; its Jacobian depends on \(P\), not \(Y\).

“Fixed \(w\)” therefore means fixed along the \(A_{\mathrm{cor}}\)-fibre. It may remain a measurable function of the outer variables, exactly as required by the reduced IH. A transformed box can still have coupled support, but that is an assembly/domain-enlargement issue, not residual dependence of \(w\).

(B) is only a useful test specialization. (C) does not solve the cancellation problem and supplies the wrong comparator. So (A) is faithful post-absorption.

2. If the actual hypothesis is
\[
\operatorname{minStretch}(Z^\top)\ge c_0,
\]
then there is no rectangular-matrix subtlety:
\[
\|A_{\mathrm{cor}}Z\|
=\|Z^\top A_{\mathrm{cor}}^\top\|
\ge c_0\|A_{\mathrm{cor}}\|.
\]
This works equally for \(Z:M_2\times q\) with \(q\ge M_2\).

But bounding only the top \(M_2-1\) singular values does not imply this. Take
\[
Z_\varepsilon=[\operatorname{diag}(1,\ldots,1,\varepsilon)\ \ 0].
\]
It is full row rank for every \(\varepsilon>0\), while its least singular value tends to zero. Then:

- at \(a=M_2-1\), \(\int\|A_{\mathrm{cor}}Z_\varepsilon\|^{-a}\) grows like \(\log(1/\varepsilon)\);
- for \(\varepsilon\ll r\),
  \[
  \operatorname{vol}\{\|A_{\mathrm{cor}}Z_\varepsilon\|<r\}\asymp r^{M_2-1},
  \]
  not \(r^{M_2}\).

Consequently, on that weaker chart an additional log already appears at \(a=M_2-1\), while \(a=M_2\) suffers a half-power loss. The advertised fixed-\(w\), uniform-\(Z\) estimate cannot hold there. Exploiting the special relation \(w=\|\Gamma'Z\|^2\) would require retaining the smallest-singular-value dependence or proving a joint \((\Gamma',A_{\mathrm{cor}})\) estimate.

3. For the first checkpoint, prove (A) with:

- quantitative full injectivity \(\operatorname{minStretch}(Z^\top)\ge c_0\);
- strict \(a<M_2\).

Then handle \(a=M_2\) separately with \(1+\log_+(K/w)\). If you retain only the top-\(M_2-1\) chart, neither proposed endpoint policy is faithful: the clean range is only \(a<M_2-1\).

4. For \(b=1\),
\[
\tau=\sqrt{\det(Q_bQ_b^\top)}=\|Q_b\|_F.
\]
This is the sole standard singular value. Splitting directly on \(\|Q_b\|\) is cleanest. In Lean terminology, beware that `minStretch` of the wide map \(Q_b:\mathbb R^q\to\mathbb R\) is zero when \(q>1\); the equal quantity is `minStretch` of \(Q_b^\top:\mathbb R\to\mathbb R^q\).