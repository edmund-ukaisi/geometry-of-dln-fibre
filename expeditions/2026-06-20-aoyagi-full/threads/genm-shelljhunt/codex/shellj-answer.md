## Q1: Exact shell threshold

- [FACT] Write
  \[
  m=M_0,\qquad n=M_1,\qquad p=M_2,\qquad k=\min(n,p),\qquad \ell=k-j.
  \]

- [FACT] Every \(W\in S_j\), and every matrix in its closure, has rank at least \(\ell\), because \(\ell\) singular values remain at least \(\varepsilon>0\).

- [FACT] On the rank-\(B=s\) stratum, \(BW=0\) implies
  \[
  \operatorname{im}W\subseteq\ker B,\qquad \operatorname{rank}W\le n-s.
  \]
  Hence this stratum is shell-reachable exactly when
  \[
  \ell\le n-s,\qquad\text{i.e.}\qquad s\le n-k+j.
  \]

- [FACT] Thus the reachable ranks are
  \[
  0\le s\le R_j,\qquad R_j:=\min\{m,n-k+j\}.
  \]

- [FACT] For each such \(s\), one can choose \(W\) with \(\ell\) singular values \(>\varepsilon\), \(j\) zero singular values, and image contained in \(\ker B\). Thus the rank cap is also sufficient.

- [FACT] The codimension of the rank-\(B=s\) zero-product stratum is
  \[
  C(s)=(m-s)(n-s)+sp.
  \]

- [FACT] Therefore
  \[
  \boxed{\lambda_j=\frac12\min_{0\le s\le R_j}\bigl((m-s)(n-s)+sp\bigr).}
  \]

- [FACT] An explicit minimizing index is
  \[
  s_j=\min\!\left(R_j,\max\!\left(0,\left\lfloor\frac{m+n-p}{2}\right\rfloor\right)\right),
  \]
  with the usual possible adjacent tie when \(m+n-p\) is odd. Hence
  \[
  \boxed{\lambda_j=\frac{(m-s_j)(n-s_j)+s_jp}{2}.}
  \]

- [FACT] Relative to the full box, the shell deletes precisely the zero-product strata with
  \[
  s>n-\min(n,p)+j.
  \]
  Consequently \(\lambda_j\ge\lambda_{\mathrm{full}}\).

- [FACT] The condition \(\det(P)\ne0\) removes a Lebesgue-null subset of the \(B\)-box. Therefore
  \[
  \int_{\det P\ne0}f^{-c'}\,dB\,dW
  =
  \int f^{-c'}\,dB\,dW
  \]
  as extended nonnegative integrals.

- [FACT] Even rank-\(B<u\) strata remain in the closure of \(\{\det P\ne0\}\), since invertible-minor matrices are dense. Removing the zero stratum itself does not remove its divergent punctured neighborhoods.

## Q2: Requested cases

- [FACT] For \(M=(6,6,6)\),
  \[
  C(s)=(6-s)^2+6s,
  \]
  and
  \[
  C(0),\ldots,C(6)=36,31,28,27,28,31,36.
  \]
  Thus \(t^*=3\) and
  \[
  T1=\frac{27}{2}.
  \]

- [FACT] For \(j=1\), \(R_1=1\), so
  \[
  \lambda_1=\frac{C(1)}2=\frac{(5)(5)+6}{2}=\frac{31}{2}.
  \]
  With \(u=4\), \(a=b=2\),
  \[
  T2=\frac{4\cdot6+2\cdot2}{2}=14.
  \]
  Hence
  \[
  \frac{27}{2}=T1<14=T2<\lambda_1=\frac{31}{2}.
  \]

- [FACT] For \(j=2\), \(R_2=2\), so
  \[
  \lambda_2=\frac{C(2)}2=\frac{(4)(4)+12}{2}=14.
  \]
  With \(u=5\), \(a=b=1\),
  \[
  T2=\frac{5\cdot6+1}{2}=\frac{31}{2}.
  \]
  Hence
  \[
  \frac{27}{2}=T1<\lambda_2=14<T2=\frac{31}{2}.
  \]

- [FACT] For \(M=(4,4,4)\),
  \[
  C(0),\ldots,C(4)=16,13,12,13,16,
  \]
  so \(t^*=2\) and \(T1=12/2=6\).

- [FACT] At \(j=1\), \(R_1=1\), and
  \[
  \lambda_1=\frac{C(1)}2=\frac{(3)(3)+4}{2}=\frac{13}{2}.
  \]
  With \(u=3\), \(a=b=1\),
  \[
  T2=\frac{3\cdot4+1}{2}=\frac{13}{2}.
  \]
  Hence
  \[
  T1=6<\lambda_1=T2=\frac{13}{2}.
  \]

- [FACT] For \(M=(8,8,8)\),
  \[
  C(0),\ldots,C(8)=64,57,52,49,48,49,52,57,64.
  \]
  Thus \(t^*=4\) and \(T1=48/2=24\).

- [FACT] At \(j=1\),
  \[
  \lambda_1=\frac{C(1)}2=\frac{49+8}{2}=\frac{57}{2}.
  \]
  With \(u=5\), \(a=b=3\),
  \[
  T2=\frac{40+9}{2}=\frac{49}{2}.
  \]
  Hence
  \[
  24=T1<\frac{49}{2}=T2<\lambda_1=\frac{57}{2}.
  \]

- [FACT] At \(j=2\),
  \[
  \lambda_2=\frac{C(2)}2=\frac{36+16}{2}=26.
  \]
  With \(u=6\), \(a=b=2\),
  \[
  T2=\frac{48+4}{2}=26.
  \]
  Hence
  \[
  T1=24<\lambda_2=T2=26.
  \]

- [FACT] At \(j=3\),
  \[
  \lambda_3=\frac{C(3)}2=\frac{25+24}{2}=\frac{49}{2}.
  \]
  With \(u=7\), \(a=b=1\),
  \[
  T2=\frac{56+1}{2}=\frac{57}{2}.
  \]
  Hence
  \[
  T1=24<\lambda_3=\frac{49}{2}<T2=\frac{57}{2}.
  \]

## Q3: Domination

- [FACT] The comparator is finite exactly when
  \[
  c'-\frac{ab}{2}<\frac{up}{2},
  \qquad\text{i.e.}\qquad c'<T2.
  \]

- [FACT] The shell integral is finite exactly when \(c'<\lambda_j\).

- [FACT] Therefore the domination is impossible for any
  \[
  \boxed{\lambda_j\le c'<T2}
  \]
  whenever \(\lambda_j<T2\): its left side is infinite while its right side is finite.

- [FACT] If both integrals are finite, then for fixed \(c'\) and positive \(G\), some finite constant \(C=I_j/G\) exists. This does not validate any separately prescribed or uniform constant.

- [FACT] If \(G=\infty\), the extended-real inequality is vacuous and yields no finiteness information.

- [FACT] The requested false-domination intervals are:
  \[
  M=(6,6,6),\ j=2:\quad 14\le c'<\frac{31}{2},
  \]
  and
  \[
  M=(8,8,8),\ j=3:\quad \frac{49}{2}\le c'<\frac{57}{2}.
  \]

## Q4: Final adjudication

- [FACT] For every shell,
  \[
  I_j(c')\le I_{\mathrm{full}}(c').
  \]
  Hence \(c'<T1\) always implies \(I_j(c')<\infty\).

- [FACT] **Divergence at some \(c'<\tfrac12\minAdm(M)\): NO.** No shell can diverge below the full-box threshold.

- [FACT] **Divergence at some \(c'<T2\): YES.** For example,
  \[
  M=(6,6,6),\quad j=2,\quad c'=14<\frac{31}{2}=T2,
  \]
  but \(I_2(14)=\infty\).

- [INFERENCE] If the surrounding proof invokes the domination only under \(c'<T1\), there is no RLCT wall in its used range. If it asserts the domination throughout the comparator-finite range \(c'<T2\), that stronger assertion is false in the configurations above.