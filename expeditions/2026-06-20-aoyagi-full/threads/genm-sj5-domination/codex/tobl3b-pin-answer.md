UNIFORM — Q1. Put \(k=M_2-j\) and \(N=\binom{M_2}{k}\binom nk\). Cauchy–Binet proves that some chart minor \(\Delta\) satisfies
\[
|\Delta|\ge N^{-1/2}\varepsilon_j^k,\qquad |\Delta|\le k^{k/2}B^k
\]
for a box of entry-radius \(B\), independently of the weak singular values. If the CoV applies this minor to \(q\) row vectors, then
\[
J_{\rm fwd}=|\Delta|^q,\qquad J_{\rm inv}=|\Delta|^{-q}
 \le N^{q/2}\varepsilon_j^{-kq}.
\]
Anchor \(j=1\): \(k=2,N=9\), so \(|\Delta|\ge\varepsilon_1^2/3\). F1–F5 do not specify \(q\), so the full Jacobian’s exact exponent requires the explicit CoV formula.

STRICTLY-CONVERGENT — Q2. For \(b-j>0\), F1 applied to
\[
a'=a-j,\quad b'=b-j,\quad M_2'=M_2-j
\]
gives finiteness exactly when
\[
a-j<(M_2-j)-(b-j)+1=M_2-b+1.
\]
Equivalently, \(a<M_2-b+j+1\). Thus a shell-0 borderline \(a=M_2-b+1\) becomes strict for every \(j\ge1\); no new \(\theta\) is needed. Anchor \(j=1\): \(1<2\). A zero-row or zero-exponent terminal weight is trivially finite. Without \(a\le M_2-b+1\), strict convergence is not automatic from F1–F5.

DOMINATION — Q3. The reduced least-squares base contains
\[
\|C(I-P_Q)\|_F^2,\qquad P_Q=Q^T(QQ^T)^{-1}Q,
\]
so it is rational and generically not the polynomial comparator loss. When the remaining base is \(L_{\rm comp}+R\), \(R\ge0\),
\[
(L_{\rm comp}+R)^{-e}\le L_{\rm comp}^{-e}\qquad(e>0).
\]
Hence the valid target is a clean \(\le\), after controlling the reduced Gram weight; not equality. F1–F5 alone do not prove the identification \(L_{\rm comp}+R\), so the explicit shell-\(j\) algebra is still owed. The terminal zero-corner case may exceptionally be exact.

BREAK: SATURATED-SHELL ESCAPE — Q4. At the anchor choose
\[
Z_\delta=\delta I_3,\qquad 0<\delta<\min(\varepsilon_0,\varepsilon_1,\varepsilon_2).
\]
Then \(Z_\delta\) lies in none of the displayed shells: every required lower bound \(\sigma_{3-j}\ge\varepsilon_j\) fails. If shell \(j=2\) is redefined to include it, its required \(1\times1\) minor is at most \(\delta\), so F5 supplies no uniform inverse-Jacobian bound; any positive inverse power diverges as \(\delta\to0\). Also \(w(Z_\delta)=\delta^2\|\Gamma'\|_F^2\), so pivot energy cannot repair the constant. A normalized annulus, dyadic radial shells, or a terminal no-minor domination lemma would settle this.

T-Obl3b has a genuine obstruction as stated; \(c'<7/2\) closes the exponent budget, but not the uncovered all-small-\(Z\) branch or the unspecified CoV/residual formula.