### U1

**Proven by Schur/coarea stratification:** if \(k=n-r'\), the effective codimension of pairs \((P,Z)\) whose product approaches rank \(r'\) is

\[
C_k=\min_{0\le a\le k}\bigl(a^2+k(k-a)\bigr)
=k^2-\lfloor k^2/4\rfloor .
\]

At the origin,

\[
A_{\rm scale}=n^2-C_n=\lfloor n^2/4\rfloor.
\]

Thus:

| \(n\) | \(A_{\rm scale}\) | \(\beta=n^2-A_{\rm scale}\) |
|---|---:|---:|
| 2 | 1 | 3 |
| 3 | 2 | 7 |
| 4 | 4 | 12 |

So \(A_{\rm scale}=n^2-\minAdm(n,n,n,n)\) is **false** from \(n=3\) onward: those proposed orders would be \(1,3,5\). Rather,

\[
\beta=\minAdm(n,n,n)=n^2-\lfloor n^2/4\rfloor .
\]

The radial shell is tight only for \(n=2\); for \(n=3,4\), angular degeneration lowers \(7\to6\) and \(12\to11\).

### U2

For corank \(k=n-r'\),

\[
\boxed{\gamma_{r'}=\lfloor k^2/4\rfloor}
\]

(up to logarithmic factors). Hence:

| \(n\) | rank \(r'\) | codim \(k^2\) | \(\gamma_{r'}\) |
|---|---:|---:|---:|
| 3 | 2 | 1 | 0, logarithmic |
| 3 | 1 | 4 | 1 |
| 3 | 0 | 9 | 2 |
| 4 | 3 | 1 | 0, logarithmic |
| 4 | 2 | 4 | 1 |
| 4 | 1 | 9 | 2 |
| 4 | 0 | 16 | 4 |

Rank \(0\) is not itself in the angular shell; its entry records the balanced-origin behavior.

### U3

No. For \(n=3\), the respective conditions are: all finite \(p\), \(p<4\), and \(p<9/2\). For \(n=4\): all finite \(p\), \(p<4\), \(p<9/2\), and \(p<4\).

Therefore, for every \(n\ge3\),

\[
\boxed{\rho_{\rm ang}\in L^p\iff 1\le p<4}
\]

locally over the whole angular shell. The endpoint \(p=4\) diverges.

### U4

The question’s asserted equivalence is false.

The **actual coupled bracket is finite** for every \(c'<c_n^*\). Indeed, the joint rank-\(r'\) chart has threshold

\[
\frac{C_k+nr'}2
=\frac{k^2-\gamma_{r'}+n(n-k)}2,
\]

whose minimum is \(3\) for \(n=3\), and \(11/2\) for \(n=4\).

But **pure Hölder using only \(B_n\)** has \(p<4\), hence \(q>4/3\), and reaches only

\[
c'<\frac34\cdot\frac{\minAdm(n,n,n)}2
=\frac38\minAdm(n,n,n).
\]

Thus:

- \(n=3\): reaches \(21/8\), versus \(3\); first gap \(3/8\).
- \(n=4\): reaches \(9/2\), versus \(11/2\); gap \(1\).

Joint stratification explains the missing finiteness, but proving its displayed threshold is itself a weighted/coupled estimate. It is not implied by the scalar unweighted statement \(B_n\).

### U5

\[
\boxed{\text{Using only the unweighted }B_n,\text{ the shell route reaches sharply only for }n\le2.}
\]

For \(n\ge3\), one must add either a weighted/coupled black box controlling  
\(\rho_{\rm ang}(X)\|XW\|^{-2c'}\), or pinned charts \(\sigma_{\min}(P)\ge\delta\) together with summable \(\delta\)-dependence. Both contain localized information strictly stronger than unweighted \(B_n\).