### Q1

[FACT] **NO.** The smallest counterexample is
\[
M=(3,4,3,1),\quad t=1,\quad j=1.
\]
Then
\[
r=\min(2,3)=2,\quad u=2,\quad a=1,\quad b=2,
\quad \operatorname{deepTailMin}(M)=\min(3,1)=1.
\]

[FACT] All assumptions hold: (S1) \(1\le4\); (S2) \(1\le j=1<2=r\); and (S3) \(a+b=3\le M_2=3\). Nevertheless \(b=2>1\).

[FACT] Minimality follows because failure requires \(b\ge2\), while the strict shell forces \(a\ge1\) and \(u=t+j\ge2\). Hence \(M_0=a+u\ge3\), \(M_1=b+u\ge4\), and \(M_2\ge a+b\ge3\). Arity \(3\) cannot fail.

### Q2

[FACT] **PROVED.** Put
\[
D=\operatorname{deepTailMin}(M),\quad
A=M_0-t^*,\quad B=M_1-t^*.
\]
Since \(j<\min(A,B)\), we have \(A,B\ge2\), so \(t^*+1\) is admissible.

[FACT] For
\[
f(t)=(M_0-t)(M_1-t)+g(t),
\]
optimality gives
\[
0\le f(t^*+1)-f(t^*)
=-(A+B-1)+\bigl(g(t^*+1)-g(t^*)\bigr).
\]
Using Q3,
\[
A+B-1\le g(t^*+1)-g(t^*)\le D.
\]
Therefore
\[
b=B-j\le B-1\le A+B-1\le D.
\]

### Q3

[FACT] The tight uniform bound is
\[
0\le g(t+1)-g(t)\le D.
\]

[FACT] Induct on tail length. Writing its first width as \(q\), reuse an optimizer \(s\) for \(g(t)\) when \(D=q\), giving increment \(q-s\le D\). When \(D\) lies deeper and \(s<q\), use \(s+1\); its increment is
\[
g_{\rm tail}(s+1)-g_{\rm tail}(s)-(t-s)\le D.
\]
If \(s=q\), reusing \(s\) gives increment \(0\). Monotonicity follows similarly by reusing an optimizer for \(t+1\), or decreasing \(s=t+1\) to \(t\).

### Q4

[INFERENCE] At binding cuts, the required route is **(b) plus (c)**: binding optimality proves \(b\le D\), while generic rank gives \(\operatorname{rank}Z_{\rm deep}=D\) almost everywhere.

[FACT] Route (a) is insufficient by Q1. Some generic-rank input is logically unavoidable because rank can drop on exceptional parameters. However, a **fresh** proof of (c) is avoidable if the supplied standard generic-rank theorem is already available.