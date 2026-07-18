## Q_A

I use the implicit convention that divisors persist unless explicitly mutated, and that the two Case-1 charts form a covering split. This persistence/boot convention is inferred rather than fully specified in the transcription.

At \(S=1\), the divisor profiles are

\[
(0,0,0)[4],\qquad A=(1,1,1)[1],
\]

where brackets contain \(M\). The full-rank level \(r=2\) has \(M=0\) and is not an exceptional divisor.

At \(S=2,J=0\), \(A\) gives Case 1 with \(J_1=1\):

- Mutate \(A\): \((1,0,0)\), with \(M=1+1\cdot2=3\). The exhausted level then gives Case 2: \((2,0,0)[4]\).
- Create from \(A\): a new \((1,0,0)[3]\), while \(A\) remains.

At \(S=2,J=1\), Case 2 creates

\[
B=(2,1,1)[(2-1)(2-1)]=(2,1,1)[1].
\]

Thus the two \(S=2\) chart types have:

\[
\begin{aligned}
U &: \{000[4],100[3],200[4],211[1]\},\\
V &: \{000[4],100[3],111[1],211[1]\}.
\end{aligned}
\]

The given \(S=3,J=0\) node occurs in \(V\), where \(A<B\). Processing the ordered level-\(1\) divisors and then applying Case 2 when that level is exhausted gives five terminal combinatorial chart types. Every chart also receives \((2,2,1)[1]\) at \(S=3,J=1\).

| Chart path | Terminal \(\widetilde t=0\) divisors | Remaining \(\widetilde t>0\) divisors |
|---|---|---|
| \(U\): mutate \(B\) | \(000[4],100[3],200[4],210[3],220[4]\) | \(221[1]\) |
| \(U\): create from \(B\) | \(000[4],100[3],200[4],210[3]\) | \(211[1],221[1]\) |
| \(V\): create from \(A\) | \(000[4],100[3],110[3]\) | \(111[1],211[1],221[1]\) |
| \(V\): mutate \(A\), create from \(B\) | \(000[4],100[3],110[3],210[3]\) | \(211[1],221[1]\) |
| \(V\): mutate \(A\), mutate \(B\) | \(000[4],100[3],110[3],210[3],220[4]\) | \(221[1]\) |

Hence the union of terminal \(\widetilde t=0\) profiles is exactly

\[
000,\ 100,\ 110,\ 200,\ 210,\ 220.
\]

As an elementary coverage audit, every zero \(P=0\) has partial-product ranks

\[
\bigl(\operatorname{rank}C^{(1)},
      \operatorname{rank}(C^{(1)}C^{(2)}),0\bigr),
\]

which must be one of precisely those six weakly decreasing triples. Thus there is no missing rank stratum.

Coverage verdict, scoped: taking “two charts” as a genuine covering split and including the suppressed pivot charts, the emitted atlas has no combinatorial coverage gap. The transcription omits the coordinate maps, so the stronger statement that every individual nearby zero has a lift cannot be independently proved from the supplied data alone.

## Q_B

Direct substitution in

\[
M=(2-t^1)^2+(t^1-t^2)(2-t^2)+(t^2-t^3)(2-t^3)
\]

gives:

| \(T\) | Exact \(M\) |
|---|---:|
| \(000\) | \(4\) |
| \(100\) | \(1+2=3\) |
| \(110\) | \(1+2=3\) |
| \(200\) | \(4\) |
| \(210\) | \(1+2=3\) |
| \(220\) | \(4\) |

Therefore

\[
\min_{\widetilde t=0}M=3,
\]

achieved by

\[
(1,0,0),\qquad(1,1,0),\qquad(2,1,0).
\]

Every terminal chart already contains \(100[3]\), so its chartwise minimum is also \(3\). The \(M=1\) profiles \(111,211,221\) have \(\widetilde t=1\) and do not enter the candidate. No emitted undershoot \(M<3\) exists.

## Q_C

For the wrong choice \(B=(2,1,1)\), Case 1(1) produces

\[
B'=(2,1,0),\qquad M(B')=1+1(2-0)=3,
\]

while \(A=(1,1,1)\) remains. Componentwise:

\[
(2,1,0)\nleq(1,1,1)
\quad\text{because }2\nleq1,
\]

and

\[
(1,1,1)\nleq(2,1,0)
\quad\text{because }1\nleq0.
\]

Thus \(B'\) and \(A\) are incomparable, immediately violating total comparability.

For the correct choice \(A=(1,1,1)\), mutation gives

\[
A'=(1,1,0),\qquad M(A')=1+1(2-0)=3,
\]

while \(B=(2,1,1)\) remains. Here

\[
(1,1,0)\leq(2,1,1)
\]

because

\[
1\leq2,\qquad1\leq1,\qquad0\leq1.
\]

Hence comparability is preserved.

Numerically, both choices emit an \(M=3\) divisor, and mechanical continuation produces no \(M<3\). Structurally, however, the wrong choice invalidates the invariant used to order the monomial factors and justify the divisibility chain. Any continuation after that point is no longer a valid execution of the stated principalization construction, even if its formal candidate minimum remains \(3\).

the tie-break protects the comparability invariant / valid principalization (coverage), with the minimum unchanged either way

MOST LIKELY WRONG (Q_A): Pointwise coverage is inferred from the meaning of “charts”; the coordinate maps and orientation/pivot subcharts were not supplied.  
MOST LIKELY WRONG (Q_B): Completeness of the six-profile list depends on the inferred \(S=1\to2\) boot and divisor-persistence convention; the displayed arithmetic itself is exact.  
MOST LIKELY WRONG (Q_C): Incomparability certainly breaks the stated invariant, but identifying that immediately with an actual coverage failure—rather than loss of the coverage proof—uses the construction’s asserted invariant-to-principalization link.