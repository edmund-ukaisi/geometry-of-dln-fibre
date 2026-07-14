## VERDICT: TRUE

For every \(n\ge 4\), every waist \(M\) has a good reverse. In fact, the reverse satisfies the stronger strict inequality
\[
\operatorname{deepTailMin}(\operatorname{rev} M)<\operatorname{rev}(M)[1].
\]

Let \(R=\operatorname{rev}(M)\). Then
\[
R[1]=M[n-2]
\]
and
\[
\operatorname{deepTailMin}(R)
=\min_{0\le k\le n-3}M[k].
\]

When \(n\ge4\):

- \(1\in\{0,\ldots,n-3\}\), so
  \[
  \operatorname{deepTailMin}(R)\le M[1].
  \]
- \(n-2\in\{2,\ldots,n-1\}\), so WAIST\((M)\) implies
  \[
  M[1]<M[n-2].
  \]

Therefore
\[
\operatorname{deepTailMin}(R)
\le M[1]
<M[n-2]
=R[1],
\]
which proves GOOD\((R)\).

These two index-membership facts are the load-bearing points, and both require exactly \(n\ge4\).

### Danger families

**(a) Palindromic waists:** None exist for \(n\ge4\). Palindromicity gives \(M[n-2]=M[1]\), while WAIST would require
\[
M[1]<M[n-2]=M[1],
\]
a contradiction.

**(b) Waist in both directions:** None exist for \(n\ge4\). Original WAIST gives
\[
M[1]<M[n-2],
\]
whereas reverse WAIST would give
\[
M[n-2]<M[1],
\]
because \(R[n-2]=M[1]\) lies in the reverse deep tail.

**(c) Boundary cases:** At \(n=4\),
\[
\operatorname{deepTailMin}(R)=\min(M[0],M[1]),\qquad R[1]=M[2],
\]
so
\[
\min(M[0],M[1])\le M[1]<M[2].
\]
Thus \(n=4\) works exactly.

Ties elsewhere cause no problem. A tie between \(M[1]\) and a deep-tail entry is excluded by WAIST. If \(M[1]=1\), every original deep-tail entry must be at least \(2\); \(M[0]\) may still equal \(1\).

### Width \(3\)

The analogous statement is **false**. The smallest positive-integer counterexample—both componentwise-minimal and minimum-sum—is
\[
M=(2,1,2).
\]

It is its own reverse. Directly,
\[
\operatorname{deepTailMin}(M)=2,\qquad M[1]=1,
\]
so WAIST\((M)\) holds. But
\[
\operatorname{deepTailMin}(\operatorname{rev}M)=2\nleq1=\operatorname{rev}(M)[1],
\]
so the reverse is not good.

Thus \(n\ge4\) is the exact width threshold.

No upper bound on \(n\) or on any entry is needed. The proof is uniform over all widths \(n\ge4\) and all positive-integer entries.