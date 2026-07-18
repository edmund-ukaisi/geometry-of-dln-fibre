Reading used: “componentwise-minimum” means \(f\le T\) for every \(T\in E\); a terminal \(J\)-advance moves to \(S+1\) and resets \(J=0\).

## Q1 — mutation (1a)

The uniform structural reason is **active-tail constancy**:

\[
(\mathrm{AT}_S)\qquad
t^S=t^{S+1}=\cdots=t^L=\widetilde T
\quad\text{for every carried }T.
\]

Thus the least occupied level \(\ell\) separates every \(g\le f\) into only two possibilities: either \(\widetilde g\le J\), in which case its entire active tail is already at most \(J\), or \(\widetilde g=\ell\), in which case minimality of \(f\) forces \(g=f\). This alignment between levels and constant active tails is the one uniform reason the mutation works.

Let \(h=\operatorname{setTail}(f,S,J)\). Since every coordinate of \(f\) is at least \(\ell>J\), we have \(h\le f\).

For any carried \(g\):

- If \(f\le g\), then \(h\le f\le g\).
- Suppose \(g\le f\). Put \(r=\widetilde g\). Then \(r\le\ell\). By the choice of \(\ell\), no occupied level lies strictly between \(J\) and \(\ell\), so either:
  - \(r\le J\). For \(i<S\), \(g^i\le f^i=h^i\); for \(i\ge S\), \((\mathrm{AT}_S)\) gives \(g^i=r\le J=h^i\). Hence \(g\le h\).
  - \(r=\ell\). Then \(g\in E\). Since \(f\) is the minimum of \(E\), \(f\le g\); combined with \(g\le f\), this gives \(g=f\), hence \(h\le g\).

Therefore replacing \(f\) by \(h\) preserves total comparability.

PROVED uniform in L

## Q2 — appended divisors

For (1b), the appended divisor is the same \(h\) considered above. The preceding proof compares \(h\) with every old divisor; in particular \(h\le f\), while \(f\) remains present. Thus appending \(h\) preserves the chain.

PROVED uniform in L

For Case 2, the claim is false even with the running-min head.

Take

\[
L=3,\qquad
(M^{(1)},M^{(2)},M^{(3)},M^{(4)})=(2,2,1,1),
\]

so

\[
M(2)=2,\qquad M(3)=M(4)=1.
\]

After layer-1 initialization,

\[
C_0=\{(0,0,0),(1,1,1)\}.
\]

At \((S,J)=(2,0)\), the eligible level is \(\ell=1\). Apply (1b) to \(f=(1,1,1)\), appending

\[
\operatorname{setTail}(f,2,0)=(1,0,0).
\]

Since \(M(3)=1\), this advances to \((3,0)\), carrying the chain

\[
(0,0,0)<(1,0,0)<(1,1,1).
\]

At \((3,0)\), the Case-1 search interval is

\[
[1,M(3)-1]=[1,0],
\]

so Case 2 applies. Its running-min divisor is

\[
c=(M(2),M(3),0)=(2,1,0).
\]

It is incomparable with \(T=(1,1,1)\): \(T\nleq c\) because \(1>0\) in coordinate \(3\), while \(c\nleq T\) because \(2>1\) in coordinate \(1\).

This has minimal depth. For \(L=1\), componentwise order is total. For \(L=2\), at layer \(2\) every reachable first coordinate is at most \(M(2)\); the Case-2 level gap then puts every divisor either below \((M(2),J)\) or above it. The displayed widths are the smallest positive widths producing the necessary strict drop \(M(2)>M(3)\).

REFUTED at \(L=3\), widths \((2,2,1,1)\), state \((S,J)=(3,0)\)

## Q3 — auxiliary invariants

The only auxiliary invariant consumed by the proofs of (1a) and (1b) is \((\mathrm{AT}_S)\).

- Initialization: every \((r,\ldots,r)\) has constant active tail equal to its minimum.
- (1a)/(1b): the new divisor has tail constantly \(J\), while its retained head is at least \(\ell>J\).
- Case 2: \(M(i+1)\ge M(S)>J\) for \(i<S\), so the new divisor again has minimum \(J\) and constant active tail.
- Layer advance: constancy from coordinate \(S\) onward implies constancy from coordinate \(S+1\) onward.

Weak decrease is also maintained—new Case-1 divisors join a weakly decreasing prefix to a smaller constant tail, while Case-2 heads are running minima—but it is not needed for Q1 or (1b).

MOST LIKELY WRONG 1: The counterexample uses the inferred reading that terminal (1b) advances immediately to the next layer.
MOST LIKELY WRONG 2: “Componentwise-minimum” is read as a least member of \(E\), not merely coordinatewise minima attained separately.
MOST LIKELY WRONG 3: Any unstated chooser restriction forbidding the exhibited (1b) would invalidate reachability, though it is absent from the supplied definitions.