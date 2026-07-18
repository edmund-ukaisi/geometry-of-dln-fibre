Let \(\lambda(T)=\widetilde T\). By WeakDec and FlatTail,
\[
\lambda(T)=T^S,\qquad T^i=\lambda(T)\quad(i\ge S).
\]

### Q1

[PROVE] Introduce the head-only invariant
\[
\operatorname{LiveHeadDom}(S,C):
\quad
\lambda(a)<\lambda(b)<M(S)
\Longrightarrow
a^i\le b^i\quad(i<S).
\]

At a case-1 node,
\[
\lambda(y)\le J<\ell=\lambda(x)<M(S).
\]
Applying LiveHeadDom with \(a=y,b=x\) gives \(y^i\le x^i\) for every head coordinate \(i<S\). FlatTail gives
\[
y^i=\lambda(y)\le J<\ell=x^i\qquad(i\ge S).
\]
Hence \(y\le x\).

The stated invariants alone do not suffice. For \(L=2\), all widths \(2\), and the abstract state
\[
(S,J)=(2,0),\qquad C=\{x=(1,1),\,y=(2,0)\},
\]
WeakDec, FlatTail, WidthBound, and run-gap all hold; \(\ell=1\), but \(x^1<y^1\). This state is not reachable because it violates LiveHeadDom.

### Q2: minimal auxiliary invariant and maintenance

[PROVE] The minimal non-circular head hypothesis used is **LiveHeadDom**. It imposes:

- no same-level comparability;
- no condition when the higher divisor is stranded at level \(\ge M(S)\);
- only the head inequalities not already supplied by FlatTail.

It is maintained as follows. Write \(h=\operatorname{setTail}(f,S,J)\), where \(f\) is the eligible **least** element at level \(\ell\). Thus \(\lambda(h)=J\) and \(h^i=f^i\) for \(i<S\).

1. **Layer-1 seed.** The constant vectors \((r,\ldots,r)\) are ordered by their levels.

2. **Case 1, replace or append \(h\).** Old pairs are unchanged.

   - If \(\lambda(a)<J=\lambda(h)\), the old invariant applied to \(a,f\) gives \(a^i\le f^i=h^i\).
   - If \(J=\lambda(h)<\lambda(b)<M(S)\), least occupancy/run-gap gives \(\lambda(b)\ge\ell\). If \(\lambda(b)=\ell\), leastness of \(f\) gives \(f\le b\). If \(\lambda(b)>\ell\), the old invariant gives \(f^i\le b^i\). Therefore \(h^i\le b^i\).

3. **Case 2.** The appended divisor has
   \[
   c^i=M(i+1)\ (i<S),\qquad c^i=J\ (i\ge S).
   \]
   If \(\lambda(a)<J=\lambda(c)\), WidthBound gives \(a^i\le M(i+1)=c^i\) on the head. Conversely, Case 2 means there is no carried \(b\) with \(J<\lambda(b)<M(S)\), so no new obligation has \(c\) as its lower member.

4. **Advance \(J\).** The invariant does not mention \(J\).

5. **Advance \(S\to S+1\).** Since \(M(S+1)\le M(S)\), every new live pair was already live. The new head coordinate \(S\) is ordered because \(a^S=\lambda(a)<\lambda(b)=b^S\).

The bottleneck pair \((2,1,0)\), \((1,1,1)\) is harmless: at that state the higher level is \(1=M(S)\), not \(<M(S)\), so it is stranded and LiveHeadDom intentionally says nothing about it.

### Q3

[PROVE] STEP1 holds for **every** divisor \(x\) at level \(\ell\), not merely the chosen minimum. The application of LiveHeadDom never mentions the chosen \(f\).

The least choice is used only to preserve LiveHeadDom after a Case-1 tail-write, when the new level-\(J\) divisor must lie below every remaining level-\(\ell\) divisor.

PROVED uniform in L

MOST LIKELY WRONG 1 — INFER: “componentwise-minimum” is read as a least element \(f\le z\) for every eligible \(z\), not merely a minimal element.  
MOST LIKELY WRONG 2 — INFER: Case-1 children inherit \(f\)’s head exactly, and Case 2 uses the running-min head stated above.  
MOST LIKELY WRONG 3 — PROVE/SCOPE: “minimal” means the weakest head-only, \(J\)-independent pairwise invariant used here; absolute logical minimality is not claimed.