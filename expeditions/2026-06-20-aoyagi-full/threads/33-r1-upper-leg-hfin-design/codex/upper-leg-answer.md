**Q1 Verdict: one direction suffices.**

For hfin, you only need the lower comparison

\[
\operatorname{frobSq}(R S)\ \ge c_0\,D
\]

equivalently \(D \le C\,\operatorname{frobSq}(RS)\).

Since \(c'>0\), this gives

\[
\operatorname{frobSq}(RS)^{-c'} \le c_0^{-c'}D^{-c'}.
\]

So finiteness of the model integral for \(D^{-c'}\) implies finiteness of the original one. The reverse inequality is useful for sharpness/divergence/value matching, but not for the hfin upper leg.

**Q2 Verdict: yes, the needed direction holds uniformly, even at corank \(\ge 2\).**

Let

\[
A=M_{11},\qquad C=M_{21},\qquad H=\operatorname{Sc},\qquad X=A P,\qquad Y=H Q.
\]

Then

\[
C P = C A^{-1} A P = F X,\qquad F:=C A^{-1}.
\]

So the comparison becomes the pure inequality

\[
\|X\|_F^2+\|F X+Y\|_F^2
\;\ge\;
c_0\bigl(\|X\|_F^2+\|Y\|_F^2\bigr).
\]

**FACT derived:** on the complete-pivoting cell, \(|F_{ij}|\le 1\), hence

\[
\|F\|_{\mathrm{op}}\le \|F\|_F\le \sqrt{k(r-k)}=:L.
\]

Then

\[
(X,Y)=(X,FX+Y)+(0,-FX),
\]

so

\[
\sqrt{\|X\|^2+\|Y\|^2}
\le
\sqrt{\|X\|^2+\|FX+Y\|^2}+ \|FX\|
\le
(1+L)\sqrt{\|X\|^2+\|FX+Y\|^2}.
\]

Therefore

\[
\|X\|^2+\|FX+Y\|^2
\ge
(1+\sqrt{k(r-k)})^{-2}
\bigl(\|X\|^2+\|Y\|^2\bigr).
\]

So one valid uniform constant is

\[
c_0=(1+\sqrt{k(r-k)})^{-2}.
\]

Yes, the bottom block can cancel: \(FX+Y\) can be small while \(Y=HQ\) is large. But cancellation forces \(X=AP\) to be large as well, and the top term \(\|AP\|^2\) records exactly that cost. That is the mechanism preventing the ratio from going to zero.

A sharper spectral constant exists, but the above dimension-only constant is enough for hfin.

**Q3 Verdict: heaviest is (c), then (b), then (a).**

Ranking in Lean-formalisation cost:

1. **(c) depth-\(r\) Tonelli/Fubini cover plumbing + per-chart changes of variables**  
   This is the largest cost. It forces Lean to track restricted domains, finite covers, parameter-dependent triangular changes of variables, determinant-one Jacobians, measurability, ae facts, integrability/lintegral conversions, and repeated product-measure rearrangements. The math is standard; the formal API burden is the weight.

2. **(b) WellFounded-on-corank recStep assembly**  
   Architecturally serious, especially with dependent dimensions and nested pivot covers, but once the per-chart analytic lemma is clean, the well-founded recursion should mostly be packaging and induction discipline.

3. **(a) N2b uniform comparison**  
   This is not the bottleneck. It reduces to a bounded-linear-map shear inequality as above. The Schur algebra is finite-dimensional norm bookkeeping.

**Q4 Verdict: needs-design-then-build, not a research wall.**

The N2b hfin direction is mathematically solid and uniformly available. So the general upper leg looks buildable, but not yet “just grind it out” unless the recursive integrability certificate and measure/COV infrastructure are designed first.

The single thing most likely to make the optimistic read wrong is using only numeric threshold data in the recursive hfin proof. The threshold value being known is not the same as having a Lean-usable finiteness certificate through the recursive charts. At corank \(\ge 2\), divisor sharing matters; a light threshold-only recursor can lose exactly the structure needed to prove the upper integrability statement.