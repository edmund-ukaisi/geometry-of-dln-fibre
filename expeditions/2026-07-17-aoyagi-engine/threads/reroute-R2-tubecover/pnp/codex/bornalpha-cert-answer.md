Verdict: (a) passes locally, (b) passes strongly, (c) passes canonically but is not proved for every leaf from the supplied facts.

### (A) KILL-CONDITION (a)

- [FACT from brief] For all six occurring shapes, \(M_{00}=E\) exactly and \(M_{00}/E=1\). It is the unique residual nonzero at the center.
- [INFERENCE] Thus every listed shape has a single-entry pivot survivor. It is not hidden in the \(\Delta\)-block and carries no \(\alpha\).
- [INFERENCE] Fact 4 suffices for this local shape-level conclusion. A global per-leaf conclusion additionally requires that later blow-ups do not pull back \(E\) through another exceptional coordinate.

### (B) KILL-CONDITION (b)

- [FACT from brief] The survivor residual is the constant \(1\).
- [INFERENCE] Its \(1/2\)-unit radius is unlimited: every radius contained in the chart domain works.
- [INFERENCE] The sandwich holds on the whole domain where the stated normal form is valid:
  \[
  K\circ g_c=(\mathrm{monomial}_c)^2\left(1+\sum_{i\ne i_0}\mathrm{resid}_i^2\right)
  \ge (\mathrm{monomial}_c)^2.
  \]
  Hence one may take \(\mathrm{cst}_c=1\). The weaker \(1/2\)-argument gives \(1/4\).

### (C) KILL-CONDITION (c)

- [FACT from brief] Canonically, \(\mathrm{monomial}=c_{11}E\). Therefore the binding divisors are \(c_{11}\) and \(E\), each with mono-exp \(1\); \(\alpha\) has mono-exp \(0\) and is nonbinding.
- [INFERENCE] The canonical divisor minimum is
  \[
  \min\!\left\{\frac{8+1}{1},\frac{7+1}{1}\right\}=\min\{9,8\}=8.
  \]
  Thus the canonical chart passes.
- [INFERENCE] Locally, Fact 4 likewise prevents that block’s born-\(\alpha\) from binding: the exact pivot is \(E\), not \(E\alpha\).
- [INFERENCE] Facts 4–6 do not determine whether every later exceptional divisor remains absent from the final pullback of \(c_{11}E\). That requires per-leaf composite pullback orders.
- [INFERENCE] “Higher mono-exp” is not protective: it enlarges the denominator. A binding divisor with mono-exp \(m\) needs total Jacobian order at least \(8m-1\).
- [INFERENCE] Center size alone is insufficient because it gives only the newly contributed Jacobian order, not the total order after composition. For example, a bare size-\(4\) contribution would give \((3+1)/m=4/m<8\) whenever it binds.
- [INFERENCE] The missing certificate is therefore: every deeper divisor has mono-exp \(0\), or an explicit per-divisor proof that \((\operatorname{jac\_exp}+1)/\operatorname{mono\_exp}\ge8\).

### (D) Biggest risk

- [INFERENCE] The principal risk is confusing an exhaustive census of local block shapes with an exhaustive certificate for composite resolution leaves. One must prove survivor persistence, divisor orders, normal crossings, and the up-to-null chart cover after every rerouting/permutation.
- [FACT from brief] Permutation invariance of codimension and center sizes does not itself prove cover completeness or composite divisor orders.
- [SPECULATION] A missed routing history in which a later center contains \(E\) could make a deeper divisor binding; nothing stated rules that out universally.