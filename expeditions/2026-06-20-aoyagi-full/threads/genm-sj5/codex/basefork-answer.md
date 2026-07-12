### Q1 — DecoratedBaseHyp is false [DERIVED]

**(a) Threshold counterexample.** Take \(d=1\), one residual \(res\equiv1\), \(\mathrm{jac}=0\), and support exponent \(N\). Then
\[
\int_0^\varepsilon (u^{2N})^{-c'}\,du
=\int_0^\varepsilon u^{-2Nc'}\,du,
\]
which diverges when \(2Nc'\ge1\). Since `pSimultaneous` is automatic for one support row, \(N\) can be arbitrarily large while `adm` holds. Thus the monomial threshold can lie strictly below \(\frac12\minAdm M\).

**(b) Coupled-residual counterexample.** Because `coeff` is unconstrained, all residuals may vanish on a positive-measure subset—or identically. There `decLoss = 0`, so `decLoss⁻ᶜ' = ∞` for \(c'>0\), and the integral diverges.

Precisely: one residual vanishing is insufficient if another summand remains nonzero; what matters is the common zero set of the summed residual loss.

Also, “zero set is null” is not itself enough: \(res(z)=z^N\) has a null zero set but can still have a divergent negative moment. The needed condition is quantitative integrability, or—after all vanishing has been extracted into monomials—a residual unit bounded away from zero.

### Q2 — Choose A [INFERRED]

For the stated uniform theorem
\[
\forall D,\ \mathrm{adm}(D)\to\mathrm{DecoratedBoxThresholdFinite}(D),
\]
ordinary arity induction necessarily reaches a width-two base with arbitrary admissible \(d\ge1\) decorations. Those decorations are not known merely from their type to have been produced by a faithful peel. Therefore the base must receive the resolution invariants through `adm` or an equivalent indexed certificate.

So **A is sound, faithful, and least structurally risky**. The #3↔#5 coupling is intrinsic to this uniform decorated descent: the carried decoration is the step’s resolution output, and terminal integrability depends on properties of that output.

A version of B is possible only after changing the induction theorem:

- decorated recursion is stated only for widths at least three;
- the final width-three step proves integrability of its constructed width-two terminal directly;
- raw decorated width-two inputs are excluded.

That does not collapse to plain IH—the higher recursive calls remain decorated—but it no longer proves the original uniform decorated theorem and requires a shifted induction boundary. It relocates the coupling into the final-step postcondition rather than eliminating it.

### Q3 — Arity alone does not force terminal form [DERIVED]

Reaching a single-matrix chain removes further product complexity, but it does not constrain arbitrary accumulated `supp`, `jac`, or `coeff`. Under the current `adm`, a partially resolved or degenerate decoration can reach width two.

A width-two carried decoration is terminal-form only if the preceding resolution has a proved postcondition saying that:

1. all exceptional vanishing has been extracted into the \(u\)-monomials;
2. the Jacobian-weighted monomial threshold is at least \(\frac12\minAdm M\);
3. the remaining free-block residual is quantitatively integrable—preferably a bounded-away-from-zero unit after the smooth/Morse coordinates.

Single-matrix smoothness supplies the final coordinate argument; it does not retroactively make an arbitrary carrier faithful.

The cleanest addition for A is one bundled predicate such as `FaithfulSJAt D (½ * minAdm M)`, containing the change-of-variables faithfulness, threshold bound, and terminal residual-unit/negative-moment certificate. The step preserves or produces it; the base consumes it.

This is **labour, not a wall**: the mathematical route is sound, but the missing resolution invariant must become explicit in the Lean architecture.