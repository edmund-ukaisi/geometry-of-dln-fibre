**S1.1**

A. **INSUFFICIENT.** Fact: the Lean statement allows arbitrary `[MeasureSpace M]`, not necessarily Lebesgue. Counterexample: on `ℝ` with active measure `|x| dx`, take `π x = x^3`, `E=∅`, `F y = y`, `φ=1`, `wstar=0`; left threshold is `2`, right threshold is `4/3`.  
Even for Lebesgue, the stated a.e. differentiability/injectivity is weaker than a usable change-of-variables theorem; missing hypotheses include C¹/local diffeo or area-formula assumptions, measurability/regularity of `F,φ,Dπ`, and control that `π(E)` is null.

B. **PASS ON PLACEMENT.** The Jacobian is on the source-side weight as `φ (π m) * |det Dπ m|`, which is the correct weighted pullback form. This avoids the known false unweighted `rlctAt (F ∘ π) = rlctAt F` trap.

C. **NOT VACUOUS.** There are many satisfying inputs: identity, linear isomorphisms, polynomial proper maps such as `x ↦ x^3` with `E=∅`. The equality is not trivially always true; the measure-density counterexample above makes it fail.

**S1.5**

D. **INSUFFICIENT / FALSE GENERALLY.** Counterexample on `X=Y=ℝ` with Lebesgue measure: let `N_k=2^(2^k)`, `A_n=N_{2n}`, `B_n=N_{2n+1}`; choose disjoint intervals `I_n,J_n→0` of lengths `e^{-A_n}`, `e^{-B_n}`, and set `F^2=e^{-A_n}` on `I_n`, `1` elsewhere, while `G^2=e^{-B_n}` on `J_n`, `1` elsewhere. Then `λ(F^2)=λ(G^2)=1`, but the joint double sum has terms `exp(-A_n-B_m+c min(A_n,B_m))`, finite for every fixed `c` because the scales alternate with huge gaps; hence `λ(F^2+G^2)=⊤`, not `2`.

E. **PRODUCT MEASURE: MOSTLY OK, BUT HYPOTHESES STILL MISSING.** Fact from local Mathlib source: the standard product `MeasureSpace (X × Y)` has `volume = volume.prod volume` by `rfl`. Inference: the printed theorem relies on that synthesized instance; it still lacks `[SFinite]`/local finiteness and, more importantly, analytic or regular sublevel-set hypotheses needed for Aoyagi-style additivity.

S1.1: **FLAG**.  
S1.5: **FLAG**.