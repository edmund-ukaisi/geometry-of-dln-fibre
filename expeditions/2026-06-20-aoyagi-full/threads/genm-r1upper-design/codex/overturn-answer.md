1. **Agree:** the low-rank-`B` power loss blocks an opaque black-box tail-chain reduction; this is **bounded**, not a new obstruction, provided the build uses Aoyagi’s joint `(S,J)` charge bookkeeping.

2. The lighter escape is not a true escape. You can present the proof as “generic `B` first, low-rank `B` separately,” but the low-rank branch must remember the inherited deficit
`δ = (a - (M1-t) rank(B))_+`.
That deficit changes the effective exponent from roughly `c' - a/2` to `c' - (M1-t)rank(B)/2` on the shared tail. A plain tail theorem has no parameter for that inherited charge, so it cannot certify the branch. A rank-stratified sub-induction would need to carry exactly this extra charge into deeper exceptional variables. That is Aoyagi’s `D_J`/`diag(b)` mechanism under another name.

Concrete caveat: “the power loss is exactly the deeper boundary’s rank drop” is right as a proof heuristic, but not literally a single divisor statement until the rank-`B` stratum is resolved into layer-wise rank-drop divisors. The formal statement should be: the multiplier creates an inherited charge supported on deeper product-rank strata, and the double induction proves that this charge is paid by their Jacobian/codimension surplus.

3. Minimal Lean build pieces, in dependency order:

1. **Local Comparability / Units**  
   Frobenius product losses, entry ideals, bounded analytic changes of variables, and finite chart covers preserve local `L¹` integrability.  
   Type: plumbing.

2. **Pivot-Schur Chart Lemma**  
   On each rank/corank chart, reduce the current layer to the block form giving `P ≍ P_tail + Γ`-part, with correct block dimensions and bounded Jacobian.  
   Type: algebraic plumbing.

3. **Boundary Blow-Up / Peel Lemma**  
   For `Γ = zV`, prove the Jacobian `z^{a-1}` and the per-step mixed integrand
   `P_tail^{-(c'-a/2)} P_full^{-a/2}` up to harmless constants/logs.  
   Type: local analytic core.

4. **`(S,J)` Normal-Form Invariant**  
   Formalize the chart invariant
   `diag(b) · [E_J | D_J] · ∏ C^{(s)}`: after each within-layer rank-drop step, the transformed product has the promised diagonal exceptional factors and residual deeper product.  
   Type: main structural plumbing.

5. **Jacobian / Charge Update Lemma**  
   Each `(S,J) -> (S,J+1)` or layer transition updates exceptional exponents by the stated codimension/rank-loss amount, matching the accumulated coupling charge.  
   Type: mechanical but load-bearing for correctness.

6. **Charge Budget Inequality**  
   The accumulated inherited charges on every exceptional divisor are bounded by the admissible codimension budget, equivalently the `minAdm` recursion/subordination inequality.  
   Type: load-bearing combinatorial core.

7. **Monomial Integrability Assembly**  
   Once losses and Jacobians are monomialized, apply the real box criterion `∫ ∏ |u_i|^{α_i} < ∞ iff α_i > -1`; logs are harmless under strict `c' < ½ minAdm`; finite charts assemble the global result.  
   Type: load-bearing analytic endpoint.

So the build decision should be: do the joint `(S,J)` formalisation. A “separate low-rank induction” is viable only if it is a weighted/rank-stratified induction carrying inherited charges, which is essentially the same proof obligation.