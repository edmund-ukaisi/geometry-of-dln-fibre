<task>
I am formalising in Lean 4 + Mathlib the boundary-SMEARED achiever box-divergence for deep linear
networks (the R1-LOWER last piece). I have BANKED, sorry-free + axiom-clean, the genuinely-new
algebraic core (verified numerically first, decorrelated):

  (1) proj_cancel_of_factorsThrough: P₂=P₁·K ∧ det(P₁ᵀP₁)≠0 ⟹ P₁·((P₁ᵀP₁)⁻¹P₁ᵀP₂)=P₂  (any tall P₁)
  (2) front_factorsThrough_general: P=U·V ∧ det(Vρ)≠0 ⟹ ∃K, P₂=P₁·K  (col(P₂)⊆col(P₁), general r)
  (3) frontShear_cancel_general: composes (1)+(2): P₁·Λ₀=P₂ for any r≥1.

This is the rate's core: F = ‖P·A^{L−1}‖² = z²·‖P₁·H̄‖² = z²·U, via the telescoping
P·A^{L−1} = P₁(z H̄ − Λ₀ S_bot) + P₂ S_bot = z·P₁ H̄ (the (P₂−P₁Λ₀)·S_bot term cancels by (3)).

REMAINING to reach the headline `routeMCore_box_diverges_smeared M (deepRank M < deepRows M) …`:
  (a) a structural bridge: the smeared front product P=prodAux M A (L−1) factors through the width-r
      BOTTLENECK layer (validated 652/652) ⟹ supplies P=U·V (I have prodAux_split_exists giving the
      U·Y split) + det(Vρ)≠0 (P₁ full column rank off a pole).
  (b) the opaque-width chart phi_sm_M = (radial pivotBlowupOn = R) ∘ (the Λ₀-shear = ψ, MP, banked as
      measurePreserving_shearM) + the pack/reshape, over DEPENDENT-Fin opaque widths.
  (c) the rate routeMCore (phi_sm_M u) = (u_p)²·U over opaque widths (consumes (3) + the telescoping).
  (d) the rational `cov` change-of-variables (det |z|^{minAdm−1} off the {det P₁ᵀP₁=0} null pole).
  (e) the NodeAchieverChart instance + headline via routeMCore_box_diverges_of_nodeChart, OR via the
      banked contract routeMCore_box_diverges_smearedContract (φ=ψ∘R form, takes ψ MP-embedding + R
      radial + a weighted source-divergence hSdiv separately).

The (2,3,1) single instance is 1125 lines (explicit 2×2/3×1 matrices, NO opaque widths). The general
version over opaque dependent-Fin widths is flagged [HIGH] cast-risk (the chainA/GenBlk dependent-width
trap). I have a single tide. I want to maximise SOLID BEDROCK (sorry-free, axiom-clean, the right scope)
rather than race a spike.

Already banked + general (do not rebuild): measurePreserving_shearM (the Λ₀-shear MP, any widths),
measurable_lamEntry (Λ₀ entrywise measurable, any widths), smearedSubBox+measurableSet, the clean
lineage cleanPhi/cleanUbound/routeMCore_box_diverges_of_nodeChart, RouteMBoundaryCleanRate (the clean
rate, which proves routeMCore (cleanPhi u)=(u_p)²·U for ALL M via pure layer-scaling, NO shear — but
the clean DET needs deepRank=deepRows; smeared needs the shear so only the r rank-rows blow up).
</task>

<output_contract>
1. RANK the order to attempt (a)–(e) by VALUE-PER-RISK (which gives the most durable bedrock per unit
   cast-risk). One line each: what it delivers, the cast-risk, whether it stands alone if the rest walls.
2. The SINGLE highest-leverage abstraction to MINIMISE the opaque-Fin cast pain in (b)/(c) — e.g. should
   I state the rate as a GENERIC lemma over an abstract front-factorization (matrices + selectors, like
   my (2)) and only instantiate the dependent-Fin widths at the very end? Concretely what is that lemma's
   statement?
3. The cheapest HONEST CEILING if the full opaque-width chart is out of reach in one tide: what is the
   smallest named gap to isolate (a single `sorry` with a precise statement) so the rest is bedrock and
   the controller can dispatch the gap? Name the exact theorem to leave as the gap.
4. One TRAP to avoid (conceptual slop) specific to this build.
</output_contract>

<grounding_rules>
Flag inference vs. fact. You do not have the Lean files; reason from the structure I gave. If a claim
needs the actual Lean signatures, say so rather than guess.
</grounding_rules>
