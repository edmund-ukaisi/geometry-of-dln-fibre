<task>
Adjudicate the proof structure of a Lean preservation lemma under a redesigned invariant. Re-derive; be concrete.

SETTING (ℝ^D polynomial world, D = flatDim d). A resolution fold at a tree node p with state (S = layer, J = cleared).
Definitions (baked):
- layerCoords ℓ := flat coords whose decoded matrix-layer = ℓ.
- supportAt S J := if J=0 then layerCoords S else if S+1<N then layerCoords (S+1) else ∅.  (the DESCENDING geometric support)
- DeeperMultilinear c Dp V := ∃ h, (∀ d∈Dp, IgnoresCoords (h d) Dpᶜ V) ∧ (∀ u∈V, c u = ∑ d∈Dp, u d · h d u).  (c is Dp-linear; sub-coeffs read only Dp)
- Deg1SupportedSlot resid j S Dp V := ∃ c, (∀i ContinuousOn (c i) V) ∧ (∀u∈V, resid j u = ∑_{i∈S} c i u·u i) ∧ (∀i DeeperMultilinear (c i) Dp V).
- FoldStepInvAt C p := (∃q, StepInv coreGen (foldG p)(foldB p)(foldResid p) q univ) ∧ (∀j, Deg1SupportedSlot (foldResid p) j C Cᶜ univ),  with C = supportAt(p.state).

The step (case-2, INTERIOR edge, guard S+1 < N via nextState): σ = blockBlowupMap ed.center ed.pivot ∘ shear (shear keeps pivot).
 - ed.center (LEDGER blow-up locus) = the layer-S residual sub-block: {flat coord q : layer(q)=S, row(q)≥J, J≤col(q)<widthMinUpto(S)}. pivot ∈ ed.center.
 - foldB(child) u = (u pivot)^δ · foldB p(σu), δ = [J=0].
 - foldResid(child) j u = (δ=1) foldResid p j (quotMap u); (δ=0) foldResid p j (σu).  quotMap u k = (if k=pivot then 1 else (shear u) k).
 - crux (proved for the OLD invariant, Deg1 support on ed.center): foldResid p j(σu) = u_pivot · foldResid p j(quotMap u).

MY STRUCTURAL FINDING (verify): the δ discriminator ALIGNS with the support layer.
 - J=0 ⟹ δ=1 ⟹ supportAt(parent) = layerCoords(S) = the blow-up layer. Residual supported on layer S; the blow-up at pivot∈layer-S makes layer-S center coords gain u_pivot ⟹ residual gains u_pivot, balanced by foldB's u_pivot (strict transform).
 - J≥1 ⟹ δ=0 ⟹ supportAt(parent) = layerCoords(S+1) = the DEEPER layer, DISJOINT from ed.center (layer S). So the residual's support coords are SPECTATORS of the layer-S blow-up (fixed, no u_pivot); foldB no u_pivot ⟹ pure pullback, orders balance.

QUESTIONS:
1. Is the divisibility CRUX (foldResid p j(σu) = u_pivot·foldResid p j(quotMap u)) still needed / true at δ=1 under the NEW invariant? Concern: supportAt(parent)=layerCoords(S) may STRICTLY contain ed.center (layer-S coords with col ≥ widthMinUpto — already-cleared columns — are in layerCoords(S) but NOT in ed.center). Such support coords are spectators of the blow-up (no u_pivot), so the residual would NOT uniformly gain u_pivot ⟹ crux FALSE for those monomials? OR does the invariant/construction guarantee supportAt(parent) ⊆ ed.center at J=0 (e.g. widthMinUpto(S) = full width d_S so layerCoords(S) = the full residual block)? Which is it, and what fact closes it?
2. Conjunct B (the re-factoring): does the child residual re-factor as Deg1SupportedSlot on supportAt(child) with DeeperMultilinear coefficients over supportAt(child)ᶜ? Give the child coefficients explicitly (δ=1 and δ=0), and confirm DeeperMultilinear self-propagates (the elder's ruling).
3. Does a divisibility engine proved for the OLD invariant (Deg1SupportedOn ed.center, coefficients IgnoresCoords ed.center) TRANSFER to the new invariant (support supportAt, coefficients read supportAtᶜ)? Or is the crux genuinely different (coefficients no longer ignore ed.center)?
</task>
<output_contract>
Answer 1,2,3 in order. For (1) give the DECIDING fact (a ⊆ relation or a construction identity) or flag it as an open dependency. For (3) YES/NO + why. Under ~500 words. Flag INFER vs KNOW; you may not have the construction's widthMinUpto facts — say so.
</output_contract>
<grounding_rules>Reason from the given defs; name any construction fact you assume (widthMinUpto, canonCenter, state-advance).</grounding_rules>
