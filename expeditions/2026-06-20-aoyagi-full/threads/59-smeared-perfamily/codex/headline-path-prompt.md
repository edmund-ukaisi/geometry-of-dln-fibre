<task>
Lean4+Mathlib. I have BANKED (axiom-clean) the L=2 boundary-smeared RATE: `routeMCore_phiL2 :
routeMCore M (phiL2 …) = z²·∑ᵢⱼ(P₁·H̄)ᵢⱼ²` where phiL2 = paramsEquivFlat ∘ chartL2Params, the deepest
factor row-split into top-r (z·H̄−Λ₀·Sbot) + bottom-s (Sbot), off the shear pole P₁·Λ₀=P₂.

I want the L=2 HEADLINE `∫_{cubeBox N ε} |routeMCore M x|^{−c'} = ⊤`. Two routes:

ROUTE-CONTRACT: a BANKED `routeMCore_box_diverges_smearedContract M ψ R D p h (hmp: MP ψ)(hemb: MeasEmb ψ)
c' ε S (hSmeas)(hSpre: S ⊆ (ψ∘R)⁻¹(cubeBox))(hRderiv)(hRinj)(hRdet: |det D u|=|u p|^h)(hSdiv: ∫_S |u p|^h
· |routeMCore M (ψ(R u))|^{−c'} = ⊤)`. Needs φ_sm = ψ∘R with R the radial pivotBlowupOn (sole Jacobian
|u p|^{minAdm−1}) and ψ the shear+reshape (MP+embedding). My phiL2 is NOT yet in ψ∘R form (it has H̄ as
free angulars, not radial-blown z·h). I have BANKED measurePreserving_shearM (the Λ₀-shear MP, any widths)
and generic pivotBlowupOn facts (det/injOn/fderiv).

ROUTE-NODECHART: a BANKED `routeMCore_box_diverges_of_nodeChart M (W : NodeAchieverChart M) …` consuming a
full bundle whose hard field is `cov` (a RATIONAL change-of-variables, the genuinely hard piece).

The (2,3,1) single instance does ROUTE-CONTRACT in 1125 lines (explicit Fin 9, dimension-specific Λ₀-bound
subBox231_lam_bound, z-axis-peel divergence subBox231_diverges). I must do it over OPAQUE L=2 widths.

The 2 remaining contract fields: A (containment smearedSubBox ⊆ (ψ∘R)⁻¹(cubeBox) — needs every chart entry
small on the box, incl a Λ₀-bound over opaque widths) and B (hSdiv — the z-axis-peel + monomial atom, given
my rate).

<output_contract>
1. ROUTE-CONTRACT vs ROUTE-NODECHART for the L=2 OPAQUE-width headline: which is less total work given I
   have the rate + measurePreserving_shearM + generic pivotBlowupOn? One paragraph, pick one.
2. The GAP between my phiL2 (H̄ free) and the contract's φ=ψ∘R (R radial): is it cheaper to (i) REDEFINE the
   chart as ψ∘R from the start (R = pivotBlowupOn on the r·c top coords, ψ = shear∘reshape) and re-derive
   the rate, or (ii) keep phiL2 and PROVE phiL2 = ψ∘R? Which, and the one key obstacle.
3. For field B (hSdiv): is there a clean M-AGNOSTIC reduction "rate F=z²·U + U-bounded-positive + 1−2c'≤−1
   ⟹ ∫_S |z|^h·F^{−c'}=⊤" that I can state+prove ONCE (the z-axis peel abstracted over the source box),
   reusable for all opaque widths? Sketch its statement (the source box = z∈(0,δ) × rest-coords small).
4. If the FULL L=2 headline is >~400 lines of opaque-width analysis (likely), the cheapest HONEST CEILING:
   what ONE interface theorem (hypotheses = the chart's MP/embedding/det/containment + my rate) yields the
   headline with everything else proven — so the gap is named, not sorry'd?
</output_contract>

<grounding_rules>
Flag inference vs fact; you lack my files. Prefer the path minimising opaque-Fin casts + measure-theory
re-derivation. If a Mathlib/measure lemma is uncertain, say "verify".
</grounding_rules>
