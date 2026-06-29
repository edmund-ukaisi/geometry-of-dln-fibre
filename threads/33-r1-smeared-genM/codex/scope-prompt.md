<task>
Lean 4 + Mathlib formalisation. I must discharge the BOUNDARY-SMEARED branch of an
∀M (L=2) achiever box-divergence "spine". The spine consumes a hypothesis

  hSmeared : ∀ _ : 2 ≤ L, BoundarySmeared M → BoxDiverges M c' ε

where `BoxDiverges M c' ε := ∫⁻ x in cubeBox (routeMAmbient M) ε, ENNReal.ofReal (|routeMCore M x| ^ (-(c':ℝ))) = ⊤`,
and `M : Fin (L+1) → ℕ`, `BoundarySmeared M` means `deepRank M < deepRows M` (the deepest factor's
compressed rank is strictly below its row count).

ALREADY BANKED, SORRY-FREE (the M-agnostic infrastructure):
1. `routeMCore_box_diverges_smearedL2` — the L=2 conditioned-box assembly. It is M-agnostic but takes a
   LONG list of PER-FAMILY chart inputs: ψ R D (the chart maps), a pivot p, a conditioned per-axis box,
   a unit Uy, plus proofs that ψ is measure-preserving + a measurable embedding, R is a radial blow-up
   with fderiv D / injective / |det D u| = |u p|^h, the conditioned box maps into (ψ∘R)⁻¹(cubeBox ε)
   (field A), the PEELED RATE `routeMCore M (ψ(R(insertNth p z y))) = z²·Uy y` on the box, Uy>0 there,
   and the exponent `(h:ℝ) − 2c' ≤ −1`.
2. `routeMCore_phiL2` — for ARBITRARY widths M : Fin 3 → ℕ with r+s = M 1, the rate
   `routeMCore M (phiL2 M hrs A0 z Hbar Sbot Λ₀) = z²·∑ᵢⱼ((P₁·H̄)ᵢⱼ)²` is PROVEN, where φL2 is the flat
   chart = paramsEquivFlat ∘ chartL2Params, P₁ = A0∘(top r cols), off the shear pole P₁·Λ₀ = P₂.
3. Generic bricks: `pivotBlowupOn` (radial blow-up, fderiv/injOn/det = |x p|^(card−1) all generic),
   `measurePreserving_coreShear_measurable` (the rational shear is MP for any widths a,b,c),
   `measurePreserving_paramsPack_of_flatIdxEquiv` (flat→Params reshape MP given a Fin N ≃ FlatIdx M equiv).
4. Two WORKED instances fire `smearedL2` end-to-end, sorry-free: (2,3,1) [Fin 9] and (1,3,2) [Fin 9],
   each ~1000 lines of case-specific machinery (an explicit `Fin N ≃ FlatIdx M` slot equiv built by
   `decide`, an explicit shear-matrix, the exact coordinate partition).

THE GAP: to discharge `hSmeared` ∀M at L=2, I'd need to construct ψ/R/box/Uy/rate for an ARBITRARY
smeared M : Fin 3 → ℕ (arbitrary widths M0,M1,M2 with deepRank < M1). The resisting parts: the
`Fin (routeMAmbient M) ≃ FlatIdx M` slot equiv (the worked ones use `decide`, impossible at opaque
widths), and the shear's exact coordinate layout (where Λ₀/S_bot/H̄ live in the flat vector).

QUESTION: I have ~one bounded module of budget. Two candidate deliverables:

(A) FULL ∀M discharge: build the uniform ψ/R/box for arbitrary M : Fin 3 → ℕ from the generic bricks,
    proving every smearedL2 input uniformly. Then `hSmeared` is closed for L=2 with NO per-family hole.

(B) A `SmearedAchieverChart M` STRUCTURE (analogous to a banked `NodeAchieverChart M`) bundling exactly
    the per-family geometric inputs smearedL2 needs (ψ/R/D/p/box/Uy + their MP/embedding/det/containment/
    peeled-rate/U-pos fields), and `routeMCore_box_diverges_of_smearedChart M (W : SmearedAchieverChart M)`
    proven M-AGNOSTICALLY from it (a thin repackaging of smearedL2). This reduces `hSmeared` to "construct
    one SmearedAchieverChart M" — leaving the chart CONSTRUCTION (the opaque-width slot equiv + shear
    layout) as the named residual, but the ASSEMBLY fully closed and the (2,3,1) instance witnessing
    non-vacuity.
</task>

<output_contract>
1. VERDICT: is (A) realistically a SINGLE bounded module (say ≤ 600 LoC of NEW Lean on top of the banked
   infra), or is the opaque-width slot-equiv + shear-layout construction itself a multi-module build?
   Give the single most likely blocker for (A) and estimate its size.
2. If (A) is NOT a single bounded module, is (B) the right bedrock deliverable for one module — i.e. does
   a `SmearedAchieverChart M` + M-agnostic `of_smearedChart` repackaging genuinely advance the leg
   (vs the existing `smearedL2` which already takes the same inputs as loose hypotheses)? Or is the
   repackaging vacuous given smearedL2 already exists?
3. The single sharpest risk in the VERIFY-FIRST claim that "the rational-pole transport interface
   suffices ∀M" — i.e. is there any width regime (e.g. M0 < r, so P₁ has no invertible r×r minor, or
   s = 0 so no shear, or r = 0) where the smeared chart DEGENERATES and the interface does NOT close?
   Name the regime and whether it's inside or outside `BoundarySmeared`.
Be concise; rank by what most changes my plan. Flag inference vs. fact.
</output_contract>

<grounding_rules>
You do not have the repo. Reason from the structures described. Mark any claim that depends on
Mathlib lemma availability as INFERENCE. Do not invent lemma names; reason about the mathematical
shape and the proof-engineering scope.
</grounding_rules>
