<task>
Adjudicate, from first principles, whether a Lean theorem's conclusion is DERIVABLE from its
hypotheses, or whether it is UNDERIVABLE / FALSE-as-stated. Do NOT trust my argument; re-derive.

SETTING (all functions ℝ-valued on ℝ^D, D = flatDim; the ambient is a real polynomial world).
Fixed generator family `F = coreGen` : Fin M → (ℝ^D → ℝ) (M = d_N·d_0 > 0), each `F i` a polynomial.

Definitions:
- StepInv F g b resid q V  :=
    (∀ i j, ContinuousOn (q i j) V)
    ∧ (∀ i, (F i ∘ g) 0 = 0)                              -- "S3 deepest-point vanishing"
    ∧ (∀ u ∈ V, ∀ i, (F i ∘ g) u = ∑_j q i j u * (b u * resid j u))   -- divisibility by b
- IgnoresCoords c S V := ∀ w∈V, ∀ m∈S, ∀ t, c (update w m t) = c w   -- c reads only coords OUTSIDE S
- Deg1SupportedOn resid S V :=
    ∀ j, ∃ c : Fin D → (ℝ^D→ℝ),
      (∀ i, ContinuousOn (c i) V) ∧ (∀ u∈V, resid j u = ∑_{i∈S} c i u * u i) ∧ (∀ i, IgnoresCoords (c i) S V)

THE FOLD DATA at a child node `p.extend ed` (ed a "terminal-reaching" edge). center=ed.center, pivot∈center.
σ := blockBlowupMap center pivot ∘ shear, where:
  * shear is a polynomial bijection with shear(0)=0 and (shear u) pivot = u pivot  (KEEPS the pivot coord);
  * blockBlowupMap center pivot w : coordinate j ↦ (w pivot) if j=pivot; (w pivot)*(w j) if j∈center\{pivot}; (w j) if j∉center.
Facts (provable): σ 0 = 0; foldRegion(p.extend ed) = ℝ^D (whole space); and
  foldG(p.extend ed) = foldG p ∘ σ ;   foldB(p.extend ed) u = (u pivot)^δ * foldB p (σ u),  δ ∈ {0,1} a fixed Bool (edgeδ).
All of foldG p, foldB p, foldResid p, σ, foldB(p.extend ed) are polynomial (hence real-analytic); foldB(p.extend ed) is not identically zero.

HYPOTHESES available (this is EVERYTHING):
  (H1) ∃ q, StepInv coreGen (foldG p) (foldB p) (foldResid p) q ℝ^D        -- parent divisibility
  (H2) Deg1SupportedOn (foldResid p) center ℝ^D                             -- parent residual is center-exact degree-1
  (H3) the edge is terminal-reaching (a purely COMBINATORIAL fact about ed.nextState; it says NOTHING
       directly about coreGen, foldB, or vanishing orders).

CONCLUSION TO ADJUDICATE ("conjunct (2)", the "born-terminally cleared-pivot generator"):
  ∃ (i₀ : Fin M) (unit : ℝ^D → ℝ),
     ContinuousOn unit ℝ^D  ∧  unit 0 ≠ 0  ∧
     ∀ u, (coreGen i₀ ∘ foldG(p.extend ed)) u = foldB(p.extend ed) u * unit u.

MY CLAIM (verify or refute independently):
  Conjunct (2) is NOT derivable from (H1)+(H2)+(H3); in fact at δ=0 it is FALSE. Sketch:
  From (H1)+(H2) one derives a child unit-residual divisibility: (coreGen i∘foldG(p.extend ed)) u
   = foldB(p.extend ed) u * Q_i(u) with Q_i continuous. [At δ=0, Q_i u = ∑_j q_ij(σu)·foldResid_p,j(σu);
   at δ=1 the pivot factor of foldB balances the u_pivot the center coords gain under the blow-up.]
  Any valid `unit` must equal Q_{i₀} on {foldB(p.extend ed) ≠ 0} (divide by nonzero), hence (continuity +
   foldB not identically 0 ⟹ {foldB≠0} dense, 0 in its closure) unit 0 = Q_{i₀} 0.
  At δ=0: foldResid_p,j(0) = 0 by (H2) (∑_{i∈center} c_i(0)·0 = 0), so Q_{i₀} 0 = ∑_j q(0)·0 = 0.
   Hence unit 0 = 0, contradicting unit 0 ≠ 0.
  Interpretation: the "unit 0 ≠ 0" (born-terminally cleared pivot) is genuine extra geometric content
   (a specific generator becomes b·(nonvanishing)); divisibility+degree-1+combinatorial-terminality force
   EVERY generator's quotient to vanish at 0, so no bare generator exists.
</task>

<output_contract>
1. VERDICT: one of {MY-CLAIM-CORRECT, MY-CLAIM-WRONG, PARTIALLY} — is conjunct (2) derivable from (H1)-(H3)?
2. If derivable, give the derivation (esp. where unit 0 ≠ 0 comes from). If not, give the cleanest refutation
   (state exactly which δ, and whether the density step is needed or avoidable).
3. Independently check the δ=1 case too: is conjunct (2) derivable at δ=1? (I claim no, but only δ=0 is a hard refutation.)
4. One line: what MINIMAL extra hypothesis would make conjunct (2) provable (the "born-terminally input")?
Keep it under ~400 words. Flag any step where you INFER vs KNOW.
</output_contract>

<grounding_rules>
Reason from the definitions given; do not assume facts about the DLN construction beyond what is stated.
If a step needs an unstated fact (e.g. "foldB not identically zero near 0"), name it explicitly.
</grounding_rules>
