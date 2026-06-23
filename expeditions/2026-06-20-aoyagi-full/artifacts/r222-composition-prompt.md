# Consultation: cleanest decomposition of the (2,2,2) RLCT cover composition (Lean 4 / Mathlib)

I'm assembling the final RLCT value for a deep-linear-network loss via a resolution cover. ALL the
atoms are PROVEN (sorry-free); I need the cleanest way to COMPOSE them. Want to avoid a multi-hundred-
LoC big-bang — prefer a decomposition into small committable sub-lemmas.

## The target

`myF222 (x : Fin 8 → ℝ) = (x0·x4+x1·x6)² + (x0·x5+x1·x7)² + (x2·x4+x3·x6)² + (x2·x5+x3·x7)²`
(= ‖A·B‖² for 2×2 A,B in flat coords a00=x0..b11=x7). Goal:
`rlctAtOn myF222 0 = ⨅_i monomialThreshold (d i)(k i)(h i)` where the ⨅ is over 24 resolution leaves
(8 "unit" leaves d=2 k=![1,1] h=![3,2]; 16 "block" leaves d=3 k=![1,1,1] h=![3,2,3]); each threshold
= 3/2.

## The atoms I have PROVEN (all sorry-free, in my files)

DIRECTION SPINE (S1Cover, abstract over any F):
- `rlctAtOn_ge_of_integral_lt (F) (U open ∋0) (t) (∀c'<t, ∫⁻_U |F|^{-c'} < ⊤) : t ≤ rlctAtOn F 0`
- `rlctAtOn_le_of_box_diverges (F) (t) (∀c'>t, ∀ε>0, ∫⁻_{cubeBox ε}|F|^{-c'} = ⊤) : rlctAtOn F 0 ≤ t`
- `cubeBox_subset_of_isOpen`, `rlctAtOn_le_of_adm_le`.

COVER ENGINE (g5):
- `g5_pivotNode (active : Finset (Fin N)) (U) (hUcov : U =ᵐ ⋃_{p∈active} argmaxCellOn active p) (g) :
   ∫⁻_U g = Σ_{p∈active} ∫⁻_{chartDomOn p \ pivotZeroOn p} ofReal|det φ_p'| · g(φ_p)` — the single
   pivot-blowup node (recursable; for a 3-deep tree compose 3 of these on g' = wᵢ·(g∘φᵢ)).
- `cover_integral_lt_top_iff` — ∫⁻_U finite ⟺ all leaf integrals finite (ENNReal.sum_lt_top).

LEMMA-2 NODE (the regular change-of-coords between blow-up steps):
- `lemma2Hom : (Fin 7→ℝ) ≃ₜ (Fin 7→ℝ)` + `measurePreserving_lemma2Hom` — det-(−1) polynomial diffeo,
  transports rlctAtOn via `rlctAtOn_comp_homeomorph`.

ANALYTIC ATOMS (Case222Cover):
- `monomialIntegrand_lintegral_box_eq_top` — ∀ε>0, ∫⁻_{[0,ε]^d}|monomial|^{-c'}=⊤ when c'≥threshold.
- `monomialIntegrand_integrable_of_lt` — c'<threshold ⟹ monomial integrable on unit box.
- `integrableOn_monomial_mul_unit_iff` — leaf integrand = monomial·|unit|^{-c} integrable ⟺ monomial
  integrable, when |unit|∈[a,b] with 0<a (the per-leaf fidelity bridge).
- `monomial_rlct` (S2 axiom): monomialThreshold = ⨅ axisRatio.

## The questions

**Q1 — do I even need the full `∫⁻_U = Σ_24` cover identity, or is there a shorter route?** Both the
≥ and ≤ spine lemmas (rlctAtOn_ge_of_integral_lt / rlctAtOn_le_of_box_diverges) work per-cube / per-U.
For the ≤ direction: I just need ONE leaf to diverge above ⨅. For the ≥ direction: I need ∫⁻_U finite
below ⨅, which DOES seem to need the full Σ_24 (all leaves finite ⟹ sum finite ⟹ U-integral finite).
Is the cleanest:
  (a) prove `∫⁻_U myF222^{-c'} = Σ_24 leaf-integral` ONCE (the full 3-deep g5_pivotNode composition +
      Lemma-2 splice), then ≥ from "all 24 leaf-integrals finite for c'<⨅", ≤ from "binding leaf
      diverges"; OR
  (b) is there an asymmetry to exploit — e.g. ≤ needs only the SINGLE binding leaf's chart (one
      g5 branch, not the full tree), so I can get ≤ cheaply and only do the full Σ for ≥?

**Q2 — the 3-deep g5_pivotNode composition + Lemma-2 splice.** The tree is: step1 (pivot on the 4
A-coords, 4 charts, blow-up |det|=x³) → Lemma-2 (homeomorph, between A and B coords) → step2 (pivot on
{E,F0,δ}, 3 charts, |det|=s²) → [δ-branch only: step3 (4 charts, |det|=u³)]. To compose `g5_pivotNode`
3×, the recursion is on `g' := wᵢ·(g∘φᵢ)` (the node's output integrand becomes the next node's input).
But Lemma-2 is a HOMEOMORPH (rlctAtOn_comp_homeomorph), not a g5 blow-up node — it sits BETWEEN nodes,
transporting the WHOLE rlctAtOn, not a single lintegral. How do I cleanly interleave a
homeomorph-transport (whole-rlctAtOn) with lintegral-cover nodes (per-U)? Is it cleaner to:
  (a) do everything at the lintegral level (∫⁻_U = Σ via g5 nodes; Lemma-2 enters as a
      change-of-variables INSIDE one lintegral via its measure-preservation + the explicit map), OR
  (b) do everything at the rlctAtOn level (transport across Lemma-2 as a homeomorph; but then the g5
      blow-up nodes — which are NOT homeomorphs — can't transport rlctAtOn directly, only lintegrals)?
This homeomorph-vs-blowup-node interleaving is the structural crux. What's the cleanest Lean architecture?

**Q3 — per-leaf identification `myF222 ∘ φ_leaf = monomial · unit`.** After composing the charts, each
leaf integrand should be `monomialIntegrand · |unit|^{-c}` on a localized box (unit smooth, |unit|∈[a,b],
0<a near the leaf center). This is 24 explicit polynomial identities (the φ are explicit). Is the
cleanest to (a) prove a GENERIC "blow-up chart turns ‖·‖² into x²·(residual)" lemma applied per node,
or (b) grind the 24 explicit `myF222 ∘ φ_leaf = ...` by `ring` after substituting the explicit φ? Given
the symmetry (4 A-charts identical mod a00↔a_ij, etc.), how much can be shared?

Please recommend the OVERALL cleanest architecture (Q2 is the crux), the decomposition into committable
sub-lemmas, and flag any place the homeomorph/blow-up interleaving could hide a soundness gap. Concrete
Mathlib v4.29 lemma names where relevant. I want to minimize total LoC and maximize per-sub-lemma
gateability.
