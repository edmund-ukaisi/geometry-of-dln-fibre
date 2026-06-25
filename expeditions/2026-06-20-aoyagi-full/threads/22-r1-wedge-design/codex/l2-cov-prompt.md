<task>
Lean 4 + Mathlib v4.29. Final architecture question: the change-of-variables Jacobian seam for an L=2
RLCT box-divergence. I have BANKED (sorry-free) the exact algebra: `loss_schur_blowup_factor` proving
‖Schur-blowup product‖² = u²·Uval334 (raw real variables), and Uval334_ge_sq (Uval ≥ a²).

GOAL: `∫⁻_{cubeBox 21 ε} |routeMCore M334|^{−c'} = ⊤` for c'≥4. M334=![3,3,4], minAdm=8.
- `routeMCore M334 x = dlnLoss M334 0 ((paramsEquivFlat M334).symm x)`, dlnLoss = ‖A·C‖²,
  A=((paramsEquivFlat).symm x) 0 : 3×3 matrix, C = ((..) 1) : 3×4.
- `paramsEquivFlat M334 : Params M334 ≃ᵐ (Fin 21 → ℝ)` is a measure-preserving HOMEO (a pure
  coordinate REINDEX via opaque `Fintype.equivFin (FlatIdx M334)`); `(paramsEquivFlat).symm x s i j =
  x (equivFin ⟨⟨s,i⟩,j⟩)` by `rfl`. The opaque equivFin does NOT kernel-reduce (decide fails).

AVAILABLE LEAN LEMMAS (exact names, confirmed):
- `perChart μ φ φ' V N hV hN hφ' hinj hNnull g : ∫⁻_{φ''V} g = ∫⁻_{V\N} ofReal|det(φ' x)|·g(φ x)`
  (single-chart c-o-v with null-exceptional drop, for E = Fin 21 → ℝ).
- `pivotBlowupOn active p` (flat blow-up on Fin N→ℝ: p↦x_p, active j≠p↦x_p·x_j, spectators fixed),
  `pivotBlowupOnDeriv_det active p (hp:p∈active) x : det = (x p)^(active.card−1)`,
  `pivotBlowupOn_hasFDerivWithinAt`, `pivotBlowupOn_injOn` (injective off {x_p=0}).
- `measurePreserving_paramsEquivFlat M : MeasurePreserving (paramsEquivFlat M) volume volume`.
- `monomialIntegrand_lintegral_box_eq_top d k h hk c' hc' hc'0 hε : ∫⁻_{[0,ε]^d} |monomialIntegrand|=⊤`.
- `lintegral_mono_set`, `coordZero_null` (coord hyperplane is null), `cubeBox_subset_of_isOpen`.

THE OBSTRUCTION: my chart Ψ must (a) have a KNOWN action on matrix entries (so the loss factors as
u²·Uval334), AND (b) have a computable flat Jacobian det = u^7. The Schur shear T:=y+a⁻¹bS, D:=E−ca⁻¹b
is NONLINEAR (products of spectator coords) but has det 1; the blow-up scales 8 coords by pivot u (det
u^7). Two candidate seams:
  SEAM 1 (chart on Params, transport): define chartP : (Fin 21→ℝ) → Params M334 (Schur+blowup matrices
    read off x directly, NO equivFin), Ψ := paramsEquivFlat ∘ chartP. Then routeMCore∘Ψ = dlnLoss∘chartP
    (clean, equivFin cancels). But det DΨ = det D(chartP) needs the fderiv of a Params-valued map, and
    perChart wants φ : E→E (same type) — type mismatch (Params ≠ Fin 21→ℝ as the perChart E).
  SEAM 2 (chart on flat, conjugate): Ψ := paramsEquivFlat ∘ chartP ∘ (paramsEquivFlat).symm :
    (Fin 21→ℝ)→(Fin 21→ℝ). Now Ψ:E→E fits perChart. routeMCore∘Ψ = dlnLoss∘chartP∘symm. But det DΨ =
    det D(chartP composed with two linear reindexes) — the reindex is LINEAR with det ±1, so |det DΨ| =
    |det D(chartP-in-flat-coords)|. Still need chartP's flat fderiv det.
  SEAM 3 (define the WHOLE chart as an explicit pivotBlowupOn ∘ explicit-shear on Fin 21→ℝ, and prove
    its action on entries via the equivFin REFLECTION lemmas, like the prior scratch's wedgeParam_entry
    which proved per-entry values WITHOUT decide, using injectivity reflection). Then det via
    pivotBlowupOnDeriv_det for the blowup factor and a hand fderiv for the shear.
</task>

<output_contract>
1. Which seam (1/2/3) minimizes Lean pain for the Jacobian det = u^7 while keeping the entry-action
   known? 2-4 sentences. Key sub-question: is it easier to compute det of the COMPOSITE Schur+blowup as
   ONE flat map, or to FACTOR the c-o-v into (measure-preserving reindex/shear, det handled by
   MeasurePreserving) ∘ (pure pivotBlowupOn, det = pivotBlowupOnDeriv_det)?
2. Can the Schur shear be made a SEPARATE measure-preserving step (so its Jacobian never needs explicit
   computation — only the pivotBlowupOn carries the u^7)? The shear T=y+a⁻¹bS is a per-fiber translation
   in (E,y) by a function of the OTHER coords (a,b,c,S) — is that a measure-preserving map on Fin 21→ℝ
   (a "shear"/unipotent), and is there a Mathlib lemma (name-uncertain ok) that a translation-in-a-
   subset-of-coords-by-a-function-of-the-complement is volume-preserving? If so the architecture becomes
   [shear: m.p., det dropped] ∘ [pivotBlowupOn 8 coords: det u^7] — both handled by existing lemmas.
3. The MINIMAL concrete plan: list the 5-7 lemmas to add (each one line) to go from my banked algebra to
   the box-divergence, in dependency order, flagging the one carrying real fderiv weight.
4. If a clean factored c-o-v is NOT reachable in one tide, the single HONEST sorry to leave (precise
   obligation statement) such that the rest is sorry-free.
</output_contract>

<grounding_rules>
Flag inference vs fact. You don't have the Lean source. The banked algebra (loss=u²·Uval334, Uval≥a²) is
DONE. Mathlib lemma names you propose: mark name-uncertain; I verify before use. The measure-preserving-
shear question is the crux — if it works the whole thing factors cleanly.
</grounding_rules>
