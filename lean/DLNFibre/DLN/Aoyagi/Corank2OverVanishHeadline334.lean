import DLNFibre.DLN.Aoyagi.Corank2OverVanishAssembly334
import DLNFibre.DLN.Aoyagi.Corank2CleanIntegrable334
import DLNFibre.DLN.Aoyagi.Corank2OverVanishTransport334
import DLNFibre.DLN.Aoyagi.Corank2OverVanishA_20_1_5
import DLNFibre.DLN.Aoyagi.Corank2OverVanishA_20_1_6
import DLNFibre.DLN.Aoyagi.Corank2OverVanishA_20_1_7
import DLNFibre.DLN.Aoyagi.Corank2OverVanishA_20_5_1
import DLNFibre.DLN.Aoyagi.Corank2OverVanishA_20_5_5
import DLNFibre.DLN.Aoyagi.Corank2OverVanishA_20_5_6
import DLNFibre.DLN.Aoyagi.Corank2OverVanishA_20_5_7
import DLNFibre.DLN.Aoyagi.Corank2OverVanishB_20_6_1
import DLNFibre.DLN.Aoyagi.Corank2OverVanishB_20_6_5
import DLNFibre.DLN.Aoyagi.Corank2OverVanishB_20_6_6
import DLNFibre.DLN.Aoyagi.Corank2OverVanishB_20_6_7
import DLNFibre.DLN.Aoyagi.Corank2OverVanishB_20_7_1
import DLNFibre.DLN.Aoyagi.Corank2OverVanishB_20_7_5
import DLNFibre.DLN.Aoyagi.Corank2OverVanishB_20_7_6
import DLNFibre.DLN.Aoyagi.Corank2OverVanishB_20_7_7

/-!
# `DLN.Aoyagi.Corank2OverVanishHeadline334` — the UNCONDITIONAL (3,3,4) V-lower headline

The convergence deliverable of the expedition: the hypothesis-free, cite-free, monument-free

`rlctAt_coreGen334_ge_four : (4:ℝ) ≤ rlctAt (sumSqFam (coreGen dvec eWrap)) 0`.

It applies the STEP-6 spine `OverVanishAssembly334.rlctAt_coreGen334_ge_four_of_perchart_integrable`
to the **folded chart family** `gFold` (Approach B, controller-decided): `gFold c = gFin c ∘ psiOf c`
where `psiOf c` is the identity on the clean-144 leaves and the `σ_{p1}`-conjugate of the per-type
straightening `psiCanon` on the over-vanishing-144. The three spine obligations are discharged as:

* per-chart integrability `hint` — the clean branch by the committed (b) brick
  `CleanIntegrable334.clean_hint_of_entry`; the over-vanishing branch by the bridge
  `OverVanish334.chart_integrableAtFilter_of_monoSumSq_dom` fed the σ_{p1}-transported per-type
  domination (`OverVanishTransport334.leaf_domination_P{n}` ← the 16 `canon_domination`);
* the folded cover `hcover` — `NativeFan334.native_hcover` transported through the folded `Ψ` on the
  over-vanishing leaves (each folded image ⊇ the unfolded over the inflated ball);
* the area-formula fields `hgdiff`/`hg_inj`/`hexcep_*` — the folded chart is differentiable, injective
  off its critical set `{jacWeight (jacExpFold c) = 0}` (which is null + closed).

## Status
Foundation checkpoint: the classifier (`bundleOf`), the folded family (`gFold`/`domFold`), and the
headline reduced to the spine. The three substantive obligations are the tracked frontier holes
`-- map: ov-headline-{cover,ainj,hint}`.
-/

open MeasureTheory Set Filter Topology Metric RLCT
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativeValue334
open DLNFibre.DLN.Aoyagi.NativeJac334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
open DLNFibre.DLN.Aoyagi.CleanHentry334

namespace DLNFibre.DLN.Aoyagi.OverVanishHeadline334

-- `IsClean c` (a `Finset` membership hidden behind a `def`) is classically decidable; the branch
-- selectors below are `noncomputable` anyway (`idxEquiv` is), so the classical instance is free.
attribute [local instance] Classical.propDecidable

/-! ## §1 — the per-type data bundle and the 16-way classifier -/

/-- The per-type over-vanishing data: the straightening `psi`, its canonical leaf index `idxC`, the
dominant-monomial exponent `a`, the regular-sequence block `Z`, and the Jacobian exponent `jac`. -/
structure OVData where
  /-- the per-type canonical straightening shear `Ψ` (a `blockShear`). -/
  psi : (Fin 21 → ℝ) → (Fin 21 → ℝ)
  /-- the canonical leaf index `(20, p2c, p3c)`. -/
  idxC : Idx
  /-- the dominant-monomial exponent `vmExp`. -/
  a : Fin 21 → ℕ
  /-- the regular-sequence coordinate block `Z` (`|Z| = 8`). -/
  Z : Finset (Fin 21)
  /-- the canonical Jacobian exponent `jacExp idxC`. -/
  jac : Fin 21 → ℕ

/-- Package one per-type namespace's data into an `OVData`. -/
private noncomputable def mkBundle (psi : (Fin 21 → ℝ) → (Fin 21 → ℝ)) (idxC : Idx)
    (a : Fin 21 → ℕ) (Z : Finset (Fin 21)) : OVData :=
  ⟨psi, idxC, a, Z, jacExp idxC⟩

/-- **The 16-way base-type classifier.** Keyed on the CANONICAL pivots `(q, r) = (σ_{p1} p2,
σ_{p1} p3) ∈ {1,5,6,7}²`, returns the per-type over-vanishing data. The default (off-grid, i.e.
clean charts) is the canonical `(20,1,1)` bundle (never consumed on the value path). -/
noncomputable def bundleOf (q r : Fin 21) : OVData :=
  if q = 1 then
    if r = 1 then mkBundle OverVanishCanon334.psiCanon OverVanishCanon334.idxCanon
        OverVanishCanon334.vmExpCanon OverVanishCanon334.Zcanon
    else if r = 5 then mkBundle OverVanishA_20_1_5.psiCanon OverVanishA_20_1_5.idxCanon
        OverVanishA_20_1_5.vmExpCanon OverVanishA_20_1_5.Zcanon
    else if r = 6 then mkBundle OverVanishA_20_1_6.psiCanon OverVanishA_20_1_6.idxCanon
        OverVanishA_20_1_6.vmExpCanon OverVanishA_20_1_6.Zcanon
    else mkBundle OverVanishA_20_1_7.psiCanon OverVanishA_20_1_7.idxCanon
        OverVanishA_20_1_7.vmExpCanon OverVanishA_20_1_7.Zcanon
  else if q = 5 then
    if r = 1 then mkBundle OverVanishA_20_5_1.psiCanon OverVanishA_20_5_1.idxCanon
        OverVanishA_20_5_1.vmExpCanon OverVanishA_20_5_1.Zcanon
    else if r = 5 then mkBundle OverVanishA_20_5_5.psiCanon OverVanishA_20_5_5.idxCanon
        OverVanishA_20_5_5.vmExpCanon OverVanishA_20_5_5.Zcanon
    else if r = 6 then mkBundle OverVanishA_20_5_6.psiCanon OverVanishA_20_5_6.idxCanon
        OverVanishA_20_5_6.vmExpCanon OverVanishA_20_5_6.Zcanon
    else mkBundle OverVanishA_20_5_7.psiCanon OverVanishA_20_5_7.idxCanon
        OverVanishA_20_5_7.vmExpCanon OverVanishA_20_5_7.Zcanon
  else if q = 6 then
    if r = 1 then mkBundle OverVanishB_20_6_1.psiCanon OverVanishB_20_6_1.idxCanon
        OverVanishB_20_6_1.vmExpCanon OverVanishB_20_6_1.Zcanon
    else if r = 5 then mkBundle OverVanishB_20_6_5.psiCanon OverVanishB_20_6_5.idxCanon
        OverVanishB_20_6_5.vmExpCanon OverVanishB_20_6_5.Zcanon
    else if r = 6 then mkBundle OverVanishB_20_6_6.psiCanon OverVanishB_20_6_6.idxCanon
        OverVanishB_20_6_6.vmExpCanon OverVanishB_20_6_6.Zcanon
    else mkBundle OverVanishB_20_6_7.psiCanon OverVanishB_20_6_7.idxCanon
        OverVanishB_20_6_7.vmExpCanon OverVanishB_20_6_7.Zcanon
  else
    if r = 1 then mkBundle OverVanishB_20_7_1.psiCanon OverVanishB_20_7_1.idxCanon
        OverVanishB_20_7_1.vmExpCanon OverVanishB_20_7_1.Zcanon
    else if r = 5 then mkBundle OverVanishB_20_7_5.psiCanon OverVanishB_20_7_5.idxCanon
        OverVanishB_20_7_5.vmExpCanon OverVanishB_20_7_5.Zcanon
    else if r = 6 then mkBundle OverVanishB_20_7_6.psiCanon OverVanishB_20_7_6.idxCanon
        OverVanishB_20_7_6.vmExpCanon OverVanishB_20_7_6.Zcanon
    else mkBundle OverVanishB_20_7_7.psiCanon OverVanishB_20_7_7.idxCanon
        OverVanishB_20_7_7.vmExpCanon OverVanishB_20_7_7.Zcanon

/-! ## §2 — the pivot projections, the loss-symmetry selector, and the folded family -/

/-- The node-1 pivot of leaf `c` (`= (idxEquiv c).1.1`). -/
noncomputable def p1Of (c : Fin numCharts) : Fin 21 := pivot1 c
/-- The node-2 native pivot of leaf `c`. -/
noncomputable def p2Of (c : Fin numCharts) : Fin 21 := pivot2 c
/-- The node-3 native pivot of leaf `c`. -/
noncomputable def p3Of (c : Fin numCharts) : Fin 21 := pivot3 c

/-- The loss-symmetry permutation `σ_{p1}` for a dominant pivot `p1` (`sigP0..sigP7`; the identity at
the canonical `p1 = 20`). -/
noncomputable def sigOf (p1 : Fin 21) : Equiv.Perm (Fin 21) :=
  if p1 = 0 then OverVanishTransport334.sigP0
  else if p1 = 1 then OverVanishTransport334.sigP1
  else if p1 = 2 then OverVanishTransport334.sigP2
  else if p1 = 3 then OverVanishTransport334.sigP3
  else if p1 = 4 then OverVanishTransport334.sigP4
  else if p1 = 5 then OverVanishTransport334.sigP5
  else if p1 = 6 then OverVanishTransport334.sigP6
  else if p1 = 7 then OverVanishTransport334.sigP7
  else Equiv.refl (Fin 21)

/-- The canonical node-2 pivot of leaf `c` (`= σ_{p1} p2`). -/
noncomputable def canonQ (c : Fin numCharts) : Fin 21 := sigOf (p1Of c) (p2Of c)
/-- The canonical node-3 pivot of leaf `c` (`= σ_{p1} p3`). -/
noncomputable def canonR (c : Fin numCharts) : Fin 21 := sigOf (p1Of c) (p3Of c)

/-- The per-chart over-vanishing bundle (its base type). -/
noncomputable def bundleAt (c : Fin numCharts) : OVData := bundleOf (canonQ c) (canonR c)

/-- **The folding shear `psiOf c`.** The identity on the clean-144 leaves; the `σ_{p1}`-conjugate of
the per-type straightening `psiCanon` on the over-vanishing-144. -/
noncomputable def psiOf (c : Fin numCharts) : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  if IsClean c then id
  else OverVanishTransport334.conjChart (sigOf (p1Of c)) (bundleAt c).psi

/-- **The folded chart** `gFold c = gFin c ∘ psiOf c`. -/
noncomputable def gFold (c : Fin numCharts) : (Fin 21 → ℝ) → (Fin 21 → ℝ) := gFin c ∘ psiOf c

/-- The folded domain: the leaf box inflated for the cubic straightening (`leafR + 2·leafR³`). -/
def domFold (_ : Fin numCharts) : Set (Fin 21 → ℝ) := closedBall 0 (leafR + 2 * leafR ^ 3)

/-- The folded chart neighbourhood (`univ`; the area formula only needs `dom ⊆ nbhd` open). -/
def nbhdFold (_ : Fin numCharts) : Set (Fin 21 → ℝ) := Set.univ

/-- **The folded per-chart Jacobian exponent.** On the clean-144 it is `jacFin c`; on the
over-vanishing-144 it is the `σ_{p1}`-transported `jacExp` of the base type. Its `jacWeight` zero-set
is the folded chart's critical set (via the folded-Jacobian collapse). -/
noncomputable def jacExpFold (c : Fin numCharts) : Fin 21 → ℕ :=
  if IsClean c then jacFin c
  else fun d => (bundleAt c).jac ((sigOf (p1Of c)).symm d)

/-- The folded chart's exceptional locus `{u | jacWeight (jacExpFold c) u = 0}` (null + closed). -/
noncomputable def excepFold (c : Fin numCharts) : Set (Fin 21 → ℝ) :=
  {u | jacWeight (jacExpFold c) u = 0}

theorem isCompact_domFold (c : Fin numCharts) : IsCompact (domFold c) :=
  isCompact_closedBall _ _

theorem isOpen_nbhdFold (c : Fin numCharts) : IsOpen (nbhdFold c) := isOpen_univ

theorem domFold_sub (c : Fin numCharts) : domFold c ⊆ nbhdFold c := Set.subset_univ _

theorem measurableSet_excepFold (c : Fin numCharts) : MeasurableSet (excepFold c) :=
  (isClosed_eq (continuous_jacWeight (jacExpFold c)) continuous_const).measurableSet

theorem volume_excepFold (c : Fin numCharts) : volume (excepFold c) = 0 :=
  volume_jacWeight_zeroSet (jacExpFold c)

/-! ## §2.5 — folded-chart differentiability -/

/-- **Coordinate precomposition is differentiable.** `w ↦ (fun k ↦ w (ρ k))` is linear, hence
smooth. -/
theorem differentiable_reindex (ρ : Fin 21 → Fin 21) :
    Differentiable ℝ (fun w : Fin 21 → ℝ ↦ fun k ↦ w (ρ k)) :=
  differentiable_pi.2 (fun k ↦ differentiable_pi.1 differentiable_id (ρ k))

/-- **`conjChart` preserves differentiability.** `conjChart σ H = post_{σ⁻¹} ∘ H ∘ pre_σ` with the two
coordinate reindexings linear. -/
theorem differentiable_conjChart (σ : Equiv.Perm (Fin 21))
    {H : (Fin 21 → ℝ) → (Fin 21 → ℝ)} (hH : Differentiable ℝ H) :
    Differentiable ℝ (OverVanishTransport334.conjChart σ H) :=
  (differentiable_reindex σ.symm).comp (hH.comp (differentiable_reindex σ))

/-- Every base-type straightening `psi` is differentiable (each per-type `differentiable_psiCanon`). -/
theorem bundleOf_psi_differentiable (q r : Fin 21) : Differentiable ℝ (bundleOf q r).psi := by
  simp only [bundleOf, mkBundle]
  split_ifs <;>
    first
      | exact OverVanishCanon334.differentiable_psiCanon
      | exact OverVanishA_20_1_5.differentiable_psiCanon
      | exact OverVanishA_20_1_6.differentiable_psiCanon
      | exact OverVanishA_20_1_7.differentiable_psiCanon
      | exact OverVanishA_20_5_1.differentiable_psiCanon
      | exact OverVanishA_20_5_5.differentiable_psiCanon
      | exact OverVanishA_20_5_6.differentiable_psiCanon
      | exact OverVanishA_20_5_7.differentiable_psiCanon
      | exact OverVanishB_20_6_1.differentiable_psiCanon
      | exact OverVanishB_20_6_5.differentiable_psiCanon
      | exact OverVanishB_20_6_6.differentiable_psiCanon
      | exact OverVanishB_20_6_7.differentiable_psiCanon
      | exact OverVanishB_20_7_1.differentiable_psiCanon
      | exact OverVanishB_20_7_5.differentiable_psiCanon
      | exact OverVanishB_20_7_6.differentiable_psiCanon
      | exact OverVanishB_20_7_7.differentiable_psiCanon

/-- **The folding shear `psiOf c` is differentiable** (identity on clean; `conjChart` of a
differentiable per-type straightening on over-vanishing). -/
theorem differentiable_psiOf (c : Fin numCharts) : Differentiable ℝ (psiOf c) := by
  unfold psiOf
  split_ifs with h
  · exact differentiable_id
  · exact differentiable_conjChart _ (bundleOf_psi_differentiable (canonQ c) (canonR c))

/-- **The folded chart `gFold c` is differentiable.** -/
theorem differentiable_gFold (c : Fin numCharts) : Differentiable ℝ (gFold c) :=
  (differentiable_gFin c).comp (differentiable_psiOf c)

/-! ## §3 — the headline -/

/-- **The UNCONDITIONAL (3,3,4) V-lower headline** (Approach B, folded chart). Hypothesis-free,
cite-free, monument-free: `4 ≤ rlctAt` of the `(3,3,4)` core loss at `0`. Applies the STEP-6 spine to
the folded family `gFold` over the inflated leaf box `domFold`. -/
theorem rlctAt_coreGen334_ge_four :
    (4 : ℝ) ≤ rlctAt (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ) := by
  refine OverVanishAssembly334.rlctAt_coreGen334_ge_four_of_perchart_integrable
    (numCharts := numCharts) ⟨⟨0, numCharts_pos⟩, Finset.mem_univ _⟩
    gFold domFold nbhdFold excepFold
    ?hgdiff isCompact_domFold isOpen_nbhdFold domFold_sub
    measurableSet_excepFold volume_excepFold ?hg_inj ?hcover ?hint
  case hgdiff => exact differentiable_gFold
  case hg_inj =>
    -- map: ov-headline-ainj — folded chart a.e.-injectivity off its critical set.
    sorry
  case hcover =>
    -- map: ov-headline-cover — native_hcover transported through the folded Ψ.
    sorry
  case hint =>
    -- map: ov-headline-hint — per-chart integrability: clean (b) / over-vanishing (c).
    sorry

end DLNFibre.DLN.Aoyagi.OverVanishHeadline334
