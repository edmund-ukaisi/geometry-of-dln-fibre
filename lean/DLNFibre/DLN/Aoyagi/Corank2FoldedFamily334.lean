import DLNFibre.DLN.Aoyagi.Corank2OverVanishAssembly334
import DLNFibre.DLN.Aoyagi.Corank2CleanIntegrable334
import DLNFibre.DLN.Aoyagi.Corank2OverVanishTransport334
import DLNFibre.DLN.Aoyagi.Corank2ChartJac
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
# `DLN.Aoyagi.Corank2FoldedFamily334` — the folded-family FOUNDATION for the (3,3,4) V-lower

The shared foundation the ainj/hint helpers + the headline (`Corank2OverVanishHeadline334`) build on.
The **folded chart family** `gFold` (Approach B, controller-decided): `gFold c = gFin c ∘ psiOf c`
where `psiOf c` is the identity on the clean-144 leaves and the `σ_{p1}`-conjugate of the per-type
straightening `psiCanon` on the over-vanishing-144. This file carries the DEFS + the DONE spine
obligations; the two open obligations (ainj `hg_inj`, over-vanishing `hint`) are proved in sibling
files against this foundation and wired in the headline.

Delivered here:
* the 16-way base-type classifier `bundleOf` (proof-carrying: `hfoldedJac` + `hdom` per type) + the
  folded family `gFold`/`domFold`/`nbhdFold`/`excepFold`/`jacExpFold`;
* the classifier-correctness kill-condition (`canonQ_mem_of_notClean`/`canonR_mem`: every
  over-vanishing chart's `(canonQ, canonR) ∈ {1,5,6,7}²`, so `bundleOf` returns the right per-type
  data — the soundness gate for the folded route);
* the DONE spine fields — `differentiable_gFold` (hgdiff), `folded_hcover` (hcover),
  `isCompact_domFold`/`isOpen_nbhdFold`/`domFold_sub`/`measurableSet_excepFold`/`volume_excepFold`;
* the SHARED coordinate-conjugation transport `jacDet_conjChart_abs` + `jacWeight_reindex`, and the
  O(1) bundle projections `bundleOf_foldedJac`/`bundleOf_domination` — consumed by BOTH open
  obligations.
-/

open MeasureTheory Set Filter Topology Metric RLCT
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativeValue334
open DLNFibre.DLN.Aoyagi.NativeJac334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
open DLNFibre.DLN.Aoyagi.CleanHentry334

namespace DLNFibre.DLN.Aoyagi.OverVanishHeadline334

-- `IsClean c` is a `Finset` membership hidden behind a `def`; expose its (computable) decidability so
-- the branch selectors' `if IsClean c` synthesizes without a blanket classical instance (which would
-- shadow the `decide`-able `Finset`/exponent instances the over-vanishing seat needs).
noncomputable instance decIsClean (c : Fin numCharts) : Decidable (IsClean c) :=
  inferInstanceAs (Decidable ((pivot1 c, pivot2 c) ∈ cleanPairs))

/-! ## §1 — the per-type data bundle and the 16-way classifier -/

/-- The per-type over-vanishing data: the straightening `psi`, its canonical leaf index `idxC`, the
dominant-monomial exponent `a`, the regular-sequence block `Z`, the Jacobian exponent `jac`, and the
two per-type value FACTS — the folded-Jacobian collapse and the product-germ domination. Carrying the
proofs makes the downstream 16-way dispatch an O(1) projection (a bare `first`-search over the 16
`canon_foldedJac`/`canon_domination` times out on the heavy `gFlat`-composite defeqs). -/
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
  /-- the folded-Jacobian collapse `|jacDet (gFlat idxC ∘ ψ)| = jacWeight jac` (`canon_foldedJac`). -/
  hfoldedJac : ∀ u, |jacDet (gFlat idxC ∘ psi) u| = jacWeight jac u
  /-- the product-germ domination `vm²·∑_Z z² ≤ loss` (`canon_domination`). -/
  hdom : ∀ u, monoSumSqGerm a Z u
    ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gFlat idxC ∘ psi)) u

/-- Package one per-type namespace's data + value facts into an `OVData`. -/
private noncomputable def mkBundle (psi : (Fin 21 → ℝ) → (Fin 21 → ℝ)) (idxC : Idx)
    (a : Fin 21 → ℕ) (Z : Finset (Fin 21))
    (hfoldedJac : ∀ u, |jacDet (gFlat idxC ∘ psi) u| = jacWeight (jacExp idxC) u)
    (hdom : ∀ u, monoSumSqGerm a Z u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gFlat idxC ∘ psi)) u) : OVData :=
  ⟨psi, idxC, a, Z, jacExp idxC, hfoldedJac, hdom⟩

/-- **The 16-way base-type classifier.** Keyed on the CANONICAL pivots `(q, r) = (σ_{p1} p2,
σ_{p1} p3) ∈ {1,5,6,7}²`, returns the per-type over-vanishing data + value facts. The default
(off-grid, i.e. clean charts) is the canonical `(20,1,1)` bundle (never consumed on the value path). -/
noncomputable def bundleOf (q r : Fin 21) : OVData :=
  if q = 1 then
    if r = 1 then mkBundle OverVanishCanon334.psiCanon OverVanishCanon334.idxCanon
        OverVanishCanon334.vmExpCanon OverVanishCanon334.Zcanon
        OverVanishCanon334.canon_foldedJac OverVanishCanon334.canon_domination
    else if r = 5 then mkBundle OverVanishA_20_1_5.psiCanon OverVanishA_20_1_5.idxCanon
        OverVanishA_20_1_5.vmExpCanon OverVanishA_20_1_5.Zcanon
        OverVanishA_20_1_5.canon_foldedJac OverVanishA_20_1_5.canon_domination
    else if r = 6 then mkBundle OverVanishA_20_1_6.psiCanon OverVanishA_20_1_6.idxCanon
        OverVanishA_20_1_6.vmExpCanon OverVanishA_20_1_6.Zcanon
        OverVanishA_20_1_6.canon_foldedJac OverVanishA_20_1_6.canon_domination
    else mkBundle OverVanishA_20_1_7.psiCanon OverVanishA_20_1_7.idxCanon
        OverVanishA_20_1_7.vmExpCanon OverVanishA_20_1_7.Zcanon
        OverVanishA_20_1_7.canon_foldedJac OverVanishA_20_1_7.canon_domination
  else if q = 5 then
    if r = 1 then mkBundle OverVanishA_20_5_1.psiCanon OverVanishA_20_5_1.idxCanon
        OverVanishA_20_5_1.vmExpCanon OverVanishA_20_5_1.Zcanon
        OverVanishA_20_5_1.canon_foldedJac OverVanishA_20_5_1.canon_domination
    else if r = 5 then mkBundle OverVanishA_20_5_5.psiCanon OverVanishA_20_5_5.idxCanon
        OverVanishA_20_5_5.vmExpCanon OverVanishA_20_5_5.Zcanon
        OverVanishA_20_5_5.canon_foldedJac OverVanishA_20_5_5.canon_domination
    else if r = 6 then mkBundle OverVanishA_20_5_6.psiCanon OverVanishA_20_5_6.idxCanon
        OverVanishA_20_5_6.vmExpCanon OverVanishA_20_5_6.Zcanon
        OverVanishA_20_5_6.canon_foldedJac OverVanishA_20_5_6.canon_domination
    else mkBundle OverVanishA_20_5_7.psiCanon OverVanishA_20_5_7.idxCanon
        OverVanishA_20_5_7.vmExpCanon OverVanishA_20_5_7.Zcanon
        OverVanishA_20_5_7.canon_foldedJac OverVanishA_20_5_7.canon_domination
  else if q = 6 then
    if r = 1 then mkBundle OverVanishB_20_6_1.psiCanon OverVanishB_20_6_1.idxCanon
        OverVanishB_20_6_1.vmExpCanon OverVanishB_20_6_1.Zcanon
        OverVanishB_20_6_1.canon_foldedJac OverVanishB_20_6_1.canon_domination
    else if r = 5 then mkBundle OverVanishB_20_6_5.psiCanon OverVanishB_20_6_5.idxCanon
        OverVanishB_20_6_5.vmExpCanon OverVanishB_20_6_5.Zcanon
        OverVanishB_20_6_5.canon_foldedJac OverVanishB_20_6_5.canon_domination
    else if r = 6 then mkBundle OverVanishB_20_6_6.psiCanon OverVanishB_20_6_6.idxCanon
        OverVanishB_20_6_6.vmExpCanon OverVanishB_20_6_6.Zcanon
        OverVanishB_20_6_6.canon_foldedJac OverVanishB_20_6_6.canon_domination
    else mkBundle OverVanishB_20_6_7.psiCanon OverVanishB_20_6_7.idxCanon
        OverVanishB_20_6_7.vmExpCanon OverVanishB_20_6_7.Zcanon
        OverVanishB_20_6_7.canon_foldedJac OverVanishB_20_6_7.canon_domination
  else
    if r = 1 then mkBundle OverVanishB_20_7_1.psiCanon OverVanishB_20_7_1.idxCanon
        OverVanishB_20_7_1.vmExpCanon OverVanishB_20_7_1.Zcanon
        OverVanishB_20_7_1.canon_foldedJac OverVanishB_20_7_1.canon_domination
    else if r = 5 then mkBundle OverVanishB_20_7_5.psiCanon OverVanishB_20_7_5.idxCanon
        OverVanishB_20_7_5.vmExpCanon OverVanishB_20_7_5.Zcanon
        OverVanishB_20_7_5.canon_foldedJac OverVanishB_20_7_5.canon_domination
    else if r = 6 then mkBundle OverVanishB_20_7_6.psiCanon OverVanishB_20_7_6.idxCanon
        OverVanishB_20_7_6.vmExpCanon OverVanishB_20_7_6.Zcanon
        OverVanishB_20_7_6.canon_foldedJac OverVanishB_20_7_6.canon_domination
    else mkBundle OverVanishB_20_7_7.psiCanon OverVanishB_20_7_7.idxCanon
        OverVanishB_20_7_7.vmExpCanon OverVanishB_20_7_7.Zcanon
        OverVanishB_20_7_7.canon_foldedJac OverVanishB_20_7_7.canon_domination

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

set_option maxRecDepth 8000 in
/-- **Classifier correctness — node-3.** `canonR c = σ_{p1} p3 ∈ {1,5,6,7}` for EVERY chart (`p3 ∈
σC2(p1)` and `σ_{p1}` maps `σC2(p1)` onto the canonical `σC2(20) = {1,5,6,7}`). -/
theorem canonR_mem (c : Fin numCharts) : canonR c ∈ ({1, 5, 6, 7} : Finset (Fin 21)) := by
  have key : ∀ p1 ∈ S1, ∀ p3 ∈ sigmaC2Fs p1, sigOf p1 p3 ∈ ({1, 5, 6, 7} : Finset (Fin 21)) := by
    decide
  exact key (p1Of c) (idxEquiv c).1.2 (p3Of c) (idxEquiv c).2.2.2

set_option maxRecDepth 8000 in
/-- **Classifier correctness — node-2 (the over-vanishing kill-condition).** For an over-vanishing
chart (`¬IsClean c`), `canonQ c = σ_{p1} p2 ∈ {1,5,6,7}` — so `bundleOf (canonQ c) (canonR c)` hits a
genuine keyed branch (`{1,5,6,7}²`), NOT the default. Equivalently, `cleanPairs` is EXACTLY the pairs
`(p1,p2)` with `σ_{p1} p2 ∈ {0,2,3,4}`; verified by `decide` over `S1 × σC1(p1)`. Without this the
folded straightening `psiOf c` would use the wrong base type and the construction would be unsound. -/
theorem canonQ_mem_of_notClean (c : Fin numCharts) (hc : ¬ IsClean c) :
    canonQ c ∈ ({1, 5, 6, 7} : Finset (Fin 21)) := by
  have key : ∀ p1 ∈ S1, ∀ p2 ∈ sigmaC1Fs p1,
      (p1, p2) ∉ cleanPairs → sigOf p1 p2 ∈ ({1, 5, 6, 7} : Finset (Fin 21)) := by decide
  exact key (p1Of c) (idxEquiv c).1.2 (p2Of c) (idxEquiv c).2.1.2 hc

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

/-! ## §2.6 — the folded cover -/

/-- `1 ≤ leafR` (the leaf box radius is `fInfl`-inflated from `1`, `fInfl x = x + 2x² ≥ x`). -/
theorem leafR_ge_one : (1 : ℝ) ≤ leafR := by
  have hge : ∀ x : ℝ, 0 ≤ x → x ≤ fInfl x := fun x hx => by
    simp only [fInfl]; nlinarith [sq_nonneg x]
  calc (1 : ℝ) ≤ max (fInfl (max (fInfl (max 1 1)) 1)) 1 := le_max_right _ _
    _ ≤ fInfl (max (fInfl (max (fInfl (max 1 1)) 1)) 1) :=
        hge _ (le_trans zero_le_one (le_max_right _ _))
    _ = leafR := rfl

theorem leafR_nonneg : (0 : ℝ) ≤ leafR := le_trans zero_le_one leafR_ge_one

/-- A coordinate reindexing by a permutation maps a `0`-ball onto itself (it preserves the sup
norm). -/
theorem reindex_image_closedBall (ρ : Equiv.Perm (Fin 21)) {R : ℝ} (hR : 0 ≤ R) :
    (fun w : Fin 21 → ℝ ↦ fun k ↦ w (ρ k)) '' closedBall 0 R = closedBall 0 R := by
  ext v
  simp only [Set.mem_image, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [pi_norm_le_iff_of_nonneg hR] at hw ⊢
    exact fun i ↦ hw (ρ i)
  · intro hv
    refine ⟨fun k ↦ v (ρ.symm k), ?_, by funext k; simp [Equiv.apply_symm_apply]⟩
    rw [pi_norm_le_iff_of_nonneg hR] at hv ⊢
    exact fun i ↦ hv (ρ.symm i)

/-- **`conjChart` preserves the covering property.** If `H` covers (`closedBall 0 r ⊆ H '' closedBall
0 R`), so does its `σ`-conjugate: `conjChart σ H = post_{σ⁻¹} ∘ H ∘ pre_σ` and both reindexings fix
`0`-balls. -/
theorem conjChart_covers (σ : Equiv.Perm (Fin 21)) {H : (Fin 21 → ℝ) → (Fin 21 → ℝ)} {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hcov : closedBall 0 r ⊆ H '' closedBall 0 R) :
    closedBall (0 : Fin 21 → ℝ) r ⊆ OverVanishTransport334.conjChart σ H '' closedBall 0 R := by
  have heq : OverVanishTransport334.conjChart σ H '' closedBall 0 R
      = (fun v : Fin 21 → ℝ ↦ fun t ↦ v (σ.symm t)) '' (H '' closedBall 0 R) := by
    rw [show OverVanishTransport334.conjChart σ H
        = (fun v : Fin 21 → ℝ ↦ fun t ↦ v (σ.symm t)) ∘ (H ∘ (fun w : Fin 21 → ℝ ↦ fun k ↦ w (σ k)))
        from rfl, Set.image_comp, Set.image_comp, reindex_image_closedBall σ hR]
  rw [heq, ← reindex_image_closedBall σ.symm hr]
  exact Set.image_mono hcov

/-- A quadratically-bounded `blockShear` covers with the cubic inflation `r + 2r³` (the 4
non-coinciding leaves whose straightening is quadratic; `2r² ≤ 2r³` for `r = leafR ≥ 1`). -/
theorem psiCanon_covers_quad {φ : (Fin 21 → ℝ) → (Fin 21 → ℝ)} (keep : Fin 21 → Prop)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin 21 → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v)
    (hb : ∀ x : Fin 21 → ℝ, ‖x‖ ≤ leafR → ‖φ x‖ ≤ 2 * leafR ^ 2) :
    closedBall (0 : Fin 21 → ℝ) leafR ⊆ blockShear φ '' closedBall 0 (leafR + 2 * leafR ^ 3) :=
  OverVanishCanon334.blockShear_covers_cubic keep hkeep hread
    (fun x hx => (hb x hx).trans (by nlinarith [leafR_ge_one]))

/-- **Every base-type straightening covers** `closedBall 0 leafR` into its inflated ball (cubic
straightening → the bare `psiCanon_cubic_cover`; quadratic straightening → `psiCanon_covers_quad`). -/
theorem bundleOf_psi_covers (q r : Fin 21) :
    closedBall (0 : Fin 21 → ℝ) leafR ⊆ (bundleOf q r).psi '' closedBall 0 (leafR + 2 * leafR ^ 3) := by
  simp only [bundleOf, mkBundle]
  split_ifs <;>
    first
      | exact OverVanishCanon334.psiCanon_cubic_cover leafR_ge_one
      | exact OverVanishA_20_1_6.psiCanon_cubic_cover leafR_ge_one
      | exact OverVanishA_20_1_7.psiCanon_cubic_cover leafR_ge_one
      | exact OverVanishA_20_5_5.psiCanon_cubic_cover leafR_ge_one
      | exact OverVanishA_20_5_6.psiCanon_cubic_cover leafR_ge_one
      | exact OverVanishA_20_5_7.psiCanon_cubic_cover leafR_ge_one
      | exact OverVanishB_20_6_1.psiCanon_cubic_cover leafR_ge_one
      | exact OverVanishB_20_6_5.psiCanon_cubic_cover leafR_ge_one
      | exact OverVanishB_20_6_6.psiCanon_cubic_cover leafR_ge_one
      | exact OverVanishB_20_7_1.psiCanon_cubic_cover leafR_ge_one
      | exact OverVanishB_20_7_5.psiCanon_cubic_cover leafR_ge_one
      | exact OverVanishB_20_7_7.psiCanon_cubic_cover leafR_ge_one
      | exact psiCanon_covers_quad OverVanishA_20_1_5.keepCanon OverVanishA_20_1_5.phiCanon_keep
          OverVanishA_20_1_5.phiCanon_read (fun x hx => OverVanishA_20_1_5.phiCanon_norm_bound hx)
      | exact psiCanon_covers_quad OverVanishA_20_5_1.keepCanon OverVanishA_20_5_1.phiCanon_keep
          OverVanishA_20_5_1.phiCanon_read (fun x hx => OverVanishA_20_5_1.phiCanon_norm_bound hx)
      | exact psiCanon_covers_quad OverVanishB_20_6_7.keepCanon OverVanishB_20_6_7.phiCanon_keep
          OverVanishB_20_6_7.phiCanon_read
          (fun x hx => OverVanishB_20_6_7.phiCanon_norm_bound leafR_nonneg hx)
      | exact psiCanon_covers_quad OverVanishB_20_7_6.keepCanon OverVanishB_20_7_6.phiCanon_keep
          OverVanishB_20_7_6.phiCanon_read
          (fun x hx => OverVanishB_20_7_6.phiCanon_norm_bound leafR_nonneg hx)

/-- **The folding shear covers** `closedBall 0 leafR` into `domFold`'s ball, for every chart (identity
on clean; the σ-conjugate of a covering straightening on over-vanishing). -/
theorem psiOf_covers (c : Fin numCharts) :
    closedBall (0 : Fin 21 → ℝ) leafR ⊆ psiOf c '' closedBall 0 (leafR + 2 * leafR ^ 3) := by
  unfold psiOf
  split_ifs with h
  · rw [Set.image_id]
    exact closedBall_subset_closedBall (by have := pow_nonneg leafR_nonneg 3; linarith)
  · have hR : (0 : ℝ) ≤ leafR + 2 * leafR ^ 3 := by
      have := pow_nonneg leafR_nonneg 3; have := leafR_nonneg; linarith
    exact conjChart_covers _ leafR_nonneg hR (bundleOf_psi_covers (canonQ c) (canonR c))

/-- **Each leaf's unfolded image sits inside its folded image** — `gFin c '' domFin c ⊆ gFold c ''
domFold c` (fold `psiOf c` into the chart; it covers, so the image only grows). -/
theorem gFin_image_subset_gFold (c : Fin numCharts) :
    gFin c '' domFin c ⊆ gFold c '' domFold c := by
  have h1 : gFin c '' domFin c ⊆ gFin c '' (psiOf c '' closedBall 0 (leafR + 2 * leafR ^ 3)) :=
    Set.image_mono (psiOf_covers c)
  rw [show domFin c = closedBall (0 : Fin 21 → ℝ) leafR from rfl] at *
  refine h1.trans ?_
  rw [← Set.image_comp]
  exact subset_of_eq rfl

/-- **The folded cover** — `native_hcover` transported through the fold: the folded images cover at
least what the unfolded ones do, so the uncovered set only shrinks (a fortiori stays null). -/
theorem folded_hcover :
    volume (ball (0 : Fin 21 → ℝ) 1 \ ⋃ c, gFold c '' domFold c) = 0 := by
  refine measure_mono_null (Set.diff_subset_diff_right ?_) native_hcover
  exact Set.iUnion_mono (fun c => gFin_image_subset_gFold c)

/-! ## §2.7 — the coordinate-conjugation transport of the Jacobian (shared by ainj + hint) -/

/-- **The Jacobian weight reindexes under a coordinate permutation.** `jacWeight h (u∘σ) = jacWeight
(h∘σ⁻¹) u` (the monomial exponent reindexes by `σ⁻¹`). -/
theorem jacWeight_reindex (σ : Equiv.Perm (Fin 21)) (h : Fin 21 → ℕ) (u : Fin 21 → ℝ) :
    jacWeight h (fun k ↦ u (σ k)) = jacWeight (fun d ↦ h (σ.symm d)) u := by
  simp only [jacWeight]
  rw [← Equiv.prod_comp σ (fun e ↦ |u e| ^ h (σ.symm e))]
  exact Finset.prod_congr rfl (fun d _ ↦ by rw [Equiv.symm_apply_apply])

/-- **The |jacDet| of a `conjChart`-conjugate transports.** `|jacDet (conjChart σ H) u| = |jacDet H
(u∘σ)|`: writing `conjChart σ H = R_{σ⁻¹} ∘ H ∘ R_σ` with `R_ρ w = w∘ρ` the coordinate reindexings
(each `|jacDet| = 1`, `abs_jacDet_permCoord`), the chain rule collapses the two reindex factors. -/
theorem jacDet_conjChart_abs (σ : Equiv.Perm (Fin 21)) {H : (Fin 21 → ℝ) → (Fin 21 → ℝ)}
    (hH : Differentiable ℝ H) (u : Fin 21 → ℝ) :
    |jacDet (OverVanishTransport334.conjChart σ H) u| = |jacDet H (fun k ↦ u (σ k))| := by
  have hRσ : Differentiable ℝ (fun w : Fin 21 → ℝ ↦ fun k ↦ w (σ k)) := differentiable_reindex σ
  have hRσs : Differentiable ℝ (fun v : Fin 21 → ℝ ↦ fun t ↦ v (σ.symm t)) :=
    differentiable_reindex σ.symm
  rw [show OverVanishTransport334.conjChart σ H
        = (fun v : Fin 21 → ℝ ↦ fun t ↦ v (σ.symm t)) ∘ (H ∘ (fun w : Fin 21 → ℝ ↦ fun k ↦ w (σ k)))
        from rfl,
    jacDet_comp u hRσs.differentiableAt (hH.comp hRσ).differentiableAt,
    jacDet_comp u hH.differentiableAt hRσ.differentiableAt, abs_mul, abs_mul,
    Corank2ChartJac.abs_jacDet_permCoord σ.symm, Corank2ChartJac.abs_jacDet_permCoord σ,
    one_mul, mul_one]

/-- **Each base type's folded Jacobian collapses to its monomial weight** (`bundleOf`'s carried
`hfoldedJac`, projected — no 16-way search). -/
theorem bundleOf_foldedJac (q r : Fin 21) (u : Fin 21 → ℝ) :
    |jacDet (gFlat (bundleOf q r).idxC ∘ (bundleOf q r).psi) u| = jacWeight (bundleOf q r).jac u :=
  (bundleOf q r).hfoldedJac u

/-- **Each base type's folded loss dominates its product germ** (`bundleOf`'s carried `hdom`). -/
theorem bundleOf_domination (q r : Fin 21) (u : Fin 21 → ℝ) :
    monoSumSqGerm (bundleOf q r).a (bundleOf q r).Z u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gFlat (bundleOf q r).idxC ∘ (bundleOf q r).psi)) u :=
  (bundleOf q r).hdom u

end DLNFibre.DLN.Aoyagi.OverVanishHeadline334
