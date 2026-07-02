import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenHmap
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenAmbient
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenCollapse
import DLNFibre.DLN.RLCT.Validate.RouteMRadialComp

/-!
# `RouteMInteriorLiveGenDetDecode` — layer (a) of the interior atom: `interiorLive_abs_det'Gen`

The general-`L` decode + assembly of the interior chart Jacobian abs-det into the single-axis monomial
the R1-LOWER leg consumes. The general-`L` lift of `RouteMBdetMonomial.interiorLive_BdetMonomial_of_hreg`
+ `RouteMInteriorLiveAtom.interiorLive_abs_det'` (both `Fin (2 + 1)`-pinned, boundary-`0`-only).

## The mathematics

The chart factors (MAP level) as `interiorLivePhiGen = (BchartLeafGen ∘ kLDU) ∘ pivotBlowupOn`
(`hmap_leafGen` + `interiorLive_commuteGen`). By the route-#1 radial split (`radialComp_abs_det_at`,
∀L, banked) its abs-det is `|u leafPivot|^{minAdm−1} · |det D(BchartLeafGen ∘ kLDU)(pbo u)|`. The
boundary-factor det `|det D(BchartLeafGen ∘ kLDU)(pbo u)|` splits (chain rule) into

  * **Factor 1** `|det D(BchartLeafGen)(kLDU(pbo u))| = ∏_s |det (readK (kLDU(pbo u)) s)|^{r_s + c_s}`
    (`DtotGen_abs_det`), and `readK (kLDU z) s = kLens (readK z s)` so `det = ∏_i (readK z s) i i`
    (`readK_kLDU` + `kLens_det`, `matrixSplit .2.1 = diagonal`); at `z = pbo u` the K-diagonal is
    pbo-fixed (`readK_pbo_allGen`), so the pivot is `u (diagAxisGen s i)`. Factor 1 folds to
    `∏_s |∏_i u (diagAxisGen s i)|^{r_s + c_s}`;
  * **Factor 2** `|det D(kLDU)(pbo u)| = ∏_k ∏_i |u (diagAxisGen k i)|^{2(t_k−1−i)}`
    (`kLDU_ambient_det_pbo_gen`).

The multi-boundary collapse (`lhs_collapse_multiboundary`) merges them per pivot to
`∏_s ∏_i |u (diagAxisGen s i)|^{(r_s+c_s)+2(t_s−1−i)}`; the per-pivot exponent IS
`interiorLive_leafHGen (diagAxisGen s i)` (`leafHGen_diagAxisGen`), so the double product is
`∏_{p : Σ s, Fin t_s} g (diagAxisGen p.1 p.2)` with `g j := |u j|^{leafHGen j}`; the injective Sigma
reindex `diagAxisSigmaGen` + the off-image collapse (`mem_image_diagAxisSigma_of_leafHGen_ne_zero`,
every nonzero-`leafHGen` non-pivot axis IS a diagonal K-axis) recover `∏_{j ≠ leafPivot} g j`. The
radial `|u leafPivot|^{minAdm−1}` fills the pivot slot (`leafHGen_pivot`), giving `∏_j g j`.

## Deliverables

* `diagAxisSigmaGen` / `diagAxisSigmaGen_injective` — the Sigma-indexed diagonal K-axis + injectivity.
* `diagAxisGen_ne_leafPivot` — a diagonal K-axis is never the leaf pivot.
* `leafHGen_diagAxisGen` — `leafHGen (diagAxisGen k i) = (r_k+c_k)+2(t_k−1−i)`.
* `mem_image_diagAxisSigma_of_leafHGen_ne_zero` — the off-image collapse.
* `Dtot_kLDU_abs_det_split` — the chain-rule split (boundary factor × ambient lens).
* `interiorLive_BdetMonomialGen` — `|det D(BchartLeafGen ∘ kLDU)(pbo u)| = ∏_{j ≠ leafPivot} |u_j|^{leafHGen j}`.
* `interiorLive_abs_det'Gen` — the headline: `|det (fderiv interiorLivePhiGen u)| = ∏_j |u_j|^{leafHGen j}`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + finite products; no analysis beyond
the banked chain rule + determinant folds). Layer (a) of the interior atom.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The Sigma-indexed diagonal K-axis + its combinatorics -/

/-- **The Sigma-indexed diagonal K-axis** `⟨k, i⟩ ↦ diagAxisGen k i` — the flat coordinate reading
`readK · k i i` at boundary `k`, diagonal index `i`. The domain `Σ k : Fin L, Fin (Text(k+2))` runs
over ALL interior boundaries' diagonal pivots (the general-`L` lift of the boundary-0-only L=2
`diagAxis`). -/
noncomputable def diagAxisSigmaGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    (Σ k : Fin L, Fin (Text M (tach M) (k.val + 2))) → Fin (routeMAmbient M) :=
  fun p => diagAxisGen M ha p.1 p.2

/-- **`diagAxisSigmaGen` is injective** — `chartIdxEquiv.symm` injective forces equal boundary tags
(`Sigma.mk.inj_iff`), then `frameSplitEquiv.symm` + `finProdFinEquiv` injective force equal diagonal
indices. The general-`L` lift of `diagAxis_injective` (whose domain was the single boundary 0). -/
theorem diagAxisSigmaGen_injective (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    Function.Injective (diagAxisSigmaGen M ha) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ hij
  simp only [diagAxisSigmaGen, diagAxisGen, readKslot] at hij
  have h1 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hij
  rw [Sigma.mk.inj_iff] at h1
  -- boundary tags equal
  obtain ⟨hk, htag⟩ := h1
  subst hk
  -- frame tags equal (heq collapses since the boundary is fixed)
  have htag' := eq_of_heq htag
  have h2 := (frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt)
    (ha.hub k.val)).symm.injective ((Sum.inl.injEq _ _).mp htag')
  have h3 := finProdFinEquiv.injective
    ((Sum.inl.injEq _ _).mp ((Sum.inl.injEq _ _).mp ((Sum.inl.injEq _ _).mp h2)))
  -- `(i, i) = (i', i')` ⟹ `i = i'`
  have : i = i' := (Prod.mk.injEq .. ▸ h3).1
  subst this
  rfl

/-- **A diagonal K-axis is never the leaf pivot** — `diagAxisGen k i = readKslot k i i` sits at
boundary tag `k` with a frame K-tag; the leaf pivot is a leaf slot at boundary `L−1` with an
incompatible tag. Direct from the banked `readKslot_ne_leafPivot` (which handles ALL boundaries,
leaf included — at the leaf `Fin (Text(L+1)) = Fin 0` is empty). -/
theorem diagAxisGen_ne_leafPivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (k : Fin L)
    (i : Fin (Text M (tach M) (k.val + 2))) :
    diagAxisGen M ha k i ≠ leafPivot M ha hL h0r h0c := by
  rw [diagAxisGen]
  exact readKslot_ne_leafPivot M ha hL h0r h0c k i i

/-- **`leafHGen` at a diagonal K-axis** — `interiorLive_leafHGen (diagAxisGen k i) =
(r_k+c_k) + 2(t_k−1−i)`. The `if j = leafPivot` is `false` (`diagAxisGen_ne_leafPivot`); the
`chartIdxEquiv` round-trip on `diagAxisGen k i` exposes the boundary-`k` K-slot tag, the
`frameSplitEquiv`/`finProdFinEquiv` round-trips collapse, and the diagonal `i = i` fires `if_pos`.
The general-`L` lift of `RouteMBdetMonomial.leafH_diagAxis`. -/
theorem leafHGen_diagAxisGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (k : Fin L)
    (i : Fin (Text M (tach M) (k.val + 2))) :
    interiorLive_leafHGen M ha hL h0r h0c (diagAxisGen M ha k i)
      = (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
        + (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
        + 2 * (Text M (tach M) (k.val + 2) - 1 - (i : ℕ)) := by
  rw [interiorLive_leafHGen, if_neg (diagAxisGen_ne_leafPivot M ha hL h0r h0c k i)]
  rw [diagAxisGen, readKslot, Equiv.apply_symm_apply, liveLeafHOnIdxGen]
  simp only [Equiv.apply_symm_apply, finProdFinEquiv.symm_apply_apply]
  rfl

/-- **The off-image collapse** — a non-pivot axis with nonzero `leafHGen` IS a diagonal K-axis. The
only nonzero `liveLeafHOnIdxGen` slots are boundary-`k` K-role diagonal entries; the corresponding
`⟨k, i⟩` sits in the image of `diagAxisSigmaGen`. The general-`L` lift of
`RouteMBdetMonomial.mem_image_diagAxis_of_leafH_ne_zero` — now the image is over ALL boundaries `k`
(no `k = 0` collapse), so the diagonal `⟨k, (finProdFinEquiv.symm qK).1⟩` is exhibited directly. -/
theorem mem_image_diagAxisSigma_of_leafHGen_ne_zero (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hL : 0 < L) (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (j : Fin (routeMAmbient M))
    (hjp : j ≠ leafPivot M ha hL h0r h0c) (hne : interiorLive_leafHGen M ha hL h0r h0c j ≠ 0) :
    j ∈ Finset.image (diagAxisSigmaGen M ha) Finset.univ := by
  rw [interiorLive_leafHGen, if_neg hjp] at hne
  have hjq : j = (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
      (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL j) := by
    rw [Equiv.symm_apply_apply]
  match hc : chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL j with
  | ⟨k, Sum.inr s⟩ => rw [hc] at hne; simp only [liveLeafHOnIdxGen] at hne; exact absurd rfl hne
  | ⟨k, Sum.inl s⟩ =>
    rw [hc] at hne; simp only [liveLeafHOnIdxGen] at hne
    match hfeq : frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>
      rw [hfeq] at hne; simp only at hne
      by_cases hdiag : (finProdFinEquiv.symm qK).1 = (finProdFinEquiv.symm qK).2
      · refine Finset.mem_image.mpr ⟨⟨k, (finProdFinEquiv.symm qK).1⟩, Finset.mem_univ _, ?_⟩
        -- `diagAxisSigmaGen ⟨k, i⟩ = j`: peel chartIdxEquiv.symm, frameSplitEquiv.symm, finProd.
        have hs : s = (frameSplitEquiv M (tach M) (k.val + 1)
            (ha.hdesc k.val k.isLt) (ha.hub k.val)).symm
              (Sum.inl (Sum.inl (Sum.inl qK))) := by rw [← hfeq, Equiv.symm_apply_apply]
        have hqK : finProdFinEquiv ((finProdFinEquiv.symm qK).1, (finProdFinEquiv.symm qK).1) = qK := by
          nth_rewrite 2 [hdiag]
          rw [Prod.mk.eta, finProdFinEquiv.apply_symm_apply]
        rw [diagAxisSigmaGen, diagAxisGen, readKslot, hjq, hc, hs, hqK]
      · rw [if_neg hdiag] at hne; exact absurd rfl hne
    | Sum.inl (Sum.inl (Sum.inr e)) => rw [hfeq] at hne; simp only at hne; exact absurd rfl hne
    | Sum.inl (Sum.inr e) => rw [hfeq] at hne; simp only at hne; exact absurd rfl hne
    | Sum.inr e => rw [hfeq] at hne; simp only at hne; exact absurd rfl hne

/-! ## The chain-rule split + Factor-1 fold -/

/-- **The chain-rule split** — `|det D(BchartLeafGen ∘ kLDU)(x)| = |det D(BchartLeafGen)(kLDU x)| ·
|det D(kLDU)(x)|`. `fderiv_comp` + `LinearMap.det_comp` + `abs_mul`. The general-`L` lift of
`RouteMBdetMonomial.BchartLeaf_kLDU_abs_det_split`. -/
theorem Dtot_kLDU_abs_det_split (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (x : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (fun y => BchartLeafGen M ha (kLDU M (tach M) ha y)) x).toLinearMap|
      = |LinearMap.det (fderiv ℝ (BchartLeafGen M ha) (kLDU M (tach M) ha x)).toLinearMap|
        * |LinearMap.det (fderiv ℝ (kLDU M (tach M) ha) x).toLinearMap| := by
  have hcomp : (fun y => BchartLeafGen M ha (kLDU M (tach M) ha y))
      = BchartLeafGen M ha ∘ kLDU M (tach M) ha := rfl
  rw [hcomp, fderiv_comp x (Bchart_differentiableAtGen M ha _)
    (differentiable_kLDUGen M (tach M) ha x)]
  rw [ContinuousLinearMap.coe_comp, LinearMap.det_comp, abs_mul]

/-- **Factor 1 at `kLDU(pbo u)`, folded** — `|det D(BchartLeafGen)(kLDU(pbo u))| =
∏_s |∏_i u (diagAxisGen s i)|^{r_s + c_s}`. From the free-`y₀` staircase det `DtotGen_abs_det`
(unconditional), with `det (readK (kLDU(pbo u)) s) = ∏_i (readK (pbo u) s) i i = ∏_i u (diagAxisGen s i)`
(`readK_kLDU` + `kLens_det` + `matrixSplit .2.1 = diagonal` (defeq) + `readK_pbo_allGen`). -/
theorem Dtot_factor1_pbo (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (BchartLeafGen M ha)
        (kLDU M (tach M) ha
          (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) u))).toLinearMap|
      = ∏ s : Fin L, |∏ i, u (diagAxisGen M ha s i)|
          ^ ((Text M (tach M) (s.val + 1) - Text M (tach M) (s.val + 2))
            + (Wext M (s.val + 1) - Text M (tach M) (s.val + 2))) := by
  set z := pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) u with hz
  -- `DtotGen ha (kLDU z) := (fderiv (BchartLeafGen ha) (kLDU z)).toLinearMap`, so its abs-det is Factor 1.
  have hDtot : |LinearMap.det (fderiv ℝ (BchartLeafGen M ha) (kLDU M (tach M) ha z)).toLinearMap|
      = |LinearMap.det (DtotGen M ha (kLDU M (tach M) ha z))| := rfl
  rw [hDtot, DtotGen_abs_det M ha (kLDU M (tach M) ha z)]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  congr 1
  -- `det (readK (kLDU z) s) = ∏_i u (diagAxisGen s i)`
  have hK : (Matrix.of (readK M (tach M) ha (kLDU M (tach M) ha z) s))
      = kLens (Matrix.of (readK M (tach M) ha z s)) := by
    ext i j
    rw [Matrix.of_apply, readK_kLDU]
    rfl
  rw [hK, kLens_det]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  -- `(matrixSplit (readK z s)).2.1 i = readK z s i i = readK u s i i = u (diagAxisGen s i)`
  -- (`matrixSplit .2.1 = diagonal` DEFEQ, then the pbo-fix `readK_pbo_allGen`).
  show (Matrix.of (readK M (tach M) ha z s)) i i = u (diagAxisGen M ha s i)
  rw [Matrix.of_apply, u_diagAxisGen M ha u s i, hz]
  exact readK_pbo_allGen M ha hL h0r h0c u s i i

/-! ## The boundary-factor det monomializes -/

/-- **The boundary-factor det monomializes** —
`|det D(BchartLeafGen ∘ kLDU)(pbo u)| = ∏_{j ≠ leafPivot} |u_j|^{leafHGen j}`. The chain-rule split
(`Dtot_kLDU_abs_det_split`) factors into Factor 1 (`Dtot_factor1_pbo`) and Factor 2
(`kLDU_ambient_det_pbo_gen`); `lhs_collapse_multiboundary` merges them per pivot to
`∏_s ∏_i |u (diagAxisGen s i)|^{leafHGen (diagAxisGen s i)}`; the Sigma reindex (`prod_sigma'` +
`prod_image` via `diagAxisSigmaGen_injective`) + off-image `prod_subset`
(`mem_image_diagAxisSigma_of_leafHGen_ne_zero`) recover `∏_{j ≠ leafPivot}`. Unconditional (no `hreg`
— `DtotGen_abs_det` already discharged the regauge). The general-`L` lift of
`RouteMBdetMonomial.interiorLive_BdetMonomial_of_hreg`. -/
theorem interiorLive_BdetMonomialGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (fun y => BchartLeafGen M ha (kLDU M (tach M) ha y))
        (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) u)).toLinearMap|
      = ∏ j, if j = leafPivot M ha hL h0r h0c then (1 : ℝ)
          else |u j| ^ (interiorLive_leafHGen M ha hL h0r h0c j) := by
  set p₀ := leafPivot M ha hL h0r h0c with hp₀
  -- split + Factor 1 + Factor 2 + collapse.  The block widths are passed in the RAW `Text`/`Wext`
  -- form the two factors produce, so the `lhs_collapse_multiboundary` pattern matches syntactically.
  rw [Dtot_kLDU_abs_det_split M ha, Dtot_factor1_pbo M ha hL h0r h0c u,
    kLDU_ambient_det_pbo_gen M ha hL h0r h0c u,
    lhs_collapse_multiboundary (fun s => Text M (tach M) (s.val + 2))
      (fun s => Text M (tach M) (s.val + 1) - Text M (tach M) (s.val + 2))
      (fun s => Wext M (s.val + 1) - Text M (tach M) (s.val + 2))
      (fun s => fun i => u (diagAxisGen M ha s i))]
  -- per-pivot exponent = `leafHGen (diagAxisGen s i)`
  have hexp : ∀ (s : Fin L) (i : Fin (Text M (tach M) (s.val + 2))),
      |u (diagAxisGen M ha s i)|
        ^ (((Text M (tach M) (s.val + 1) - Text M (tach M) (s.val + 2))
              + (Wext M (s.val + 1) - Text M (tach M) (s.val + 2)))
          + 2 * ((Text M (tach M) (s.val + 2) : ℕ) - 1 - (i : ℕ)))
        = |u (diagAxisGen M ha s i)| ^ (interiorLive_leafHGen M ha hL h0r h0c (diagAxisGen M ha s i)) := by
    intro s i
    rw [leafHGen_diagAxisGen M ha hL h0r h0c s i]
  rw [Finset.prod_congr rfl (fun s _ => Finset.prod_congr rfl (fun i _ => hexp s i))]
  -- LHS = `∏_s ∏_i g (diagAxisGen s i)`, RHS = `∏_j if j = p₀ then 1 else g j`, with `g j := |u j|^{leafHGen j}`.
  let g : Fin (routeMAmbient M) → ℝ := fun j => |u j| ^ (interiorLive_leafHGen M ha hL h0r h0c j)
  show ∏ s : Fin L, ∏ i, g (diagAxisGen M ha s i) = ∏ j, if j = p₀ then (1 : ℝ) else g j
  -- fold the double product to the Sigma product
  rw [← Fintype.prod_sigma' (fun s i => g (diagAxisGen M ha s i))]
  -- RHS: split the pivot off and collapse the `if`.
  have hRHS : (∏ j, if j = p₀ then (1 : ℝ) else g j)
      = ∏ j ∈ (Finset.univ : Finset (Fin (routeMAmbient M))).erase p₀, g j := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => if j = p₀ then (1 : ℝ) else g j)
      (Finset.mem_univ p₀), if_pos rfl, one_mul]
    exact Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))
  -- LHS: reindex through the injective Sigma image, then grow to `erase p₀`.
  have hLHS : (∏ p : (Σ k : Fin L, Fin (Text M (tach M) (k.val + 2))), g (diagAxisGen M ha p.1 p.2))
      = ∏ j ∈ (Finset.univ : Finset (Fin (routeMAmbient M))).erase p₀, g j := by
    rw [show (∏ p : (Σ k : Fin L, Fin (Text M (tach M) (k.val + 2))), g (diagAxisGen M ha p.1 p.2))
        = ∏ p : (Σ k : Fin L, Fin (Text M (tach M) (k.val + 2))), g (diagAxisSigmaGen M ha p) from rfl]
    rw [← Finset.prod_image (g := diagAxisSigmaGen M ha) (f := g)
      ((diagAxisSigmaGen_injective M ha).injOn)]
    refine Finset.prod_subset ?_ ?_
    · intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨⟨k, i⟩, _, rfl⟩ := hj
      exact Finset.mem_erase.mpr
        ⟨diagAxisGen_ne_leafPivot M ha hL h0r h0c k i, Finset.mem_univ _⟩
    · intro j hj hjimg
      have hjp : j ≠ p₀ := (Finset.mem_erase.mp hj).1
      have hz : interiorLive_leafHGen M ha hL h0r h0c j = 0 := by
        by_contra hne
        exact hjimg (mem_image_diagAxisSigma_of_leafHGen_ne_zero M ha hL h0r h0c j hjp hne)
      show g j = 1
      simp only [g]; rw [hz, pow_zero]
  rw [hLHS, hRHS]

/-! ## The headline: `interiorLive_abs_det'Gen` -/

/-- **`interiorLive_abs_det'Gen`** — the interior chart Jacobian abs-det is the single-axis monomial
`∏_j |u_j|^{leafHGen j}` (the R1-LOWER leg's target). The chart factors (MAP) as
`interiorLivePhiGen = (BchartLeafGen ∘ kLDU) ∘ pivotBlowupOn` (`hmap_leafGen` +
`interiorLive_commuteGen`); the route-#1 radial split (`radialComp_abs_det_at`) gives
`|u leafPivot|^{minAdm−1} · |det D(BchartLeafGen ∘ kLDU)(pbo u)|`, and the boundary factor
monomializes (`interiorLive_BdetMonomialGen`) to `∏_{j ≠ leafPivot} |u_j|^{leafHGen j}`; the radial
`|u leafPivot|^{minAdm−1} = |u leafPivot|^{leafHGen leafPivot}` (`leafHGen_pivot`) fills the pivot slot.
The general-`L` lift of `RouteMInteriorLiveAtom.interiorLive_abs_det'`. -/
theorem interiorLive_abs_det'Gen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (interiorLivePhiGen M ha hL h0r h0c) u).toLinearMap|
      = ∏ j, |u j| ^ (interiorLive_leafHGen M ha hL h0r h0c j) := by
  set p₀ := leafPivot M ha hL h0r h0c with hp₀
  set B' := fun y => BchartLeafGen M ha (kLDU M (tach M) ha y) with hB'
  -- MAP factorization: `interiorLivePhiGen = B' ∘ pivotBlowupOn activeMGen p₀`
  have hmap : interiorLivePhiGen M ha hL h0r h0c
      = B' ∘ pivotBlowupOn (activeMGen M ha) p₀ := by
    funext x
    rw [interiorLivePhiGen, hmap_leafGen M ha hL h0r h0c]
    show BchartLeafGen M ha (pivotBlowupOn (activeMGen M ha) p₀ (kLDU M (tach M) ha x)) = _
    rw [interiorLive_commuteGen M ha hL h0r h0c x]; rfl
  -- `B'` has an fderiv at `pbo u`
  have hasDB' : HasFDerivAt B'
      (fderiv ℝ B' (pivotBlowupOn (activeMGen M ha) p₀ u))
      (pivotBlowupOn (activeMGen M ha) p₀ u) :=
    ((Bchart_differentiableAtGen M ha _).comp _
      (differentiable_kLDUGen M (tach M) ha _)).hasFDerivAt
  rw [radialComp_abs_det_at M (activeMGen M ha) p₀ (leafPivotGen_mem_activeMGen M ha hL h0r h0c)
    (activeMGen_card M ha) B' (interiorLivePhiGen M ha hL h0r h0c) u _ hmap hasDB',
    interiorLive_BdetMonomialGen M ha hL h0r h0c u]
  -- |u p₀|^{minAdm−1} · ∏(if j=p₀ then 1 else |u j|^{leafHGen j}) = ∏ |u j|^{leafHGen j}
  conv_rhs => rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ p₀)
    (fun j => |u j| ^ (interiorLive_leafHGen M ha hL h0r h0c j))]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ p₀)
    (fun j => if j = p₀ then (1 : ℝ) else |u j| ^ (interiorLive_leafHGen M ha hL h0r h0c j))]
  rw [if_pos rfl, one_mul, interiorLive_leafHGen_pivot M ha hL h0r h0c]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [if_neg (by simp at hj; exact hj : j ≠ p₀)]

end DLNFibre.DLN.RLCT
