import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Validate.RouteMKLens
import DLNFibre.DLN.RLCT.Validate.RouteMLeafChart
import DLNFibre.DLN.RLCT.Validate.RouteMLeafHeadline
import DLNFibre.DLN.RLCT.Validate.RouteMLeafBData
import DLNFibre.DLN.RLCT.Validate.RouteMNullSliceCov
import DLNFibre.DLN.RLCT.Validate.RouteMFactorMaps
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior

/-!
# `RouteMInteriorLiveContract` — the LIVE-leaf ∘ kLDU interior achiever box-divergence (SPECIFY)

The CORRECT interior-branch achiever chart for the ∀M-L2 R1-LOWER leg: the **LIVE-leaf** chart
`phiFlatLiveAt` (with the `rfinFixedPivot` `(0,0)=1` anchor that makes it INJECTIVE — the dead-leaf
`genBlkFlatStruct` of `RouteMInteriorLDUContract` is provably NON-INJECTIVE, genm-hinj) **precomposed
with the K-slot LDU lens `kLDU`** (which monomializes the polynomial frame det `|det K|^{r+c}` into the
diagonal-pivot product, the `RouteMFlatLDU` wall-check fix). The binding pivot is `leafPivot`, NOT the
`structPivot = ⟨0⟩` of the dead-leaf contract.

## The double-count-free factorization (Codex xhigh verdict, `codex/livekldu-fork-answer.md`)

Chain-ruling through `kLDU` TWICE would square the K-pivot. AVOIDED by pushing `kLDU` into the
boundary factor. `radialComp_abs_det_at` is generic in `B`; set `B' := BchartLeaf ha ∘ kLDU`. Then the
single map identity `phiFlatLiveAt … leafPivot (kLDU x) = B' (pivotBlowupOn activeM leafPivot x)` makes
the headline fire ONCE: `|det Dφ| = |u_{leafPivot}|^{minAdm−1}·|det DB'|`. The map identity reduces to a
COMMUTE fact (source-verified): `activeM = {E-block ∪ leaf slots}` (NO K), `kLDU` touches ONLY K, so
`pivotBlowupOn activeM leafPivot ∘ kLDU = kLDU ∘ pivotBlowupOn activeM leafPivot` (disjoint coords),
and `hmap_leaf` fires at the point `kLDU x`.

## Banked infrastructure consumed

* RATE: `phiFlatLiveAt_rate` (∀M, any reparam; reads the radial from `x p₀`; `(kLDU x) leafPivot =
  x leafPivot` since `kLDU` skips leaf slots). banked.
* HEADLINE: `interiorDet_leaf_headline` (`|det D(phiFlatLiveAt)| = |u p₀|^{minAdm−1}·|det DB|`, generic
  `B`/`DB`/`hmap`/`hasDB`). banked.
* MAP id: `hmap_leaf` (`phiFlatLiveAt = BchartLeaf ∘ pivotBlowupOn activeM leafPivot`). banked.
* K-LDU monomial: `readK_kLDU_det`, `kLens_det`, the `read*_kLDU` pass-through. banked.
* COV engine: `ldu_cov_of_differentiable_injOn` (takes `hdiff`/`habsdet`/`hinj`). banked.
* THRESHOLD: `nodeChart_thresholdLe` (`leafH p = minAdm−1` ⟹ `≤ ½·minAdm`). banked.

## Open obligations (each a stated `sorry`, mapped to an H-sub-task)

* `interiorLive_commute` — `pivotBlowupOn activeM leafPivot (kLDU x) = kLDU (pivotBlowupOn …)` (the
  disjoint-coords commute; the load-bearing map fact).
* `interiorLive_leafH` (def, H2) — the multi-axis exponent vector, with `leafH leafPivot = minAdm−1`.
* `interiorLive_abs_det` (H2) — `|det Dφ| = ∏_j |u_j|^{leafH j}` (headline ∘ kLDU monomial).
* `interiorLive_diff` — `Differentiable ℝ (interiorLivePhi)` (polynomial chain).
* `interiorLive_injOn` (H-inj) — `InjOn` off the pivot ∪ q-axes (factors through the composition).
* `interiorLive_Ubound`, `interiorLive_Umeas`, `interiorLive_image` (H1-internal).

The TOP result `routeMCore_box_diverges_interiorLive` is the interior `BoxDiverges` atom the dispatch
spine's `hInterior` consumes. NOT axiom-clean yet (carries the listed `sorry`s). The dead-leaf
`RouteMInteriorLDUContract` is RETIRED in favour of this.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {M : Fin (2 + 1) → ℕ}

/-! ## The LIVE-leaf ∘ kLDU interior chart -/

/-- **The LIVE-leaf ∘ kLDU interior achiever chart** `phiFlatLiveAt M ha leafPivot (kLDU x)` — the
injective live-leaf chart with the K-slots LDU-straightened so the frame det is a monomial. -/
noncomputable def interiorLivePhi (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  fun x => phiFlatLiveAt M ha (by norm_num) (leafPivot M ha (by norm_num) h0r h0c)
    (kLDU M (tach M) ha x)

/-- **The LIVE-leaf ∘ kLDU unit factor** — the radial quotient `routeMCore(φ x)/(x leafPivot)²`. -/
noncomputable def interiorLiveUnit (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    (Fin (routeMAmbient M) → ℝ) → ℝ :=
  fun x => VvalGen (x (leafPivot M ha (by norm_num) h0r h0c)) M (tach M)
    (genBlkFlatLive M (tach M) ha
      (rfinFixedPivot M ha (by norm_num) (kLDU M (tach M) ha x)) (kLDU M (tach M) ha x))
    (hleStruct M (tach M) ha)

/-- **`(kLDU x) leafPivot = x leafPivot`** — the radial axis survives `kLDU` (a leaf slot, not a
K-slot; `kLDU` is identity off K-slots). The leaf pivot `leafPivot = leafSlot…0 0` decodes via
`chartIdxEquiv` to the Schur slot at boundary `L−1 = 1`; the kLDU K-arm at boundary `k = 1` reads the
K-core `readK x 1 : Matrix (Fin (Text 3)) …` which is `0×0` (`Text 3 = 0` at `L = 2`), so the K-arm is
vacuous and the leaf slot falls through `kLDU`'s identity branch. -/
theorem kLDU_leafPivot (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (x : Fin (routeMAmbient M) → ℝ) :
    (kLDU M (tach M) ha x) (leafPivot M ha (by norm_num) h0r h0c)
      = x (leafPivot M ha (by norm_num) h0r h0c) := by
  rw [kLDU, leafPivot, leafSlot]
  simp only [Equiv.apply_symm_apply]
  have hT3 : Text M (tach M) 3 = 0 := by
    have := Text_Lsucc_eq_zero M (by norm_num : 0 < 2); simpa using this
  split
  · -- K-arm: `qK : Fin (Text 3 · Text 3) = Fin 0` is uninhabited (the leaf boundary's K-block is `0×0`)
    rename_i qK _
    have hz : Text M (tach M) ((⟨2 - 1, by norm_num⟩ : Fin 2).val + 1 + 1)
          * Text M (tach M) ((⟨2 - 1, by norm_num⟩ : Fin 2).val + 1 + 1) = 0 := by
      show Text M (tach M) 3 * Text M (tach M) 3 = 0
      rw [hT3, Nat.mul_zero]
    exact (Fin.cast hz qK).elim0
  · rfl

/-- **The rate of the LIVE-leaf ∘ kLDU chart ∀M** (banked, NO bridge): `routeMCore M (φ x) =
(x leafPivot)² · interiorLiveUnit x`. The radial axis survives `kLDU` (`kLDU_leafPivot`), so
`phiFlatLiveAt_rate` at the point `kLDU x` transfers verbatim. -/
theorem routeMCore_interiorLivePhi (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (interiorLivePhi ha h0r h0c x)
      = (x (leafPivot M ha (by norm_num) h0r h0c)) ^ 2 * interiorLiveUnit ha h0r h0c x := by
  rw [interiorLivePhi, phiFlatLiveAt_rate M ha (by norm_num)
    (leafPivot M ha (by norm_num) h0r h0c) (kLDU M (tach M) ha x), kLDU_leafPivot ha h0r h0c x]
  rfl  -- `interiorLiveUnit x` is, by def, the `VvalGen … (kLDU x)` the rate produces

/-- `0 ≤ interiorLiveUnit` (sum of squares, banked `VvalGen_nonneg`). -/
theorem interiorLiveUnit_nonneg (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (x : Fin (routeMAmbient M) → ℝ) :
    0 ≤ interiorLiveUnit ha h0r h0c x :=
  VvalGen_nonneg _ M (tach M) _ _

/-! ## Differentiability atoms (the `kLens` / `kLDU` / `pivotBlowupOn` polynomial chain) -/

/-- **`kLens` is differentiable** — `matrixSplit.symm ∘ lduCoreMap ∘ matrixSplit`, the LinearEquivs
smooth and `lduCoreMap` with fderiv everywhere (`lduCoreMap_hasFDerivAt`). -/
theorem differentiable_kLens {t : ℕ} : Differentiable ℝ (kLens (t := t)) := by
  have hlduc : Differentiable ℝ (lduCoreMap (t := t)) :=
    fun z => (lduCoreMap_hasFDerivAt z).differentiableAt
  intro K
  unfold kLens
  exact (matrixSplit.symm.toContinuousLinearEquiv.differentiable _).comp K
    ((hlduc _).comp K (matrixSplit.toContinuousLinearEquiv.differentiable K))

/-- **`kLDU` is differentiable** — per coordinate: the K-arm is `kLens ∘ (linear K-read)`, the identity
arm is a coordinate projection. -/
theorem differentiable_kLDU {L : ℕ} (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) :
    Differentiable ℝ (kLDU M t ha) := by
  apply differentiable_pi.mpr
  intro q
  unfold kLDU
  split
  · rename_i k s heq
    split
    · rename_i qK hfeq
      have hrk : Differentiable ℝ
          (fun x : Fin (routeMAmbient M) → ℝ => Matrix.of (readK M t ha x k)) := by
        apply differentiable_pi.mpr; intro i; apply differentiable_pi.mpr; intro j
        exact differentiable_apply _
      have hcomp : Differentiable ℝ
          (fun x : Fin (routeMAmbient M) → ℝ => kLens (Matrix.of (readK M t ha x k))) :=
        fun x => (differentiable_kLens _).comp x (hrk x)
      exact differentiable_pi.mp (differentiable_pi.mp hcomp (finProdFinEquiv.symm qK).1)
        (finProdFinEquiv.symm qK).2
    · exact differentiable_apply _
  · exact differentiable_apply _

/-- **`pivotBlowupOn` is differentiable** (`pivotBlowupOn_hasFDerivWithinAt` on `Set.univ`). -/
theorem differentiable_pivotBlowupOn {N : ℕ} (active : Finset (Fin N)) (p : Fin N) :
    Differentiable ℝ (pivotBlowupOn active p) :=
  fun x => (hasFDerivWithinAt_univ.mp
    (pivotBlowupOn_hasFDerivWithinAt active p Set.univ x)).differentiableAt

/-! ## The commute fact (the load-bearing map identity) -/

/-- **`kLDU` is identity on every `activeM` slot** — the E-block slots decode to `frameSplitEquiv`'s
`Sum.inr` (E-role, kLDU identity arm); the leaf slots sit at the leaf boundary where the K-block is
`0×0`, so they fall through the identity arm too. (The shared atom for the commute.) -/
theorem kLDU_eq_on_activeM (ha : StructAdm M (tach M)) (x : Fin (routeMAmbient M) → ℝ)
    {q : Fin (routeMAmbient M)} (hq : q ∈ activeM M ha) :
    (kLDU M (tach M) ha x) q = x q := by
  rw [activeM, Finset.mem_union] at hq
  rcases hq with hE | hL
  · rw [activeEImg, Finset.mem_image] at hE
    obtain ⟨p, _, hp⟩ := hE; subst hp
    rw [kLDU, activeSlotE]; simp only [Equiv.apply_symm_apply]
  · rw [activeLeafImg, Finset.mem_image] at hL
    obtain ⟨p, _, hp⟩ := hL; subst hp
    rw [kLDU, leafSlot]; simp only [Equiv.apply_symm_apply]
    have hT3 : Text M (tach M) 3 = 0 := by
      have := Text_Lsucc_eq_zero M (by norm_num : 0 < 2); simpa using this
    split
    · rename_i qK _
      exact (Fin.cast (by show Text M (tach M) 3 * Text M (tach M) 3 = 0; rw [hT3, Nat.mul_zero])
        qK).elim0
    · rfl

/-- **`readK (pbo x) = readK x` ∀ boundary `k`** — `pivotBlowupOn` fixes K-slots: boundary `0` by the
banked `readK_pbo`; the leaf boundary `1` is vacuous (`Text 3 = 0`, the K-block is `0×0`). -/
theorem readK_pbo_all (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin 2) (i j : Fin (Text M (tach M) (k.val + 2))) :
    readK M (tach M) ha
        (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x) k i j
      = readK M (tach M) ha x k i j := by
  fin_cases k
  · exact readK_pbo ha h0r h0c x i j
  · have hT3 : Text M (tach M) 3 = 0 := by
      have := Text_Lsucc_eq_zero M (by norm_num : 0 < 2); simpa using this
    have : i.val < Text M (tach M) 3 := by simpa using i.isLt
    omega

/-- **The kLDU / pivotBlowupOn commute** — `pivotBlowupOn activeM leafPivot (kLDU x) =
kLDU (pivotBlowupOn activeM leafPivot x)`. `activeM = {E-block ∪ leaf slots}` (NO K-slots), `kLDU`
touches ONLY K-slots, so the two maps act on disjoint coordinate sets. The funext casework: a K-branch
`q` lands in the kLDU K-arm on both sides (`kLens(readK · k)`, equal by `readK_pbo_all`), and `pbo`
fixes it (K ∉ activeM); a non-K `q` lands in the kLDU identity arm, where `pbo` and `kLDU` commute
because the pivot + activeM slots `pbo` scales are all kLDU-fixed (`kLDU_eq_on_activeM`). -/
theorem interiorLive_commute (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (x : Fin (routeMAmbient M) → ℝ) :
    pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) (kLDU M (tach M) ha x)
      = kLDU M (tach M) ha
        (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x) := by
  set p₀ := leafPivot M ha (by norm_num) h0r h0c with hp₀
  funext q
  by_cases hpiv : q = p₀
  · subst hpiv
    rw [pivotBlowupOn, if_pos rfl, kLDU_leafPivot ha h0r h0c x,
        kLDU_leafPivot ha h0r h0c (pivotBlowupOn (activeM M ha) p₀ x), pivotBlowupOn, if_pos rfl]
  · by_cases hact : q ∈ activeM M ha
    · rw [pivotBlowupOn, if_neg hpiv, if_pos hact,
          kLDU_eq_on_activeM ha x hact, kLDU_leafPivot ha h0r h0c x,
          kLDU_eq_on_activeM ha (pivotBlowupOn (activeM M ha) p₀ x) hact,
          pivotBlowupOn, if_neg hpiv, if_pos hact]
    · -- spectator: both kLDU calls land in the same arm; K-arm equal by `readK_pbo_all`, identity
      -- arm by `pbo` fixing the slot (`q ∉ activeM`, `q ≠ p₀`).
      rw [pivotBlowupOn, if_neg hpiv, if_neg hact, kLDU, kLDU]
      have hpboq : pivotBlowupOn (activeM M ha) p₀ x q = x q := by
        rw [pivotBlowupOn, if_neg hpiv, if_neg hact]
      match hc : chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL q with
      | ⟨k, Sum.inl s⟩ =>
        have hmat : readK M (tach M) ha (pivotBlowupOn (activeM M ha) p₀ x) k
            = readK M (tach M) ha x k := by
          funext a b; exact readK_pbo_all ha h0r h0c x k a b
        simp only [hmat, hpboq]
      | ⟨k, Sum.inr s⟩ => simp only [hpboq]

/-! ## H2 — the multi-axis Jacobian exponent vector `leafH` -/

/-- **The `ChartIdx`-indexed K-diagonal exponent placement** (the LIVE-leaf analogue of the dead-leaf
`lduleafHOnIdx`, inlined to decouple from the retired `RouteMInteriorLDUContract`). At a frame slot
(`Sum.inl s`), boundary `k`, the K-role branch decodes `(i,j) = finProdFinEquiv.symm qK`; on the
diagonal `i = j` it returns the per-pivot exponent `(r_s + c_s) + 2·(t_s − 1 − i)` (the Schur frame
`r_s+c_s` + the LDU core `2(t_s−1−i)`), `0` off-diagonal / X,N,E / lift. -/
noncomputable def liveLeafHOnIdx (ha : StructAdm M (tach M)) :
    ChartIdx M (tDesc M (tach M)) → ℕ := fun q =>
  match q with
  | ⟨k, Sum.inl s⟩ =>
    match frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>
      let ij := finProdFinEquiv.symm qK
      if ij.1 = ij.2 then
        (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
          + (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
          + 2 * (Text M (tach M) (k.val + 2) - 1 - ij.1.val)
      else 0
    | _ => 0
  | ⟨_, Sum.inr _⟩ => 0

/-- **H2 — the multi-axis Jacobian exponent vector** for the LIVE-leaf ∘ kLDU chart. The binding axis
`leafPivot` carries `minAdm−1` (override); the lensed K-diagonal axes carry the frame+LDU exponents
`liveLeafHOnIdx`; `0` elsewhere. At `leafPivot` the placement is `0` (the leaf boundary's K-block is
empty), so the override introduces the genuine radial exponent without masking a K exponent. -/
noncomputable def interiorLive_leafH (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) : Fin (routeMAmbient M) → ℕ := fun j =>
  if j = leafPivot M ha (by norm_num) h0r h0c then
    minAdm M - 1
  else
    liveLeafHOnIdx ha (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL j)

/-- **H2 — the binding axis carries `minAdm−1`** (the pivot override is `if_pos rfl`). -/
theorem interiorLive_leafH_pivot (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    interiorLive_leafH ha h0r h0c (leafPivot M ha (by norm_num) h0r h0c) = minAdm M - 1 := by
  rw [interiorLive_leafH, if_pos rfl]

/-! ## H2 — the chart Jacobian monomial (headline ∘ kLDU) -/

/-- **H2b (genm-h2bdet's deliverable, consumed here)** — the boundary-factor determinant monomializes:
`|det D(BchartLeaf ∘ kLDU)(pbo u)| = ∏_{j ≠ leafPivot} |u_j|^{leafH j}` (the off-pivot K-diagonal
product, `1` at the pivot). STATED `sorry` — wired to genm-h2bdet's atom.

**CAVEAT (NOT a bounded monomialization — hreg-GATED; genm-h2bdet STEP-0 + source-verified).** The
un-lensed boundary det is NOT banked as `∏engine`: `interiorDet_leaf_headline_freeK` reduces it to
`engineFreeK = |det K|^{r+c}` only under the hypothesis `hDtot : |det Dtot| = |det K|^{r+c}`, and that
in turn (`interiorDet_leaf_headline_eihd`, `RouteMHDtotEihd.lean:1029`) rests on the OPEN regauge
residual `hreg : |det((eihdOut).symm ∘ eIn)| = 1` (the two-sided staircase conjugacy). No unconditional
headline exists; `hreg` is discharged nowhere (task #224 still open). So this `sorry` is hreg-GATED:
its honest closure is `H2b-i (the NEW full-ambient det D(kLDU) = ∏|q|^{2(t−1−i)}, genm-h2bdet,
route-independent) + the conditional freeK/eihd headline + hreg`. `hreg` is TRUE + BOUNDED (a slot-
reindex det-1, `eIn`/`eihdOut` permutation-like) but genuinely open — a named LEAF-1 sub-obligation. -/
theorem interiorLive_BdetMonomial (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (fun y => BchartLeaf ha (kLDU M (tach M) ha y))
        (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u)).toLinearMap|
      = ∏ j, if j = leafPivot M ha (by norm_num) h0r h0c then (1 : ℝ)
          else |u j| ^ (interiorLive_leafH ha h0r h0c j) :=
  sorry

/-- **H2 — the chart Jacobian is the monomial** `|det Dφ u| = ∏_j |u_j|^{leafH j}` (this thread's
assembly). Via the B' = BchartLeaf ∘ kLDU factorization (hmap-for-B' from `hmap_leaf` at `kLDU x` +
the commute): `radialComp_abs_det_at` fires ONCE → `|u leafPivot|^{minAdm−1} · |det DB'|`; the residual
`|det DB'|` is `interiorLive_BdetMonomial`; the pivot factor folds in via `interiorLive_leafH_pivot` +
the `Finset.prod` split.

The assembly (radial split + prod arithmetic) is sorry-free; it is **hreg-GATED through
`interiorLive_BdetMonomial`** (see that caveat) — the unconditional abs_det needs the open regauge
`hreg` closed (a bounded LEAF-1 sub-obligation), NOT a bounded monomialization. -/
theorem interiorLive_abs_det (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (interiorLivePhi ha h0r h0c) u).toLinearMap|
      = ∏ j, |u j| ^ (interiorLive_leafH ha h0r h0c j) := by
  set p₀ := leafPivot M ha (by norm_num) h0r h0c with hp₀
  set B' := fun y => BchartLeaf ha (kLDU M (tach M) ha y) with hB'
  have hmap : interiorLivePhi ha h0r h0c = B' ∘ pivotBlowupOn (activeM M ha) p₀ := by
    funext x
    rw [interiorLivePhi, hmap_leaf ha h0r h0c]
    show BchartLeaf ha (pivotBlowupOn (activeM M ha) p₀ (kLDU M (tach M) ha x)) = _
    rw [interiorLive_commute ha h0r h0c x]; rfl
  have hasDB' : HasFDerivAt B'
      (fderiv ℝ B' (pivotBlowupOn (activeM M ha) p₀ u))
      (pivotBlowupOn (activeM M ha) p₀ u) :=
    ((Bchart_differentiableAt ha _).comp _ (differentiable_kLDU M (tach M) ha _)).hasFDerivAt
  rw [radialComp_abs_det_at M (activeM M ha) p₀ (leafPivot_mem_activeM ha h0r h0c) (activeM_card ha)
    B' (interiorLivePhi ha h0r h0c) u _ hmap hasDB', interiorLive_BdetMonomial ha h0r h0c u]
  -- |u p₀|^{minAdm−1} · ∏(if j=p₀ then 1 else |u j|^{leafH j}) = ∏ |u j|^{leafH j}
  conv_rhs => rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ p₀)
    (fun j => |u j| ^ (interiorLive_leafH ha h0r h0c j))]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ p₀)
    (fun j => if j = p₀ then (1 : ℝ) else |u j| ^ (interiorLive_leafH ha h0r h0c j))]
  rw [if_pos rfl, one_mul, interiorLive_leafH_pivot ha h0r h0c]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [if_neg (by simp at hj; exact hj : j ≠ p₀)]

/-! ## H1-internal — differentiability, injectivity, unit facts, image -/

/-- **Differentiable** — `interiorLivePhi` is a polynomial chain. Via the hmap-for-B' factorization
(`hmap_leaf` at `kLDU x` + the commute): `interiorLivePhi = (BchartLeaf ∘ kLDU) ∘ pivotBlowupOn`, each
factor differentiable (`Bchart_differentiableAt`, `differentiable_kLDU`, `differentiable_pivotBlowupOn`). -/
theorem interiorLive_diff (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    Differentiable ℝ (interiorLivePhi ha h0r h0c) := by
  have hfact : interiorLivePhi ha h0r h0c
      = (fun y => BchartLeaf ha (kLDU M (tach M) ha y))
        ∘ pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) := by
    funext x
    rw [interiorLivePhi, hmap_leaf ha h0r h0c]
    show BchartLeaf ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c)
      (kLDU M (tach M) ha x)) = _
    rw [interiorLive_commute ha h0r h0c x]; rfl
  rw [hfact]
  refine Differentiable.comp ?_ (differentiable_pivotBlowupOn (activeM M ha) _)
  exact fun y => ((fun u => Bchart_differentiableAt ha u) _).comp y
    (differentiable_kLDU M (tach M) ha y)

/-- **The injectivity set's extra weighted axes** — the slots where `leafH > 0` off the binding pivot
(the K-LDU diagonal-pivot q-axes). Selected by `leafH`, so the cov engine's null-slice add-back
covers exactly the axes carrying a positive Jacobian exponent. -/
noncomputable def interiorLive_E (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) : Finset (Fin (routeMAmbient M)) :=
  Finset.univ.filter (fun j => 0 < interiorLive_leafH ha h0r h0c j
    ∧ j ≠ leafPivot M ha (by norm_num) h0r h0c)

/-- The injectivity domain — `{u | u leafPivot ≠ 0 ∧ ∀ j ∈ E, u j ≠ 0}` (off the pivot ∪ q-axes). -/
def interiorLiveInjDom (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) : Set (Fin (routeMAmbient M) → ℝ) :=
  {u | u (leafPivot M ha (by norm_num) h0r h0c) ≠ 0 ∧ ∀ j ∈ interiorLive_E ha h0r h0c, u j ≠ 0}

/-- **injOn atom #1 (genm-lduinj's deliverable, consumed here)** — `kLDU` is injective on the
blown-up domain `pbo '' injDom`. Reduces (via the banked `kLens`-Equiv peeling) to the LDU-product
uniqueness `(1+L)·diag(q)·(1+U)` injective off the q-pivots, which `pbo` preserves (K-slots ∉ activeM,
so `pbo` fixes them). STATED `sorry` — wired to genm-lduinj's LDU-uniqueness atom. -/
theorem interiorLive_kLDU_injOn (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    Set.InjOn (kLDU M (tach M) ha)
      (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c)
        '' interiorLiveInjDom ha h0r h0c) :=
  sorry

/-- **injOn atom #2 (my deliverable)** — `BchartLeaf` injective on the kLDU-image of `pbo '' injDom`.
The off-radial block recovery (radial fixed to `1` in `BchartLeaf`): K via the LDU-coordinatized
read, then X via forward-substitution through the Schur block `Bmat = [K; XK]`, then N/E/leaf linear
(banked `Agen_congr` / `schurFrameProd_u_to_E`), then `paramsEquivFlat` injective. STATED `sorry`. -/
theorem interiorLive_BchartLeaf_injOn (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    Set.InjOn (BchartLeaf ha)
      (kLDU M (tach M) ha
        '' (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c)
          '' interiorLiveInjDom ha h0r h0c)) :=
  sorry

/-- **H-inj — `InjOn` off the pivot ∪ q-axes** — the `Set.InjOn.comp` glue (#3, this thread): from the
factorization `interiorLivePhi = (BchartLeaf ∘ kLDU) ∘ pivotBlowupOn` (hmap-for-B' via `hmap_leaf` at
`kLDU x` + the commute), `pivotBlowupOn` injective off `{u leafPivot = 0}` (banked, the domain already
excludes it), then `BchartLeaf ∘ kLDU` injective via the two atoms (`interiorLive_kLDU_injOn` #1 +
`interiorLive_BchartLeaf_injOn` #2). -/
theorem interiorLive_injOn (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    Set.InjOn (interiorLivePhi ha h0r h0c) (interiorLiveInjDom ha h0r h0c) := by
  set p₀ := leafPivot M ha (by norm_num) h0r h0c with hp₀
  set pbo := pivotBlowupOn (activeM M ha) p₀ with hpbo
  have hfact : interiorLivePhi ha h0r h0c
      = (BchartLeaf ha ∘ kLDU M (tach M) ha) ∘ pbo := by
    funext x
    rw [interiorLivePhi, hmap_leaf ha h0r h0c]
    show BchartLeaf ha (pbo (kLDU M (tach M) ha x)) = _
    rw [hpbo, interiorLive_commute ha h0r h0c x]; rfl
  rw [hfact]
  have hpbo_inj : Set.InjOn pbo (interiorLiveInjDom ha h0r h0c) := by
    have hsub : interiorLiveInjDom ha h0r h0c
        ⊆ interiorLiveInjDom ha h0r h0c \ {x | x p₀ = 0} := by
      intro u hu; exact ⟨hu, hu.1⟩
    exact (pivotBlowupOn_injOn (activeM M ha) p₀ _).mono hsub
  exact (interiorLive_BchartLeaf_injOn ha h0r h0c).comp
    (interiorLive_kLDU_injOn ha h0r h0c) (Set.mapsTo_image _ _)
    |>.comp hpbo_inj (Set.mapsTo_image _ _)

/-- **H1-internal — the lensed unit a.e.-positivity + box bound** (`NodeAchieverChart.Ubound`). -/
theorem interiorLive_Ubound (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (hInt : InteriorDrop M) :
    ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
      (∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
        interiorLiveUnit ha h0r h0c u ≤ B) ∧
      ∀ᵐ u ∂(volume.restrict
          (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))),
        0 < interiorLiveUnit ha h0r h0c u :=
  sorry

/-- **H1-internal — the lensed unit is measurable** (polynomial chain). -/
theorem interiorLive_Umeas (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    Measurable (interiorLiveUnit ha h0r h0c) :=
  sorry

/-- **H1-internal — image containment** (`NodeAchieverChart.image_subset`). -/
theorem interiorLive_image (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ > 0, interiorLivePhi ha h0r h0c ''
        (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))
        ⊆ cubeBox (routeMAmbient M) ε :=
  sorry

/-! ## The n-fold null-slice cov from the engine -/

/-- **The change-of-variables** — assembles the cov engine `ldu_cov_of_differentiable_injOn` with
`hdiff` (`interiorLive_diff`), `habsdet` (`interiorLive_abs_det`), `hinj` (`interiorLive_injOn`). -/
theorem interiorLive_cov (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (V : Set (Fin (routeMAmbient M) → ℝ)) (hV : MeasurableSet V)
    (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in interiorLivePhi ha h0r h0c ''
        (V \ {x | x (leafPivot M ha (by norm_num) h0r h0c) = 0}), g x
      = ∫⁻ u in V \ {x | x (leafPivot M ha (by norm_num) h0r h0c) = 0},
          ENNReal.ofReal (∏ j, |u j| ^ (interiorLive_leafH ha h0r h0c j))
            * g (interiorLivePhi ha h0r h0c u) :=
  ldu_cov_of_differentiable_injOn (interiorLivePhi ha h0r h0c)
    (leafPivot M ha (by norm_num) h0r h0c) (interiorLive_leafH ha h0r h0c)
    (interiorLive_E ha h0r h0c) (interiorLive_diff ha h0r h0c)
    (fun u => interiorLive_abs_det ha h0r h0c u) (interiorLive_injOn ha h0r h0c) V hV g

/-! ## The assembled bundle + the interior box-divergence atom -/

/-- **The LIVE-leaf ∘ kLDU interior achiever chart bundle** — `interiorLivePhi` with binding pivot
`leafPivot`, the multi-axis `leafH`, unit `interiorLiveUnit`, and the open fields above. -/
noncomputable def interiorLiveNodeChart (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (hpos : 1 ≤ minAdm M) (hInt : InteriorDrop M) :
    NodeAchieverChart M where
  hpos := hpos
  phi := interiorLivePhi ha h0r h0c
  p := leafPivot M ha (by norm_num) h0r h0c
  leafH := interiorLive_leafH ha h0r h0c
  leafH_pivot := interiorLive_leafH_pivot ha h0r h0c
  Ufun := interiorLiveUnit ha h0r h0c
  Ubound := interiorLive_Ubound ha h0r h0c hInt
  Umeas := interiorLive_Umeas ha h0r h0c
  leaf_integrand := fun c =>
    Filter.Eventually.of_forall (fun x =>
      leaf_integrand_of_rate (leafPivot M ha (by norm_num) h0r h0c) (interiorLive_leafH ha h0r h0c)
        (fun y => routeMCore M (interiorLivePhi ha h0r h0c y)) (interiorLiveUnit ha h0r h0c)
        (fun y => routeMCore_interiorLivePhi ha h0r h0c y)
        (fun y => interiorLiveUnit_nonneg ha h0r h0c y) c x)
  cov := interiorLive_cov ha h0r h0c
  image_subset := interiorLive_image ha h0r h0c

/-- **The LIVE-leaf ∘ kLDU INTERIOR box-divergence atom** — `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`
for `c'` at-or-above `½·minAdm M`, every `ε > 0`, on the interior class. The `hInterior` atom the
dispatch spine consumes, via the M-agnostic `routeMCore_box_diverges_of_nodeChart`. -/
theorem routeMCore_box_diverges_interiorLive (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (hpos : 1 ≤ minAdm M) (hInt : InteriorDrop M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_nodeChart M
    (interiorLiveNodeChart ha h0r h0c hpos hInt) c' hc' ε hε

end DLNFibre.DLN.RLCT
