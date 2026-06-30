import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Validate.RouteMFlatLDU
import DLNFibre.DLN.RLCT.Validate.RouteMKLens
import DLNFibre.DLN.RLCT.Validate.RouteMPhiTargetDet
import DLNFibre.DLN.RLCT.Validate.RouteMBridgeCLE
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior
import DLNFibre.DLN.RLCT.Validate.RouteMLeafHeadline
import DLNFibre.DLN.RLCT.Validate.RouteMLeafBData

/-!
# `RouteMInteriorLDUContract` — the LDU-lensed INTERIOR achiever box-divergence contract (SPECIFY)

The CORRECT interior-branch achiever chart for the ∀M-L2 R1-LOWER leg, on the **LDU-lensed**
structured decoder `phiFlatLDU M (tach M) ha hN (kLDU M (tach M) ha)` — NOT the free-K
`phiFlatStructV` of `RouteMInteriorContract`, whose `cov` (pure monomial Jacobian) is provably
UNSATISFIABLE for a `t × t` K-core with `t ≥ 2` (the frame det `|det K_s|^{r+c}` is a degree-`t`
POLYNOMIAL, not a monomial — `RouteMFlatLDU` header). The LDU lens `kLDU` straightens each K-core's
det to the diagonal-pivot MONOMIAL `∏_i q_i` (`readK_kLDU_det`, banked), so the lensed chart's
frame+LDU Jacobian is `∏_j |u_j|^{leafH_j}` with the multi-axis exponent vector
`leafH = radial(minAdm−1) ⊕ per-boundary[(r+c) + 2(t−1−i)]`.

This module is the SPECIFY skeleton: it states the LDU-lensed `NodeAchieverChart M` bundle and the
interior box-divergence atom it produces, with the genuinely-open fields isolated as precisely-stated
`sorry`s (one per H-sub-task). The det/rate/threshold infrastructure they consume is banked:

* RATE: `routeMCore_phiFlatLDU` (∀M, any reparam — `phiFlatLDU` rate `= (x p)²·UvalLDU`). banked.
* DET telescope: `phiTarget_abs_det_of_factored` (`composeFold fs = φ` + per-factor det bookkeeping ⟹
  `|det Dφ| = ∏_j |u_j|^{leafH_j}`). banked. The map-eq `composeFold fs = phiFlatLDU…kLDU` reduces
  (via `composeFold_bridge_eq`, `bridgeCLE`) to a Params-level layer-op equality. banked spine.
* per-factor maps + dets (Schur `|det K|^{r+c}`, LDU `∏|q_i|^{2(t−1−i)}`, chain `1`, radial
  `|u_p|^{minAdm−1}`): banked full-ambient `ChartFactor`s. The LDU K-monomial `readK_kLDU_det`: banked.
* THRESHOLD: `nodeChart_thresholdLe` (`leafH p = minAdm−1` ⟹ `monomialThreshold ≤ ½·minAdm`). banked.

## The open obligations (each a stated `sorry`, mapped to an H-sub-task)

* `interiorLDU_leafH` (def, H2) — the multi-axis exponent vector, with `leafH p = minAdm−1`.
* `interiorLDU_factors` (def, H1) — the dependency-ordered factor list `fs` (Schur/LDU/chain/radial
  layer-ops conjugated by `bridgeCLE`).
* `interiorLDU_map_eq` (H1) — `composeFold (interiorLDU_factors …) = phiFlatLDU … kLDU` (the bridge,
  via `composeFold_bridge_eq` + the Params-level per-layer match).
* `interiorLDU_det_bookkeeping` (H2) — `∏ |det D_i| = ∏_j |u_j|^{leafH_j}` (the per-factor dets).
* `interiorLDU_Ubound` (H1-internal) — the lensed unit a.e.-positivity + box bound (the `kLDU`-lens
  transfer of the interior-drop witness `achieverUfun_wInt_ne_zero`).
* `interiorLDU_Umeas` (H1-internal) — `UvalLDU` measurable (polynomial-in-`x` chain).
* `interiorLDU_cov` (H3) — the n-fold null-slice lintegral change-of-variables (variable axis count).
* `interiorLDU_image` (H1-internal) — image containment (continuity + `φ 0 = 0`).

The TOP result `routeMCore_box_diverges_interiorLDU` is the interior `BoxDiverges` atom the dispatch
spine's `hInterior` consumes. The skeleton's signature is the contract; the `sorry`s are the build.

NOT axiom-clean yet (carries the listed `sorry`s, each with a CORRECT statement). To be discharged
H1/H2/H3; then `#print axioms` must be clean-three + inherited `monomial_rlct`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The LDU-lensed interior chart (the CORRECT interior chart) -/

/-- The LDU-lensed interior achiever chart `phiFlatLDU M (tach M) ha hN (kLDU M (tach M) ha)` — the
structured chart with the K-slots LDU-straightened so the frame det is a monomial. Rate banked
(`routeMCore_phiFlatLDU`); det a monomial (the lensed K-cores via `readK_kLDU_det`). -/
noncomputable def interiorLDUphi (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  phiFlatLDU M (tach M) ha hN (kLDU M (tach M) ha)

/-- The LDU-lensed unit `UvalLDU … kLDU` — the radial quotient `routeMCore (interiorLDUphi x)/(x p)²`. -/
noncomputable def interiorLDUunit (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) : (Fin (routeMAmbient M) → ℝ) → ℝ :=
  UvalLDU M (tach M) ha hN (kLDU M (tach M) ha)

/-- **The rate of the LDU-lensed interior chart ∀M** (banked, NO bridge): `routeMCore M
(interiorLDUphi x) = (x p)² · interiorLDUunit x`. The `kLDU` lens fixes the pivot, so the radial axis
survives; `routeMCore_phiFlatLDU` transfers the rate verbatim. -/
theorem routeMCore_interiorLDUphi (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (interiorLDUphi M ha hN x)
      = (x (structPivot M hN)) ^ 2 * interiorLDUunit M ha hN x :=
  routeMCore_phiFlatLDU M (tach M) ha hN (kLDU M (tach M) ha) x

/-- `0 ≤ interiorLDUunit` (sum of squares, banked `UvalLDU_nonneg`). -/
theorem interiorLDUunit_nonneg (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) (x : Fin (routeMAmbient M) → ℝ) :
    0 ≤ interiorLDUunit M ha hN x :=
  UvalLDU_nonneg M (tach M) ha hN (kLDU M (tach M) ha) x

/-! ## H1 (piece #1) — the `u`-free LDU-lensed boundary factor `BchartLDU` (the `BchartLeaf` analog)

Route B (Codex): `interiorLDUphi = phiFlatLDU … kLDU` factors as `BchartLDU ∘ pivotBlowupOn activeM p₀`
(a `u`-free boundary factor ∘ the radial blow-up), so the banked `radialComp_abs_det_at` gives
`|det Dφ| = |u_{p₀}|^{minAdm−1} · |det DBchartLDU|` — NO per-role CLE tower, NO long `composeFold`. The
boundary factor reads the LDU-lensed structured decoder at the FIXED radial scalar `1`, residuals from
the blown-up `y`. Mirrors `RouteMLeafBData.BparamsLeaf`/`BchartLeaf` but on `genBlkFlatStruct ∘ kLDU`
(the dead-leaf LDU decoder) instead of `genBlkFlatLive`. -/

/-- **The `u`-free LDU boundary-factor `Params`** `BparamsLDU ha y := chartParamsGen 1 M (tach M)
(genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha y)) hle` — radial scalar hardwired to `1`, the
K-slots LDU-straightened by `kLDU`, residuals read from `y`. -/
noncomputable def BparamsLDU (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y : Fin (routeMAmbient M) → ℝ) : Params M :=
  chartParamsGen 1 M (tach M)
    (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha y)) (hleStruct M (tach M) ha)

/-- **The `u`-free LDU boundary factor** `BchartLDU ha y := paramsEquivFlat M (BparamsLDU ha y)`. -/
noncomputable def BchartLDU (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  paramsEquivFlat M (BparamsLDU M ha y)

/-! ## H2 — the multi-axis Jacobian exponent vector `leafH` -/

/-- **H2 — the multi-axis Jacobian exponent vector** for the LDU-lensed interior chart:
`leafH = radial(minAdm−1) on the pivot ⊕ per-boundary[(r_s+c_s) + 2(t_s−1−i)]` on the lensed K-pivot
axes (the frame `r+c` exponent + the LDU-core deriv `2(t−1−i)` exponent), `0` on spectator axes. The
binding axis `p = structPivot` carries `minAdm−1` (`interiorLDU_leafH_pivot`).

STATED `sorry` (H2): the concrete construction over opaque widths — reads the per-boundary K-core
size `t_s` and the residual dims `r_s,c_s` off the achiever-path structure, places the LDU-pivot
exponents `(r_s+c_s)+2(t_s−1−i)` at the K-diagonal flat slots, the radial `minAdm−1` at the pivot,
`0` elsewhere. (Validated at `(3,3,3,3)`: `|u0|⁵·|u1|⁴·|u4|²·|u9|³`.) -/
noncomputable def interiorLDU_leafH (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) : Fin (routeMAmbient M) → ℕ :=
  sorry

/-- **H2 — the binding axis carries `minAdm−1`** (the radial blow-up exponent at the pivot). -/
theorem interiorLDU_leafH_pivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) :
    interiorLDU_leafH M ha hN (structPivot M hN) = minAdm M - 1 :=
  sorry

/-! ## H1 — the factor list + the map-equality bridge -/

/-- **H1 — the dependency-ordered factor list** `fs : List (ChartFactor N)` whose composite is the
LDU-lensed interior chart. Each factor is a `bridgeCLE`-conjugated Params-level layer-op (Schur_s /
LDU_s / chain_s / radial), assembled via `cleConjFactor (bridgeCLE M)`. The per-factor abs-dets are
the banked monomial values; `composeFold` of the list is `interiorLDUphi` (`interiorLDU_map_eq`).

STATED `sorry` (H1): the concrete ordered list over opaque widths — the genuine layer-op
decomposition of `phiParamsStruct` (on the `kLDU`-lensed decoder) into the Schur/LDU/chain/radial
fold. The CLE-collapse spine (`composeFold_bridge_eq`, `bridgeCLE`) is banked; this builds the `gs`
list + its `cleConjFactor` packaging. -/
noncomputable def interiorLDU_factors (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) : List (ChartFactor (routeMAmbient M)) :=
  sorry

/-- **H1 — the map-equality bridge** `composeFold (interiorLDU_factors …) = interiorLDUphi …`. The
genuine content: the Params-level layer-op equality (the `composeFold_bridge_eq` reduction) — the
`gs.foldr = phiParamsStruct` per-layer match over opaque widths (the cast bottleneck). -/
theorem interiorLDU_map_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) :
    composeFold (interiorLDU_factors M ha hN) = interiorLDUphi M ha hN :=
  sorry

/-- **H2 — the per-factor det bookkeeping** `∏ |det D_i| = ∏_j |u_j|^{leafH_j}` (the prefix-evaluated
per-factor abs-dets multiply to the multi-axis monomial). Assembles the banked per-factor dets
(radial `|u_p|^{minAdm−1}`, Schur `|det (lensed K)|^{r+c} = (∏q_i)^{r+c}`, LDU `∏|q_i|^{2(t−1−i)}`,
chain `1`) through `readK_kLDU_det` + the exponent arithmetic `(r+c)+2(t−1−i)`. -/
theorem interiorLDU_det_bookkeeping (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) (u : Fin (routeMAmbient M) → ℝ) :
    ((foldDerivList (interiorLDU_factors M ha hN) u).map
        (fun D : (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ) ↦
          |LinearMap.det D.toLinearMap|)).prod
      = ∏ j, |u j| ^ (interiorLDU_leafH M ha hN j) :=
  sorry

/-- **H1+H2 — the chart Jacobian is the monomial** `|det D(interiorLDUphi) u| = ∏_j |u_j|^{leafH_j}`,
assembled from the map-eq (H1) + the det bookkeeping (H2) via the banked generic telescope
`phiTarget_abs_det_of_factored`. NO further `sorry` — pure assembly of H1+H2. -/
theorem interiorLDU_abs_det (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (interiorLDUphi M ha hN) u).toLinearMap|
      = ∏ j, |u j| ^ (interiorLDU_leafH M ha hN j) :=
  phiTarget_abs_det_of_factored (interiorLDUphi M ha hN) (interiorLDU_factors M ha hN)
    (interiorLDU_map_eq M ha hN) (interiorLDU_leafH M ha hN) u
    (interiorLDU_det_bookkeeping M ha hN u)

/-! ## H1-internal — the unit a.e.-positivity, measurability, and image containment -/

/-- **H1-internal — the lensed unit a.e.-positivity + box bound** (`NodeAchieverChart.Ubound`). The
interior-drop pivot-survival witness `achieverUfun_wInt_ne_zero` gives `UvalStructV(wInt) ≠ 0`; the
`kLDU` lens is a pivot-fixing reparam, so a witness for `UvalLDU(kLDU)` transfers (the K-LDU image
hits the same nonzero `Hmat 0` entry). Combined with the polynomial box-bound. -/
theorem interiorLDU_Ubound (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) (hL : 0 < L) (hInt : InteriorDrop M) :
    ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
      (∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
        interiorLDUunit M ha hN u ≤ B) ∧
      ∀ᵐ u ∂(volume.restrict
          (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))),
        0 < interiorLDUunit M ha hN u :=
  sorry

/-- **H1-internal — the lensed unit is measurable** (`UvalLDU∘kLDU` is a polynomial in the chart
coordinates: the chain readers + `kLens` are polynomial maps). -/
theorem interiorLDU_Umeas (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) :
    Measurable (interiorLDUunit M ha hN) :=
  sorry

/-- **H3 — the n-fold null-slice change-of-variables** (`NodeAchieverChart.cov`). The lensed chart's
genuine Jacobian `|det Dφ| = ∏_j |u_j|^{leafH_j}` off the pivot-zero locus, the lintegral c-o-v with
the monomial weight, injOn off the union of weighted-axis planes + the n-fold null-slice (variable
weighted-axis count, generalizing the `(3,3,3,3)` 4-slice `phi3333_cov`). -/
theorem interiorLDU_cov (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M)
    (V : Set (Fin (routeMAmbient M) → ℝ)) (hV : MeasurableSet V)
    (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in interiorLDUphi M ha hN '' (V \ {x | x (structPivot M hN) = 0}), g x
      = ∫⁻ u in V \ {x | x (structPivot M hN) = 0},
          ENNReal.ofReal (∏ j, |u j| ^ (interiorLDU_leafH M ha hN j)) * g (interiorLDUphi M ha hN u) :=
  sorry

/-- **H1-internal — image containment** (`NodeAchieverChart.image_subset`): a small source box `[0,δ]^N`
maps into `cubeBox N ε` (continuity of `interiorLDUphi` + `interiorLDUphi 0 = 0`). -/
theorem interiorLDU_image (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ > 0, interiorLDUphi M ha hN ''
        (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))
        ⊆ cubeBox (routeMAmbient M) ε :=
  sorry

/-! ## The assembled LDU-lensed `NodeAchieverChart M` + the interior box-divergence atom -/

/-- **The LDU-lensed interior achiever chart bundle** — `interiorLDUphi` with binding pivot
`structPivot`, the multi-axis `leafH`, unit `interiorLDUunit`, and the open fields above. The
`leaf_integrand` rides on the banked rate `routeMCore_interiorLDUphi` + nonnegativity, det-free
(`leaf_integrand_of_rate`). -/
noncomputable def interiorLDUnodeChart (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) (hL : 0 < L) (hpos : 1 ≤ minAdm M) (hInt : InteriorDrop M) :
    NodeAchieverChart M where
  hpos := hpos
  phi := interiorLDUphi M ha hN
  p := structPivot M hN
  leafH := interiorLDU_leafH M ha hN
  leafH_pivot := interiorLDU_leafH_pivot M ha hN
  Ufun := interiorLDUunit M ha hN
  Ubound := interiorLDU_Ubound M ha hN hL hInt
  Umeas := interiorLDU_Umeas M ha hN
  leaf_integrand := fun c =>
    Filter.Eventually.of_forall (fun x =>
      leaf_integrand_of_rate (structPivot M hN) (interiorLDU_leafH M ha hN)
        (fun y => routeMCore M (interiorLDUphi M ha hN y)) (interiorLDUunit M ha hN)
        (fun y => routeMCore_interiorLDUphi M ha hN y)
        (fun y => interiorLDUunit_nonneg M ha hN y) c x)
  cov := interiorLDU_cov M ha hN
  image_subset := interiorLDU_image M ha hN

/-- **The LDU-lensed INTERIOR box-divergence atom** — `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`
for `c'` at-or-above `½·minAdm M`, every `ε > 0`, on the interior class. The `hInterior` atom the
dispatch spine `routeMCore_box_diverges_achiever_spine` consumes. Fed by the LDU-lensed bundle through
the M-agnostic assembly `routeMCore_box_diverges_of_nodeChart`. -/
theorem routeMCore_box_diverges_interiorLDU (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hN : 0 < routeMAmbient M) (hpos : 1 ≤ minAdm M) (hInt : InteriorDrop M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_nodeChart M
    (interiorLDUnodeChart M (structAdm_tach M hL) hN hL hpos hInt) c' hc' ε hε

end DLNFibre.DLN.RLCT
