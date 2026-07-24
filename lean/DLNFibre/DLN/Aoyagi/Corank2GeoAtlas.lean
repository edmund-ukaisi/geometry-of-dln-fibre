import DLNFibre.DLN.Aoyagi.LeafCoverTiling
import DLNFibre.Core.Aoyagi.ProductResolution

/-!
# `DLN.Aoyagi.Corank2GeoAtlas` — the CORANK-2 geometric go/no-go (L6 dom-wide `hjac` + L7 `hcover`)

The first-unit measurement for the geometric atlas (charter §1.B, `exists_coreResolution:311`): does ONE
genuinely-COUPLED corank-2 leaf's geometric realization inhabit CLEANLY? Two pieces, per the build brief:

* **L6 (dom-wide composite Jacobian).** The corank-2 chart map is `g = coShear ∘ blockBlowupMap S p`,
  the (unipotent Schur shear) ∘ (block blow-up) step. Its `|det Dg|` is the pure blow-up monomial
  `|u_p|^(|S|-1)` with the unit **identically 1** on ALL of the ambient (`coG_hjac`), because
  `jacDet coShear ≡ 1` EXACTLY (`jacDet_blockShear`, the shear-pin) and `jacDet (blockBlowupMap S p) =
  (u_p)^(|S|-1)` EXACTLY (`jacDet_blockBlowupMap`). The germ-only trap is structurally void. This is the
  `Chart.hjac` field's exact shape (`jacWeight coJac · |1|`).

* **L7 (`hcover` — the un-probed piece).** The COUPLED per-edge shear `coShear = blockShear coPhi`, where
  `coPhi` is the genuine rank-1 outer-product Schur displacement `C₂₂ ↦ C₂₂ − c₂₁ ⊗ c₁₂` on a 2×2 block
  (FOUR simultaneous bilinear corrections, the corank-2 coupling), satisfies the per-edge box-containment
  `closedBall 0 r ⊆ coShear '' closedBall 0 (r + r²)` (`coShear_covers`) — the SAME degree-2 inflation
  `f = r + r²` as the single-term `qshear`, because each corrected coordinate carries exactly one product
  `≤ r²` (a rank-1 update). Fed to the `LeafCoverTiling` engine, a depth-2, `|S|=2`, coupled-shear fan
  closes `Covers (r ↦ r + r²) · 1` (`covers_coTree`), so `covers_subset`/`exists_ball_subset_leafImages`
  give the cover of a punctured neighbourhood. The coupling changes only WHICH coordinates are corrected,
  NOT the per-edge degree (still 2), so obligation-1 does NOT fight at corank-2.

**Scope (no over-claim).** This inhabits L6's `hjac` (unit ≡ 1) and L7's `hcover`-contribution
(obligations 1+2 assembled by the engine) for the coupled corank-2 fan. It does NOT build the full
`Chart` record (the `hideal_*` ideal identity is the separate PROTO-§4 matrix-Schur bridge) — the
go/no-go is the two crux fields the brief names.
-/

open MeasureTheory Set Filter Topology Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.LeafCoverTiling

namespace DLNFibre.DLN.Aoyagi.Corank2GeoAtlas

/-! ## §1 — the coupled corank-2 Schur shear `coShear = blockShear coPhi`

Coordinate layout on `Fin 8`: `0,1 = c₁₂` (the pivot column), `2,3 = c₂₁` (the pivot row),
`4,5,6,7 = C₂₂` (the 2×2 coupled block). The displacement `coPhi` places the rank-1 outer product
`−c₂₁ ⊗ c₁₂` in the four `C₂₂` slots and `0` on the kept `{0,1,2,3}` — Aoyagi's coupled Schur update
`Δ = C₂₂ − c₂₁·c₁₂` (worked.tex:475–520; the PROTO `Delta` at corank 2). -/

/-- The kept coordinate set `{0,1,2,3}` (the pivot row + column) — the shear FIXES these and READS ONLY
these. -/
def coKeep : Fin 8 → Prop := fun i ↦ i.val < 4

/-- The coupled rank-1 Schur displacement `−c₂₁ ⊗ c₁₂`: coord `4 ↦ −x₀·x₂`, `5 ↦ −x₁·x₂`,
`6 ↦ −x₀·x₃`, `7 ↦ −x₁·x₃`, and `0` on the kept block `{0,1,2,3}`. FOUR simultaneous bilinear terms —
the genuine corank-2 coupling (a 2×2 block, not a single quadratic). -/
def coPhi (x : Fin 8 → ℝ) : Fin 8 → ℝ := fun i ↦
  if i = 4 then - (x 0 * x 2)
  else if i = 5 then - (x 1 * x 2)
  else if i = 6 then - (x 0 * x 3)
  else if i = 7 then - (x 1 * x 3)
  else 0

/-- The coupled corank-2 chart shear `coShear = blockShear coPhi = u ↦ u + coPhi u`. -/
def coShear : (Fin 8 → ℝ) → (Fin 8 → ℝ) := blockShear coPhi

/-- `coPhi` fixes the origin. -/
theorem coPhi_zero : coPhi (0 : Fin 8 → ℝ) = 0 := by
  funext i
  simp only [coPhi, Pi.zero_apply, mul_zero, neg_zero, ite_self]

/-- `coPhi` is analytic (a polynomial map: products of coordinate projections). -/
theorem analyticOnNhd_coPhi : AnalyticOnNhd ℝ coPhi Set.univ := by
  have hproj : ∀ k : Fin 8, AnalyticOnNhd ℝ (fun w : Fin 8 → ℝ ↦ w k) Set.univ := fun k ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 8 ↦ ℝ) k).analyticOnNhd _
  apply AnalyticOnNhd.pi
  intro j
  by_cases h4 : j = 4
  · have : (fun w : Fin 8 → ℝ ↦ coPhi w j) = fun w ↦ - (w 0 * w 2) := by
      funext w; simp [coPhi, h4]
    rw [this]; exact ((hproj 0).mul (hproj 2)).neg
  · by_cases h5 : j = 5
    · have : (fun w : Fin 8 → ℝ ↦ coPhi w j) = fun w ↦ - (w 1 * w 2) := by
        funext w; simp [coPhi, h4, h5]
      rw [this]; exact ((hproj 1).mul (hproj 2)).neg
    · by_cases h6 : j = 6
      · have : (fun w : Fin 8 → ℝ ↦ coPhi w j) = fun w ↦ - (w 0 * w 3) := by
          funext w; simp [coPhi, h4, h5, h6]
        rw [this]; exact ((hproj 0).mul (hproj 3)).neg
      · by_cases h7 : j = 7
        · have : (fun w : Fin 8 → ℝ ↦ coPhi w j) = fun w ↦ - (w 1 * w 3) := by
            funext w; simp [coPhi, h4, h5, h6, h7]
          rw [this]; exact ((hproj 1).mul (hproj 3)).neg
        · have : (fun w : Fin 8 → ℝ ↦ coPhi w j) = fun _ ↦ (0 : ℝ) := by
            funext w; simp [coPhi, h4, h5, h6, h7]
          rw [this]; exact analyticOnNhd_const

/-- `coPhi` is differentiable (from analyticity). -/
theorem differentiable_coPhi : Differentiable ℝ coPhi :=
  differentiableOn_univ.mp analyticOnNhd_coPhi.differentiableOn

/-- `coPhi` VANISHES on the kept block `{0,1,2,3}` — the `hkeep` clause for the shear. -/
theorem coPhi_keep (u : Fin 8 → ℝ) (i : Fin 8) (hi : coKeep i) : coPhi u i = 0 := by
  simp only [coKeep] at hi
  have h4 : i ≠ 4 := by rintro rfl; omega
  have h5 : i ≠ 5 := by rintro rfl; omega
  have h6 : i ≠ 6 := by rintro rfl; omega
  have h7 : i ≠ 7 := by rintro rfl; omega
  simp [coPhi, h4, h5, h6, h7]

/-- `coPhi` READS ONLY the kept block `{0,1,2,3}` — the `hread` clause for the shear. -/
theorem coPhi_read (u v : Fin 8 → ℝ) (h : ∀ i, coKeep i → u i = v i) : coPhi u = coPhi v := by
  have e0 : u 0 = v 0 := h 0 (by simp [coKeep])
  have e1 : u 1 = v 1 := h 1 (by simp [coKeep])
  have e2 : u 2 = v 2 := h 2 (by simp [coKeep])
  have e3 : u 3 = v 3 := h 3 (by simp [coKeep])
  funext i
  simp only [coPhi]
  rw [e0, e1, e2, e3]

/-! ## §2 — shear-level facts (origin-fixing, analytic, unit Jacobian, bijective) -/

/-- `coShear` fixes the origin. -/
theorem coShear_zero : coShear (0 : Fin 8 → ℝ) = 0 := blockShear_zero coPhi coPhi_zero

/-- `coShear` is analytic (`id + coPhi`, a polynomial automorphism). -/
theorem analyticOnNhd_coShear : AnalyticOnNhd ℝ coShear Set.univ :=
  analyticOnNhd_blockShear coPhi analyticOnNhd_coPhi

/-- `coShear` is differentiable. -/
theorem differentiable_coShear : Differentiable ℝ coShear :=
  differentiableOn_univ.mp analyticOnNhd_coShear.differentiableOn

/-- `coShear` is injective (a bijection with polynomial inverse `blockShearInv coPhi`). -/
theorem injective_coShear : Function.Injective coShear :=
  injective_blockShear coPhi coKeep coPhi_keep coPhi_read

/-- **The shear-pin at corank 2: `jacDet coShear ≡ 1` EXACTLY, everywhere.** The coupled Schur shear is
unipotent (block-triangular differential `[[I,0],[∂/∂kept, I]]`, `hkeep` kills the kept rows, `hread`
kills the non-kept columns), so its Jacobian is an EXACT `1` — no power-series unit that could vanish.
This is why the L6 composite unit is identically `1`. -/
theorem jacDet_coShear (u : Fin 8 → ℝ) : jacDet coShear u = 1 :=
  jacDet_blockShear coPhi coKeep differentiable_coPhi coPhi_keep coPhi_read u

/-! ## §3 — L7 obligation-1: the per-edge box-containment for the COUPLED shear

The un-probed crux. The coupled shear has FOUR simultaneous bilinear corrections, yet closes under the
SAME degree-2 inflation `f = r + r²` as the single-term `qshear`: each corrected coordinate carries
exactly one product `≤ r²` (a rank-1 update), so the coupling adds corrected coordinates but never
raises the per-edge degree. -/

/-- **L7 obligation-1 (corank-2 coupled).** `closedBall 0 r ⊆ coShear '' closedBall 0 (r + r²)` — the
per-edge box-containment for the coupled Schur shear, under the degree-2 inflation `f = r + r²`. The
preimage of `x` is `blockShearInv coPhi x = x − coPhi x`; each of its coordinates is either `x i` (kept,
`≤ r`) or `x i ± (product of two coords)` (`≤ r + r²`). This is the exact clause `LeafCoverTiling`'s
`Covers` fold consumes per node — and it does NOT fight at corank 2. -/
theorem coShear_covers {r : ℝ} (hr : 0 ≤ r) :
    closedBall (0 : Fin 8 → ℝ) r ⊆ coShear '' closedBall 0 (r + r ^ 2) := by
  have hrr : (0 : ℝ) ≤ r + r ^ 2 := by positivity
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr] at hx
  have hb : ∀ i, |x i| ≤ r := fun i ↦ by rw [← Real.norm_eq_abs]; exact hx i
  -- the bilinear bound: `|x a · x b| ≤ r²` (each factor `≤ r`)
  have hbil : ∀ a b : Fin 8, |x a * x b| ≤ r ^ 2 := by
    intro a b; rw [abs_mul, sq]; exact mul_le_mul (hb a) (hb b) (abs_nonneg _) hr
  refine ⟨blockShearInv coPhi x, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hrr]
    intro i
    rw [Real.norm_eq_abs]
    simp only [blockShearInv, Pi.sub_apply]
    by_cases hi4 : i = 4
    · subst hi4
      have h4 := abs_le.mp (hb 4); have hp := abs_le.mp (hbil 0 2)
      change |x 4 - -(x 0 * x 2)| ≤ r + r ^ 2
      rw [abs_le]; exact ⟨by linarith [h4.1, hp.1], by linarith [h4.2, hp.2]⟩
    · by_cases hi5 : i = 5
      · subst hi5
        have h5 := abs_le.mp (hb 5); have hp := abs_le.mp (hbil 1 2)
        change |x 5 - -(x 1 * x 2)| ≤ r + r ^ 2
        rw [abs_le]; exact ⟨by linarith [h5.1, hp.1], by linarith [h5.2, hp.2]⟩
      · by_cases hi6 : i = 6
        · subst hi6
          have h6 := abs_le.mp (hb 6); have hp := abs_le.mp (hbil 0 3)
          change |x 6 - -(x 0 * x 3)| ≤ r + r ^ 2
          rw [abs_le]; exact ⟨by linarith [h6.1, hp.1], by linarith [h6.2, hp.2]⟩
        · by_cases hi7 : i = 7
          · subst hi7
            have h7 := abs_le.mp (hb 7); have hp := abs_le.mp (hbil 1 3)
            change |x 7 - -(x 1 * x 3)| ≤ r + r ^ 2
            rw [abs_le]; exact ⟨by linarith [h7.1, hp.1], by linarith [h7.2, hp.2]⟩
          · have hc0 : coPhi x i = 0 := by simp [coPhi, hi4, hi5, hi6, hi7]
            rw [hc0, sub_zero]
            exact (hb i).trans (le_add_of_nonneg_right (by positivity))
  · show blockShear coPhi (blockShearInv coPhi x) = x
    exact blockShearInv_rightInverse coPhi coKeep coPhi_keep coPhi_read x

end DLNFibre.DLN.Aoyagi.Corank2GeoAtlas
