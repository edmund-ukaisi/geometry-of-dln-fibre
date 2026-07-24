import DLNFibre.DLN.Aoyagi.LeafCoverTiling
import DLNFibre.Core.Aoyagi.ProductResolution

/-!
# `DLN.Aoyagi.GeneralGeoAtlas` — the GENERAL-`d` geometric mechanisms (L6 `hjac` + L7 `hcover`)

The general-`d` assembly of the two hardest geometric mechanisms the corank-2 first unit
(`Corank2GeoAtlas.lean`) proved genuine on hardcoded `Fin 8`: the coupled per-edge box-containment
(L7 obligation-1) and the dom-wide unit ≡ 1 composite Jacobian (L6). Here they are proven over
GENERAL `Fin D`, ARBITRARY block sizes / pivots, and ARBITRARY displacement — the primitives
(`PathAtoms`, `BlockBlowup`, `LeafCoverTiling`) are already general in `Fin D`, so this is the
bounded-buildable ASSEMBLY the brief scopes, NOT a new monument.

## §1 — L7 obligation-1, GENERAL (`blockShear_covers_of_norm_bound`)

The corank-2 `coShear_covers` was a coordinate-by-coordinate bound on a 4-term rank-1 shear. The
general form is a single **norm-level** estimate: any block shear whose displacement is
quadratically bounded on the `r`-ball (`‖φ x‖ ≤ r²`) covers the `r`-ball from the `(r + r²)`-ball,
as the polynomial inverse `blockShearInv φ x = x − φ x` obeys `‖x − φ x‖ ≤ ‖x‖ + ‖φ x‖ ≤ r + r²`.
This is dimension-free and displacement-generic — it retires the "un-probed at corank ≥ 2" flag for
EVERY block size and pivot type, since the hypothesis `hquad` is the only thing that varies.

## §2 — the general rank-1 (outer-product) coupling (`outerDisp`) + CENTERS

Aoyagi's per-step Schur update `C₂₂ ↦ C₂₂ − c₂₁ ⊗ c₁₂` is, entrywise, a RANK-1 outer product: each
corrected coordinate carries exactly ONE bilinear product `−x_a · x_b` (one pivot per step). The
general `outerDisp corr` places, at each coordinate `i`, either `0` (kept) or `−x_{a} · x_{b}` for a
declared source pair `(a,b)`. Under the block hypothesis `hsrc` (each corrected coordinate reads
only KEPT sources), it satisfies `hkeep`/`hread` (so `jacDet = 1`, unipotent) AND the quadratic
bound `hquad` with constant `1` (rank-1 ⟹ `C = 1`). This is why the clean `r + r²` recurrence
survives to general `d`: no rank-`q > 1` correction inflates the constant.

**CENTERS (the brief's discharge criterion), dissolved.** `outerDisp corr` vanishes to 2nd order at
the chart origin: `outerDisp corr 0 = 0` (`outerDisp_zero`) and `fderiv (outerDisp corr) 0 = 0`
(`fderiv_outerDisp_zero`) — no linear part. The load-bearing consequence is the GLOBAL quadratic
bound `outerDisp_norm_bound` (stronger than the germ `fderiv = 0`), which holds at every radius, so
the box-inflation constant never picks up a center-dependent term. Centers never bite; we do not
track them.
-/

open MeasureTheory Set Filter Topology Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.LeafCoverTiling

namespace DLNFibre.DLN.Aoyagi.GeneralGeoAtlas

variable {D : ℕ}

/-! ## §1 — L7 obligation-1, GENERAL: the norm-level box-containment -/

/-- **L7 obligation-1, GENERAL (`Fin D`, any displacement).** A block shear whose displacement is
quadratically bounded on the `r`-ball (`‖φ x‖ ≤ r²`) covers the `r`-ball from the `(r + r²)`-ball:
`closedBall 0 r ⊆ blockShear φ '' closedBall 0 (r + r²)`. The preimage is the polynomial inverse
`blockShearInv φ x = x − φ x`, and `‖x − φ x‖ ≤ ‖x‖ + ‖φ x‖ ≤ r + r²` (triangle inequality). No
dimension bound, no coordinate case-split — the displacement-generic form of `coShear_covers` that
the `LeafCoverTiling` fold consumes per node, for EVERY block size and pivot type. -/
theorem blockShear_covers_of_norm_bound {φ : (Fin D → ℝ) → (Fin D → ℝ)} (keep : Fin D → Prop)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v)
    {r : ℝ} (hquad : ∀ x : Fin D → ℝ, ‖x‖ ≤ r → ‖φ x‖ ≤ r ^ 2) :
    closedBall (0 : Fin D → ℝ) r ⊆ blockShear φ '' closedBall 0 (r + r ^ 2) := by
  intro x hx
  have hxr : ‖x‖ ≤ r := mem_closedBall_zero_iff.mp hx
  refine ⟨blockShearInv φ x, ?_, blockShearInv_rightInverse φ keep hkeep hread x⟩
  rw [mem_closedBall_zero_iff]
  calc ‖blockShearInv φ x‖ = ‖x - φ x‖ := rfl
    _ ≤ ‖x‖ + ‖φ x‖ := norm_sub_le _ _
    _ ≤ r + r ^ 2 := add_le_add hxr (hquad x hxr)

/-! ## §2 — the general rank-1 (outer-product) coupling `outerDisp` -/

/-- The **general rank-1 (outer-product) Schur displacement.** `corr i = none` marks coordinate `i`
as KEPT (`φ x i = 0`); `corr i = some (a, b)` marks it CORRECTED with the single bilinear product
`−x_a · x_b`. This is the entrywise form of Aoyagi's coupled update `C₂₂ ↦ C₂₂ − c₂₁ ⊗ c₁₂`: one
product per corrected coordinate (rank-1, one pivot per step). The corank-2 `coPhi` is the instance
`corr 4 = (0,2)`, `corr 5 = (1,2)`, `corr 6 = (0,3)`, `corr 7 = (1,3)`, else `none`. -/
def outerDisp (corr : Fin D → Option (Fin D × Fin D)) (x : Fin D → ℝ) : Fin D → ℝ :=
  fun i ↦ match corr i with
    | none => 0
    | some (a, b) => -(x a * x b)

@[simp] theorem outerDisp_none (corr : Fin D → Option (Fin D × Fin D)) (x : Fin D → ℝ) {i : Fin D}
    (h : corr i = none) : outerDisp corr x i = 0 := by
  simp only [outerDisp, h]

@[simp] theorem outerDisp_some (corr : Fin D → Option (Fin D × Fin D)) (x : Fin D → ℝ)
    {i a b : Fin D} (h : corr i = some (a, b)) : outerDisp corr x i = -(x a * x b) := by
  simp only [outerDisp, h]

/-- **`outerDisp` fixes the origin** (`coPhi 0 = 0`; the first CENTERS clause). Every corrected
coordinate is a product, which vanishes at `0`. -/
theorem outerDisp_zero (corr : Fin D → Option (Fin D × Fin D)) :
    outerDisp corr (0 : Fin D → ℝ) = 0 := by
  funext i
  cases hc : corr i with
  | none => rw [outerDisp_none corr _ hc]; rfl
  | some ab => obtain ⟨a, b⟩ := ab; rw [outerDisp_some corr _ hc]; simp

/-- **`outerDisp` is analytic** (a polynomial map: each coordinate is `0` or `−`(product of two
projections)). -/
theorem analyticOnNhd_outerDisp (corr : Fin D → Option (Fin D × Fin D)) :
    AnalyticOnNhd ℝ (outerDisp corr) Set.univ := by
  have hproj : ∀ k : Fin D, AnalyticOnNhd ℝ (fun w : Fin D → ℝ ↦ w k) Set.univ := fun k ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin D ↦ ℝ) k).analyticOnNhd _
  apply AnalyticOnNhd.pi
  intro j
  cases hc : corr j with
  | none =>
    have : (fun w : Fin D → ℝ ↦ outerDisp corr w j) = fun _ ↦ (0 : ℝ) := by
      funext w; exact outerDisp_none corr w hc
    rw [this]; exact analyticOnNhd_const
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have : (fun w : Fin D → ℝ ↦ outerDisp corr w j) = fun w ↦ -(w a * w b) := by
      funext w; exact outerDisp_some corr w hc
    rw [this]; exact ((hproj a).mul (hproj b)).neg

/-- **`outerDisp` is differentiable** (from analyticity). -/
theorem differentiable_outerDisp (corr : Fin D → Option (Fin D × Fin D)) :
    Differentiable ℝ (outerDisp corr) :=
  differentiableOn_univ.mp (analyticOnNhd_outerDisp corr).differentiableOn

/-- The **kept-coordinate predicate**: `i` is kept iff it is not corrected (`corr i = none`). -/
def outerKeep (corr : Fin D → Option (Fin D × Fin D)) : Fin D → Prop := fun i ↦ corr i = none

/-- **`outerDisp` vanishes on the kept coordinates** — the `hkeep` clause. -/
theorem outerDisp_keep (corr : Fin D → Option (Fin D × Fin D)) (u : Fin D → ℝ) (i : Fin D)
    (hi : outerKeep corr i) : outerDisp corr u i = 0 :=
  outerDisp_none corr u hi

/-- **`outerDisp` reads only KEPT coordinates** — the `hread` clause. Requires `hsrc`: every
corrected coordinate's source pair consists of KEPT coordinates (the block structure — the pivot
row/column are fixed, the block is only written). -/
theorem outerDisp_read (corr : Fin D → Option (Fin D × Fin D))
    (hsrc : ∀ i a b, corr i = some (a, b) → corr a = none ∧ corr b = none)
    (u v : Fin D → ℝ) (h : ∀ i, outerKeep corr i → u i = v i) :
    outerDisp corr u = outerDisp corr v := by
  funext i
  cases hc : corr i with
  | none => rw [outerDisp_none corr u hc, outerDisp_none corr v hc]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    obtain ⟨ha, hb⟩ := hsrc i a b hc
    rw [outerDisp_some corr u hc, outerDisp_some corr v hc, h a ha, h b hb]

/-- **The load-bearing quadratic bound (`hquad`, the CENTERS discharge).** `‖x‖ ≤ r ⟹ ‖outerDisp
corr x‖ ≤ r²` — each corrected coordinate is a single product `|x_a · x_b| ≤ r·r = r²` (rank-1,
constant `1`), the kept ones are `0`. This GLOBAL bound (at every radius) keeps the box-inflation
clean `r + r²`; a rank-`q` step would give `r + q·r²`. Feeds `blockShear_covers_of_norm_bound`. -/
theorem outerDisp_norm_bound (corr : Fin D → Option (Fin D × Fin D)) {x : Fin D → ℝ} {r : ℝ}
    (hx : ‖x‖ ≤ r) : ‖outerDisp corr x‖ ≤ r ^ 2 := by
  have hr : 0 ≤ r := le_trans (norm_nonneg x) hx
  rw [pi_norm_le_iff_of_nonneg (sq_nonneg r)]
  intro i
  rw [Real.norm_eq_abs]
  cases hc : corr i with
  | none => rw [outerDisp_none corr x hc, abs_zero]; exact sq_nonneg r
  | some ab =>
    obtain ⟨a, b⟩ := ab
    rw [outerDisp_some corr x hc, abs_neg, abs_mul, sq]
    have ha : |x a| ≤ r := by rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x a).trans hx
    have hb : |x b| ≤ r := by rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x b).trans hx
    exact mul_le_mul ha hb (abs_nonneg _) hr

/-- **`outerDisp` has zero derivative at the origin** (`fderiv (outerDisp corr) 0 = 0`; the second,
load-bearing CENTERS clause — NO linear part, pure quadratic-and-up). Follows from the global
quadratic bound `outerDisp_norm_bound` (`‖outerDisp corr x‖ ≤ ‖x‖² = o(‖x‖)`). So a nonzero center
never gains a linear term that could break the clean `r + r²`. -/
theorem fderiv_outerDisp_zero (corr : Fin D → Option (Fin D × Fin D)) :
    fderiv ℝ (outerDisp corr) (0 : Fin D → ℝ) = 0 := by
  have hlo : (outerDisp corr) =o[𝓝 (0 : Fin D → ℝ)] (fun x ↦ x) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have hev : ∀ᶠ x in 𝓝 (0 : Fin D → ℝ), ‖x‖ ≤ ε := by
      filter_upwards [closedBall_mem_nhds (0 : Fin D → ℝ) hε] with x hx
      exact mem_closedBall_zero_iff.mp hx
    filter_upwards [hev] with x hx
    calc ‖outerDisp corr x‖ ≤ ‖x‖ ^ 2 := outerDisp_norm_bound corr le_rfl
      _ = ‖x‖ * ‖x‖ := sq ‖x‖
      _ ≤ ε * ‖x‖ := by
        rw [mul_comm ε]; exact mul_le_mul_of_nonneg_left hx (norm_nonneg x)
  have hfd : HasFDerivAt (outerDisp corr) (0 : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ)) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    simpa [outerDisp_zero] using hlo
  exact hfd.fderiv

/-- **`outerShear`** — the general rank-1 block shear `u ↦ u + outerDisp corr u`. The general-`d`
analogue of the corank-2 `coShear`. -/
def outerShear (corr : Fin D → Option (Fin D × Fin D)) : (Fin D → ℝ) → (Fin D → ℝ) :=
  blockShear (outerDisp corr)

/-- **`outerShear` is differentiable** (analytic polynomial automorphism). -/
theorem differentiable_outerShear (corr : Fin D → Option (Fin D × Fin D)) :
    Differentiable ℝ (outerShear corr) :=
  differentiableOn_univ.mp
    (analyticOnNhd_blockShear (outerDisp corr) (analyticOnNhd_outerDisp corr)).differentiableOn

/-- **`outerShear` is injective** (a polynomial automorphism), given the block source hypothesis. -/
theorem injective_outerShear (corr : Fin D → Option (Fin D × Fin D))
    (hsrc : ∀ i a b, corr i = some (a, b) → corr a = none ∧ corr b = none) :
    Function.Injective (outerShear corr) :=
  injective_blockShear (outerDisp corr) (outerKeep corr) (outerDisp_keep corr)
    (outerDisp_read corr hsrc)

/-- **The `outerShear` Jacobian is exactly 1** (unipotent, the shear-pin), given the block source
hypothesis. -/
theorem jacDet_outerShear (corr : Fin D → Option (Fin D × Fin D))
    (hsrc : ∀ i a b, corr i = some (a, b) → corr a = none ∧ corr b = none) (u : Fin D → ℝ) :
    jacDet (outerShear corr) u = 1 :=
  jacDet_blockShear (outerDisp corr) (outerKeep corr) (differentiable_outerDisp corr)
    (outerDisp_keep corr) (outerDisp_read corr hsrc) u

/-- **L7 obligation-1 for `outerShear`, at EVERY radius.** `closedBall 0 r ⊆ outerShear corr ''
closedBall 0 (r + r²)` — the general-`d` `coShear_covers`, now for arbitrary block sizes / pivots
(the corank-2 4-term shear is one instance). Rides `blockShear_covers_of_norm_bound` on the rank-1
quadratic bound `outerDisp_norm_bound` (`hquad`, constant `1`). Holds at every `r`, so it plugs into
the fan fold at any depth. -/
theorem outerShear_covers (corr : Fin D → Option (Fin D × Fin D))
    (hsrc : ∀ i a b, corr i = some (a, b) → corr a = none ∧ corr b = none) {r : ℝ} :
    closedBall (0 : Fin D → ℝ) r ⊆ outerShear corr '' closedBall 0 (r + r ^ 2) :=
  blockShear_covers_of_norm_bound (outerKeep corr) (outerDisp_keep corr) (outerDisp_read corr hsrc)
    (fun _ hxr ↦ outerDisp_norm_bound corr hxr)

/-! ## §3 — L6: the dom-wide composite Jacobian, unit ≡ 1 (general block sizes + pivots) -/

/-- **`blockBlowupMap S p` is differentiable** (a polynomial map; general `Fin D`). -/
theorem differentiable_blockBlowupMap (S : Finset (Fin D)) (p : Fin D) :
    Differentiable ℝ (blockBlowupMap S p) :=
  differentiableOn_univ.mp (analyticOnNhd_blockBlowupMap S p).differentiableOn

/-- The single-step Jacobian monomial exponent `j ↦ (|S|−1)·[j = p]` (the pure block-blow-up
exponent; the shear contributes nothing). -/
def singleJac (S : Finset (Fin D)) (p : Fin D) : Fin D → ℕ :=
  fun j ↦ if j = p then S.card - 1 else 0

/-- `jacWeight (singleJac S p) u = |u_p|^(|S|−1)` (the block-blow-up monomial as a `jacWeight`). -/
theorem jacWeight_singleJac (S : Finset (Fin D)) (p : Fin D) (u : Fin D → ℝ) :
    jacWeight (singleJac S p) u = |u p| ^ (S.card - 1) := by
  rw [jacWeight, Finset.prod_eq_single p]
  · simp [singleJac]
  · intro d _ hd; simp [singleJac, hd]
  · intro h; exact absurd (Finset.mem_univ p) h

/-- **L6 per-step, GENERAL.** A unit-Jacobian shear `sh` (`jacDet sh ≡ 1`) composed with a block
blow-up `blockBlowupMap S p` (`p ∈ S`) has `|jacDet (sh ∘ blockBlowupMap S p) u| = |u_p|^(|S|−1)`
for ALL `u` (dom-wide). Chain rule ∘ shear-pin ∘ the block-blow-up monomial `jacDet_blockBlowupMap`.
The general-`d`, arbitrary-block-size / pivot generalization of the corank-2 `jacDet_coG`. -/
theorem abs_jacDet_shear_comp_blockBlowup {S : Finset (Fin D)} {p : Fin D} (hp : p ∈ S)
    (sh : (Fin D → ℝ) → (Fin D → ℝ)) (hsh_diff : Differentiable ℝ sh)
    (hsh_jac : ∀ w, jacDet sh w = 1) (u : Fin D → ℝ) :
    |jacDet (sh ∘ blockBlowupMap S p) u| = |u p| ^ (S.card - 1) := by
  rw [jacDet_comp u (hsh_diff _) (differentiable_blockBlowupMap S p u), hsh_jac, one_mul,
    jacDet_blockBlowupMap hp, abs_pow]

/-- **L6 — the DOM-WIDE Jacobian certificate `hjac`, unit ≡ 1, GENERAL.** For a unit-Jacobian shear
`sh`, `|jacDet (sh ∘ blockBlowupMap S p) u| = jacWeight (singleJac S p) u · |1|` for ALL `u` — the
exact `Chart.hjac` field shape with `unit := fun _ ↦ 1` (nonvanishing everywhere). The germ-only
trap is structurally void: the unit is IDENTICALLY `1` (shear det is exact `1`, blow-up det is an
exact monomial). Generalizes `coG_hjac` to `Fin D` + arbitrary block sizes / pivots. -/
theorem shearBlowup_hjac {S : Finset (Fin D)} {p : Fin D} (hp : p ∈ S)
    (sh : (Fin D → ℝ) → (Fin D → ℝ)) (hsh_diff : Differentiable ℝ sh)
    (hsh_jac : ∀ w, jacDet sh w = 1) (u : Fin D → ℝ) :
    |jacDet (sh ∘ blockBlowupMap S p) u| = jacWeight (singleJac S p) u * |(1 : ℝ)| := by
  rw [abs_jacDet_shear_comp_blockBlowup hp sh hsh_diff hsh_jac, jacWeight_singleJac, abs_one,
    mul_one]

/-- **L6 for the `outerShear` chart step.** The coupled general-`d` chart step `outerShear corr ∘
blockBlowupMap S p` has the dom-wide unit ≡ 1 Jacobian — the direct instantiation of
`shearBlowup_hjac` by the general rank-1 shear. This is the general-`d` `coG_hjac`. -/
theorem outerShearBlowup_hjac (corr : Fin D → Option (Fin D × Fin D))
    (hsrc : ∀ i a b, corr i = some (a, b) → corr a = none ∧ corr b = none)
    {S : Finset (Fin D)} {p : Fin D} (hp : p ∈ S) (u : Fin D → ℝ) :
    |jacDet (outerShear corr ∘ blockBlowupMap S p) u| = jacWeight (singleJac S p) u * |(1 : ℝ)| :=
  shearBlowup_hjac hp (outerShear corr) (differentiable_outerShear corr)
    (jacDet_outerShear corr hsrc) u

/-- **L6 — a.e.-injectivity** off the null pivot hyperplane `{u_p = 0}` for the coupled chart step
(`Chart.hg_inj`/`hexcep_null` content), given the block source hypothesis. -/
theorem outerShearBlowup_injOn (corr : Fin D → Option (Fin D × Fin D))
    (hsrc : ∀ i a b, corr i = some (a, b) → corr a = none ∧ corr b = none)
    {S : Finset (Fin D)} {p : Fin D} (hp : p ∈ S) :
    Set.InjOn (outerShear corr ∘ blockBlowupMap S p)
      (Set.univ \ {w : Fin D → ℝ | w p = 0}) :=
  centerCoordAligned_of_injective (outerShear corr) hp (injective_outerShear corr hsrc)

/-! ### §3b — the PATH composite along a branch: `|jacDet|` = product of monomials, unit ≡ 1

Aoyagi's leaf charts are MULTI-step composites `g_c = ∘_j (shear_j ∘ blockBlowupMap S_j p_j)` down a
root→leaf branch. The composite `|jacDet g_c u|` is the PRODUCT of the per-step blow-up monomials
(each evaluated at the running partial composition), with NO residual unit factor — the shears
contribute exactly `1` at every step. So the dom-wide unit is IDENTICALLY `1` along the whole
branch, not merely per step (the germ-only trap void, at branch scale). -/

/-- One **geo step** of a resolution branch: a block-center `S ∋ p` and a unit-Jacobian shear. -/
structure GeoStep (D : ℕ) where
  /-- The blow-up center. -/
  S : Finset (Fin D)
  /-- The pivot. -/
  p : Fin D
  /-- The pivot is in the center. -/
  hp : p ∈ S
  /-- The (unipotent) shear applied after the block blow-up. -/
  shear : (Fin D → ℝ) → (Fin D → ℝ)
  /-- The shear is differentiable. -/
  hshear_diff : Differentiable ℝ shear
  /-- The shear's Jacobian is exactly `1` (the shear-pin). -/
  hshear_jac : ∀ w, jacDet shear w = 1

/-- The step's coordinate change `shear ∘ blockBlowupMap S p` (block blow-up outermost within the
step, shear inner). -/
def GeoStep.stepMap (g : GeoStep D) : (Fin D → ℝ) → (Fin D → ℝ) :=
  g.shear ∘ blockBlowupMap g.S g.p

/-- The step map is differentiable. -/
theorem GeoStep.differentiable_stepMap (g : GeoStep D) : Differentiable ℝ g.stepMap :=
  g.hshear_diff.comp (differentiable_blockBlowupMap g.S g.p)

/-- **The branch Jacobian monomial** — the product, down the branch, of each step's blow-up monomial
`|(partial composition of deeper steps)_{p}|^(|S|−1)`. Manifestly a product of monomials (no unit
factor): this IS the "`unit ≡ 1` identically" content at branch scale. -/
def geoPathWeight : List (GeoStep D) → (Fin D → ℝ) → ℝ
  | [], _ => 1
  | s :: rest, u =>
      |(pathMap (rest.map GeoStep.stepMap) u) s.p| ^ (s.S.card - 1) * geoPathWeight rest u

/-- **L6, PATH composite (unit ≡ 1 down the whole branch).** `|jacDet (pathMap branch) u| =
geoPathWeight branch u` — the composite Jacobian is EXACTLY the product of the per-step blow-up
monomials, with no residual unit. Cons-induction on the branch: `abs_jacDet_pathMap_cons` peels the
head, `abs_jacDet_shear_comp_blockBlowup` turns it into the head monomial (shear det ≡ 1), the IH
handles the tail. The general-`d`, multi-step generalization of `jacDet_coG` (a single step). -/
theorem abs_jacDet_geoPath (steps : List (GeoStep D)) (u : Fin D → ℝ) :
    |jacDet (pathMap (steps.map GeoStep.stepMap)) u| = geoPathWeight steps u := by
  induction steps generalizing u with
  | nil => simp [geoPathWeight, pathMap_nil, jacDet_id]
  | cons s rest ih =>
    have hdiffRest : Differentiable ℝ (pathMap (rest.map GeoStep.stepMap)) :=
      differentiable_pathMap _ (by
        intro σ hσ
        obtain ⟨g, _, rfl⟩ := List.mem_map.mp hσ
        exact g.differentiable_stepMap)
    rw [List.map_cons,
      abs_jacDet_pathMap_cons s.stepMap (rest.map GeoStep.stepMap) u
        (s.differentiable_stepMap _) (hdiffRest u),
      show s.stepMap = s.shear ∘ blockBlowupMap s.S s.p from rfl,
      abs_jacDet_shear_comp_blockBlowup s.hp s.shear s.hshear_diff s.hshear_jac, ih]
    rfl

/-! ## §4 — L7 assembly: the general-depth, varying-center fan cover -/

/-- One **fan step**: a nonempty center `S ⊆ Fin D` and a per-pivot shear family. A LIST of these is
a root→leaf branch of the resolution tree (varying centers, varying shears, arbitrary depth). -/
structure FanStep (D : ℕ) where
  /-- The (nonempty) blow-up center at this step. -/
  center : Finset (Fin D)
  /-- The center is nonempty (there is a pivot). -/
  hne : center.Nonempty
  /-- The per-pivot shear applied at this step. -/
  shear : Fin D → (Fin D → ℝ) → (Fin D → ℝ)

/-- **The fan tree of a step list.** An empty list is a leaf box `closedBall 0 R`; a `s :: rest` is
a full pivot fan over `s.center` with per-pivot shear `s.shear`, each child the fan of `rest` at the
inflated radius `f (max R 1)`. The list length is the DEPTH (arbitrary); the centers/shears VARY per
step (item 3 of the brief). -/
def fanOfSteps (f : ℝ → ℝ) : List (FanStep D) → ℝ → FanTree D
  | [], R => FanTree.leaf (closedBall 0 R)
  | s :: rest, R =>
      FanTree.node s.center s.hne s.shear (fun _ ↦ fanOfSteps f rest (f (max R 1)))

/-- **L7 assembly, GENERAL depth + varying centers.** If every step's shear box-contains under the
inflation `f` at EVERY radius (`closedBall 0 t ⊆ shear p '' closedBall 0 (f t)`), then the step-list
fan `Covers f · R` at any target radius `R`. Proved by induction on the step list — the depth is the
list length (arbitrary), the centers/shears vary per step, and the radius bookkeeping is exactly the
`f (max R 1)` propagation the `Covers` fold does (item 5). Generalizes `covers_coTree` (hardcoded
depth-2, one center, one shear) to the real varying-branch shape. -/
theorem covers_fanOfSteps {f : ℝ → ℝ} :
    ∀ (steps : List (FanStep D)) (R : ℝ),
      (∀ s ∈ steps, ∀ p ∈ s.center, ∀ t : ℝ,
        closedBall 0 t ⊆ s.shear p '' closedBall 0 (f t)) →
      FanTree.Covers f (fanOfSteps f steps R) R
  | [], R, _ => by
      change closedBall (0 : Fin D → ℝ) R ⊆ closedBall 0 R
      exact subset_rfl
  | s :: rest, R, hstep => by
      refine ⟨fun p _ ↦ hstep s (List.mem_cons.mpr (Or.inl rfl)) p ‹_› (max R 1), fun p _ ↦ ?_⟩
      exact covers_fanOfSteps rest (f (max R 1))
        (fun s' hs' ↦ hstep s' (List.mem_cons.mpr (Or.inr hs')))

/-- **The general-`d` `hcover` shape (`∃ ρ > 0`).** A ball around `0` lies inside the step-list
fan's leaf-chart images, whenever every step box-contains under `f = r ↦ r + r²` at every radius.
This is the L7 `hcover` contribution for a general resolution branch (arbitrary depth, varying
centers) — `covers_fanOfSteps` fed to the `LeafCoverTiling` engine. -/
theorem exists_ball_subset_fanOfSteps_leafImages (steps : List (FanStep D))
    (hstep : ∀ s ∈ steps, ∀ p ∈ s.center, ∀ t : ℝ,
      closedBall 0 t ⊆ s.shear p '' closedBall 0 (t + t ^ 2)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ball (0 : Fin D → ℝ) ρ ⊆ (fanOfSteps (fun r ↦ r + r ^ 2) steps 1).leafImages :=
  FanTree.exists_ball_subset_leafImages _ (covers_fanOfSteps steps 1 hstep)

/-- **The general-`d` coupled cover — every step an `outerShear`.** When each step's shear (for
every pivot) is the general rank-1 `outerShear corr` with kept sources, the fan closes: a ball
around `0` is covered by the leaf-chart images, arbitrary depth, varying centers. The full
general-`d` analogue of `exists_ball_subset_coTree_leafImages` — the per-edge box-containment
(`outerShear_covers`) assembled by the engine over the WHOLE varying branch. -/
theorem exists_ball_subset_outerFan_leafImages
    (steps : List (FanStep D))
    (hout : ∀ s ∈ steps, ∃ corr : Fin D → Option (Fin D × Fin D),
      (∀ i a b, corr i = some (a, b) → corr a = none ∧ corr b = none) ∧
      s.shear = fun _ ↦ outerShear corr) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ball (0 : Fin D → ℝ) ρ ⊆ (fanOfSteps (fun r ↦ r + r ^ 2) steps 1).leafImages := by
  refine exists_ball_subset_fanOfSteps_leafImages steps (fun s hs p _ t ↦ ?_)
  obtain ⟨corr, hsrc, hsh⟩ := hout s hs
  rw [hsh]
  exact outerShear_covers corr hsrc

/-! ## §5 — the forced axiom gate (rev-render / controller `#print axioms`)

The general-`d` L6/L7 mechanisms rest only on `[propext, Classical.choice, Quot.sound]` — a future
edit that makes any depend on `sorryAx` FAILS this red (not masked by a stale-olean `exit 0`;
lean/CLAUDE.md caveat). -/
#assert_banked_clean_batch [blockShear_covers_of_norm_bound, outerDisp_norm_bound, outerDisp_zero,
  fderiv_outerDisp_zero, outerShear_covers, jacDet_outerShear, injective_outerShear,
  abs_jacDet_shear_comp_blockBlowup, shearBlowup_hjac, outerShearBlowup_hjac,
  outerShearBlowup_injOn, abs_jacDet_geoPath, covers_fanOfSteps,
  exists_ball_subset_fanOfSteps_leafImages, exists_ball_subset_outerFan_leafImages]

end DLNFibre.DLN.Aoyagi.GeneralGeoAtlas
