import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeScalar
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeCShift` — the corank-one edge C-shift bound (R2)

Thread `genm-tideD` (aoyagi-full Stage 2). The **C-shift change-of-variables** brick of satred's corank-one
edge peel: the `C`-integral of the shifted fragile residual over the pivot box is dominated by the
`a`-dimensional scaled radial (`scaledRadialEuclid`, landed in `RouteMSJEdgeScalar`).

For a nonzero fragile direction `v : Fin (u+1) → ℝ` (`v = Q̃ₚ·ω`), a fixed shift `β : Fin a → ℝ`
(`β = σ·Γη`, `C`-independent), and pivot energy `W > 0`:

    ∫_{C ∈ [−1,1]^{a×(u+1)}} (W + ‖(of C).mulVec v + β‖²)^{−c'} dC  ≤  K(v) · ∫_{ζ∈ℝ^a} (W + ‖ζ‖²)^{−c'} dζ,

with `K(v) = 2^{a·u}·|v_{j₀}|^{−a}` (`j₀` any index with `v_{j₀}≠0`). The bound is **β-invariant** (the
RHS is β-free: after the a-fortiori box→ℝ^a enlargement, Lebesgue translation invariance absorbs the
shift — the finite-box integral itself is β-dependent, only its ℝ^a-enlargement is not) and the RHS is exactly
`scaledRadialEuclid = W^{a/2−c'}·B`, `B = ∫_{ℝ^a}(1+‖s‖²)^{−c'}`. `B` is FINITE exactly for `a < 2c'`
(`japaneseBracket_euclid_lt_top`), i.e. in the edge window `c' > a/2` (`= (M₀−u)(M₁−u)/2` for the
corank-one column), where the RHS gives the clean corank charge `W^{a/2−c'}` — NO log. (At `c' = a/2`
the full-space RHS DIVERGES to `+∞`; the corank-one tie-log is a property of a BOUNDED/cutoff radial, NOT
this full-space comparator, and the edge window's strict lower bound excludes `c' = a/2` — reviewer/Codex,
correcting an earlier "RHS ≍ log(1/W)" gloss.) Consultant-converged (dbuild/edgebrick/satred): the column
substitution `C ↦ C·Λ` (`Λ = I` with column `j₀` replaced by `v`, `det Λ = v_{j₀}`) realises the bounded
pushforward density.

## What lands here
* `affineScale_pi_le` — the `a`-dimensional core atom: the scaled-and-shifted box integral over
  `Fin a → ℝ` is `≤ (|v₀|^a)⁻¹ · (full-space radial)`. The genuinely-new measure-theoretic content:
  box→ℝ^a a-fortiori enlargement + `map_addHaar_smul` Jacobian `|v₀|^{−a}` + translation invariance
  (β-absorption).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators

/-- **The pi-radial equals the Euclidean radial (`scaledRadialEuclid` LHS).** The sum-of-squares radial
over the plain product space `Fin a → ℝ` equals the norm-squared radial over `EuclideanSpace ℝ (Fin a)`:
`∫⁻ z:Fin a→ℝ, (W+∑ᵢzᵢ²)^{−c'} = ∫⁻ x:EuclideanSpace ℝ (Fin a), (W+‖x‖²)^{−c'}`. Via the volume-preserving
`ofLp` (`PiLp.volume_preserving_ofLp`) and `EuclideanSpace.real_norm_sq_eq` (`‖x‖² = ∑ᵢ(xᵢ)²`). Bridges
the C-shift bound's pi output to the landed `scaledRadialEuclid`. -/
theorem radial_pi_eq_euclid {a : ℕ} {W c' : ℝ} (hW : 0 < W) :
    (∫⁻ z : Fin a → ℝ, ENNReal.ofReal ((W + ∑ i, (z i) ^ 2) ^ (-c')))
      = ∫⁻ x : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((W + ‖x‖ ^ 2) ^ (-c')) := by
  have hmeas : Measurable (fun z : Fin a → ℝ => ENNReal.ofReal ((W + ∑ i, (z i) ^ 2) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    have hbase : Continuous (fun z : Fin a → ℝ => W + ∑ i, (z i) ^ 2) := by fun_prop
    exact (hbase.rpow_const (fun z => Or.inl (by positivity))).measurable
  have hcomp := (PiLp.volume_preserving_ofLp (ι := Fin a)).lintegral_comp hmeas
  rw [← hcomp]
  refine lintegral_congr (fun x => ?_)
  rw [EuclideanSpace.real_norm_sq_eq]

/-- **The `a`-dimensional affine-scale box bound (R2 core atom).** For `v₀ ≠ 0`, a shift `β : Fin a → ℝ`,
`W > 0`, and any exponent `c'`, the box integral of the scaled-and-shifted radial is dominated by the
reciprocal-Jacobian multiple of the full-space radial:

    ∫_{y ∈ [−1,1]^a} (W + ∑ᵢ (v₀·yᵢ + βᵢ)²)^{−c'} dy  ≤  (|v₀|^a)⁻¹ · ∫_{z : Fin a → ℝ} (W + ∑ᵢ zᵢ²)^{−c'} dz.

Proof: enlarge the box to all of `ℝ^a` (a-fortiori, integrand `≥ 0`); substitute `z = v₀ • y`
(`map_addHaar_smul`, Jacobian `|v₀|^{−a}`); absorb the shift `β` by translation invariance
(`lintegral_add_right_eq_self`). The `|v₀|^{−a}` factor is the single-column Jacobian of the C-shift
CoV; the β-invariance is why the C-integration absorbs the shift (satred). -/
theorem affineScale_pi_le {a : ℕ} {v₀ : ℝ} (hv₀ : v₀ ≠ 0) (β : Fin a → ℝ) {W c' : ℝ} (hW : 0 < W) :
    (∫⁻ y in Set.pi Set.univ (fun _ : Fin a => Set.Icc (-1 : ℝ) 1),
        ENNReal.ofReal ((W + ∑ i, (v₀ * y i + β i) ^ 2) ^ (-c')))
      ≤ ENNReal.ofReal ((|v₀| ^ a)⁻¹)
          * ∫⁻ z : Fin a → ℝ, ENNReal.ofReal ((W + ∑ i, (z i) ^ 2) ^ (-c')) := by
  classical
  -- `G z = (W + ∑ (zᵢ + βᵢ)²)^{−c'}` — the shifted full-space integrand
  set G : (Fin a → ℝ) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal ((W + ∑ i, (z i + β i) ^ 2) ^ (-c')) with hG
  have hGmeas : Measurable G := by
    apply ENNReal.measurable_ofReal.comp
    have hbase : Continuous (fun z : Fin a → ℝ => W + ∑ i, (z i + β i) ^ 2) := by fun_prop
    exact (hbase.rpow_const (fun z => Or.inl (by positivity))).measurable
  -- Step 1: box → ℝ^a (a-fortiori; the LHS integrand is `G (v₀ • y)`)
  have hbox : (∫⁻ y in Set.pi Set.univ (fun _ : Fin a => Set.Icc (-1 : ℝ) 1),
        ENNReal.ofReal ((W + ∑ i, (v₀ * y i + β i) ^ 2) ^ (-c')))
      ≤ ∫⁻ y : Fin a → ℝ, G (v₀ • y) := by
    refine (lintegral_mono_set (Set.subset_univ _)).trans_eq ?_
    rw [Measure.restrict_univ]
    refine lintegral_congr (fun y => ?_)
    simp only [hG, Pi.smul_apply, smul_eq_mul]
  -- Step 2: scale CoV `z = v₀ • y` (Jacobian `|v₀|^{−a}` via `map_addHaar_smul`)
  have hscale : (∫⁻ y : Fin a → ℝ, G (v₀ • y))
      = ENNReal.ofReal ((|v₀| ^ a)⁻¹) * ∫⁻ z : Fin a → ℝ, G z := by
    have hmap := MeasureTheory.Measure.map_addHaar_smul
      (μ := (volume : Measure (Fin a → ℝ))) hv₀
    rw [Module.finrank_fin_fun] at hmap
    have hlm := lintegral_map (μ := (volume : Measure (Fin a → ℝ))) hGmeas
      (measurable_const_smul v₀)
    rw [hmap, lintegral_smul_measure] at hlm
    rw [← hlm, show |(v₀ ^ a)⁻¹| = (|v₀| ^ a)⁻¹ from by rw [abs_inv, abs_pow], smul_eq_mul]
  -- Step 3: translation invariance absorbs `β`
  have htrans : (∫⁻ z : Fin a → ℝ, G z)
      = ∫⁻ z : Fin a → ℝ, ENNReal.ofReal ((W + ∑ i, (z i) ^ 2) ^ (-c')) := by
    have := lintegral_add_right_eq_self
      (μ := (volume : Measure (Fin a → ℝ)))
      (fun z : Fin a → ℝ => ENNReal.ofReal ((W + ∑ i, (z i) ^ 2) ^ (-c'))) β
    simpa only [hG, Pi.add_apply] using this
  calc (∫⁻ y in Set.pi Set.univ (fun _ : Fin a => Set.Icc (-1 : ℝ) 1),
          ENNReal.ofReal ((W + ∑ i, (v₀ * y i + β i) ^ 2) ^ (-c')))
      ≤ ∫⁻ y : Fin a → ℝ, G (v₀ • y) := hbox
    _ = ENNReal.ofReal ((|v₀| ^ a)⁻¹) * ∫⁻ z : Fin a → ℝ, G z := hscale
    _ = ENNReal.ofReal ((|v₀| ^ a)⁻¹)
          * ∫⁻ z : Fin a → ℝ, ENNReal.ofReal ((W + ∑ i, (z i) ^ 2) ^ (-c')) := by rw [htrans]

/-- **The corank-one edge C-shift bound (R2), matrix form.** For a fragile direction `v : Fin (u+1) → ℝ`
with a nonzero pivot coordinate `v j₀ ≠ 0`, a fixed shift `β : Fin a → ℝ`, and pivot energy `W > 0`, the
`C`-integral of the shifted fragile residual `(of C).mulVec v + β` over the pivot box `[−1,1]^{a×(u+1)}` is
dominated by `K · scaledRadialEuclid`, where `K = 2^{a·u}·|v j₀|^{−a}` is the (β-independent, `v`-only)
density constant and the radial `∫_{ℝ^a}(W+‖x‖²)^{−c'}` (= `scaledRadialEuclid`) carries the `W^{a/2−c'}`
pivot-energy dependence into the arity−1 comparator.

Proof: peel column `j₀` (`piCongrRight (piFinSuccAbove j₀)` ∘ `arrowProdEquivProdArrow`, volume-preserving);
the shifted-radial factors through the peeled column as `(of C).mulVec v i = v_{j₀}·C_{i,j₀} + rᵢ(rest)`
(`Fin.sum_univ_succAbove`); Fubini with the column inner (`setLIntegral_prod_symm`); apply the core atom
`affineScale_pi_le` per transverse slice (`|v j₀|^{−a}` Jacobian, β-invariant); integrate the constant over
the transverse box (`volume = 2^{a·u}`); bridge the pi-radial to the Euclidean one (`radial_pi_eq_euclid`).
`{v=0}` is NOT an R2 case — the assembly disposes it via the reduced chain (satred). -/
theorem edge_C_shift_bound {a u : ℕ} (v : Fin (u + 1) → ℝ) (j₀ : Fin (u + 1)) (hj₀ : v j₀ ≠ 0)
    (β : Fin a → ℝ) {W c' : ℝ} (hW : 0 < W) :
    (∫⁻ C in Set.pi Set.univ (fun _ : Fin a => Set.pi Set.univ (fun _ : Fin (u + 1) => Set.Icc (-1 : ℝ) 1)),
        ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v i + β i) ^ 2) ^ (-c')))
      ≤ ENNReal.ofReal (2 ^ (a * u) * (|v j₀| ^ a)⁻¹)
          * ∫⁻ x : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((W + ‖x‖ ^ 2) ^ (-c')) := by
  classical
  -- the boxes
  set Icc1 : Set ℝ := Set.Icc (-1 : ℝ) 1 with hIcc1
  set cubeA : Set (Fin a → ℝ) := Set.pi Set.univ (fun _ : Fin a => Icc1) with hcubeA
  set cubeT : Set (Fin a → Fin u → ℝ) :=
    Set.pi Set.univ (fun _ : Fin a => Set.pi Set.univ (fun _ : Fin u => Icc1)) with hcubeT
  set boxC : Set (Fin a → Fin (u + 1) → ℝ) :=
    Set.pi Set.univ (fun _ : Fin a => Set.pi Set.univ (fun _ : Fin (u + 1) => Icc1)) with hboxC
  -- the column-peel volume-preserving equiv (col j₀ ↦ first factor)
  set e : (Fin a → Fin (u + 1) → ℝ) ≃ᵐ (Fin a → ℝ) × (Fin a → Fin u → ℝ) :=
    (MeasurableEquiv.piCongrRight
        (fun _ : Fin a => MeasurableEquiv.piFinSuccAbove (fun _ : Fin (u + 1) => ℝ) j₀)).trans
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin u → ℝ) (Fin a)) with he_def
  have he : MeasurePreserving e :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ (Fin u → ℝ) (Fin a)).comp
      (volume_preserving_pi
        (fun _ : Fin a => volume_preserving_piFinSuccAbove (fun _ : Fin (u + 1) => ℝ) j₀))
  have hap : ∀ C : Fin a → Fin (u + 1) → ℝ,
      e C = (fun i => C i j₀, fun i k => C i (j₀.succAbove k)) := fun C => rfl
  -- the shift induced by the transverse columns
  set r : (Fin a → Fin u → ℝ) → Fin a → ℝ :=
    fun ct i => ∑ k, ct i k * v (j₀.succAbove k) with hr
  -- the transported (peeled) integrand
  set Fp : (Fin a → ℝ) × (Fin a → Fin u → ℝ) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((W + ∑ i, (v j₀ * p.1 i + (r p.2 i + β i)) ^ 2) ^ (-c')) with hFp
  have hFpmeas : Measurable Fp := by
    apply ENNReal.measurable_ofReal.comp
    have hbase : Continuous (fun p : (Fin a → ℝ) × (Fin a → Fin u → ℝ) =>
        W + ∑ i, (v j₀ * p.1 i + (r p.2 i + β i)) ^ 2) := by
      simp only [hr]; fun_prop
    exact (hbase.rpow_const (fun p => Or.inl (by positivity))).measurable
  -- Step A: box preimage identity `e ⁻¹' (cubeA ×ˢ cubeT) = boxC`
  have hpre : e ⁻¹' (cubeA ×ˢ cubeT) = boxC := by
    ext C
    simp only [Set.mem_preimage, hap, Set.mem_prod, hcubeA, hcubeT, hboxC, Set.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ i
      exact (Fin.forall_iff_succAbove j₀).2 ⟨h1 i, h2 i⟩
    · intro h
      exact ⟨fun i => h i j₀, fun i k => h i (j₀.succAbove k)⟩
  -- Step B: the integrand factors through the peel `F C = Fp (e C)`
  have hintegrand : ∀ C : Fin a → Fin (u + 1) → ℝ,
      ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v i + β i) ^ 2) ^ (-c')) = Fp (e C) := by
    intro C
    have hsumeq : (∑ i, ((Matrix.of C).mulVec v i + β i) ^ 2)
        = ∑ i, (v j₀ * C i j₀ + ((∑ k, C i (j₀.succAbove k) * v (j₀.succAbove k)) + β i)) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by
        have hsum : (Matrix.of C).mulVec v i
            = C i j₀ * v j₀ + ∑ k, C i (j₀.succAbove k) * v (j₀.succAbove k) := by
          simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
          exact Fin.sum_univ_succAbove (fun j => C i j * v j) j₀
        rw [hsum]; ring)
    simp only [hFp, hap, hr]
    rw [hsumeq]
  -- Step C: rewrite LHS through the transport + Fubini (column inner)
  have hLHS : (∫⁻ C in boxC,
        ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v i + β i) ^ 2) ^ (-c')))
      = ∫⁻ ct in cubeT, ∫⁻ y in cubeA, Fp (y, ct) := by
    rw [show (∫⁻ C in boxC, ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v i + β i) ^ 2) ^ (-c')))
          = ∫⁻ C in boxC, Fp (e C) from lintegral_congr (fun C => hintegrand C),
      ← hpre, he.setLIntegral_comp_preimage_emb e.measurableEmbedding Fp (cubeA ×ˢ cubeT),
      Measure.volume_eq_prod (Fin a → ℝ) (Fin a → Fin u → ℝ),
      setLIntegral_prod_symm Fp hFpmeas.aemeasurable]
  rw [hLHS]
  -- Step D: bound each inner column integral by the core atom (β-invariant, |v j₀|^{−a})
  have hinner : ∀ ct : Fin a → Fin u → ℝ,
      (∫⁻ y in cubeA, Fp (y, ct))
        ≤ ENNReal.ofReal ((|v j₀| ^ a)⁻¹)
            * ∫⁻ z : Fin a → ℝ, ENNReal.ofReal ((W + ∑ i, (z i) ^ 2) ^ (-c')) := by
    intro ct
    have := affineScale_pi_le (a := a) (v₀ := v j₀) hj₀ (fun i => r ct i + β i) (W := W) (c' := c') hW
    refine le_trans (le_of_eq ?_) this
    rfl
  -- Step E: integrate the constant bound over the transverse box (`volume cubeT = 2^{a·u}`)
  have hcubeTvol : volume cubeT = ENNReal.ofReal (2 ^ (a * u)) := by
    rw [hcubeT, volume_pi_pi]
    have hrow : ∀ _ : Fin a,
        (volume : Measure (Fin u → ℝ)) (Set.pi Set.univ (fun _ : Fin u => Icc1))
          = ENNReal.ofReal (2 ^ u) := by
      intro _
      rw [volume_pi_pi]
      simp only [hIcc1, Real.volume_Icc]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        show (1 : ℝ) - (-1) = 2 from by ring, ← ENNReal.ofReal_pow (by norm_num)]
    rw [Finset.prod_congr rfl (fun i _ => hrow i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← ENNReal.ofReal_pow (by positivity), ← pow_mul, Nat.mul_comm u a]
  calc (∫⁻ ct in cubeT, ∫⁻ y in cubeA, Fp (y, ct))
      ≤ ∫⁻ _ct in cubeT, ENNReal.ofReal ((|v j₀| ^ a)⁻¹)
            * ∫⁻ z : Fin a → ℝ, ENNReal.ofReal ((W + ∑ i, (z i) ^ 2) ^ (-c')) :=
        lintegral_mono hinner
    _ = (ENNReal.ofReal ((|v j₀| ^ a)⁻¹)
            * ∫⁻ z : Fin a → ℝ, ENNReal.ofReal ((W + ∑ i, (z i) ^ 2) ^ (-c'))) * volume cubeT := by
        rw [setLIntegral_const]
    _ = ENNReal.ofReal (2 ^ (a * u) * (|v j₀| ^ a)⁻¹)
          * ∫⁻ x : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((W + ‖x‖ ^ 2) ^ (-c')) := by
        rw [hcubeTvol, radial_pi_eq_euclid hW, mul_right_comm,
          ← ENNReal.ofReal_mul (by positivity), mul_comm ((|v j₀| ^ a)⁻¹)]

/-- **The corank-one edge C-shift integral is finite (R2 finiteness).** For `v j₀ ≠ 0`, `W > 0`, and the
radial tail condition `a < 2c'` (the corank charge window), the shifted `C`-integral over the pivot box is
`< ⊤`: bound it (`edge_C_shift_bound`) by `K · scaledRadialEuclid`, finite by `scaledRadialEuclid_lt_top`.
This is the finiteness the edge assembly consumes (per transverse/`W` slice, before the `W`-integral). -/
theorem edge_C_shift_lt_top {a u : ℕ} (v : Fin (u + 1) → ℝ) (j₀ : Fin (u + 1)) (hj₀ : v j₀ ≠ 0)
    (β : Fin a → ℝ) {W c' : ℝ} (hW : 0 < W) (ha : (a : ℝ) < 2 * c') :
    (∫⁻ C in Set.pi Set.univ (fun _ : Fin a => Set.pi Set.univ (fun _ : Fin (u + 1) => Set.Icc (-1 : ℝ) 1)),
        ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v i + β i) ^ 2) ^ (-c'))) < ⊤ :=
  lt_of_le_of_lt (edge_C_shift_bound v j₀ hj₀ β hW)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (scaledRadialEuclid_lt_top hW ha))

/-- **The edge leaf over the free Γ-direction (R2 composed with the P1 free block).** For the `b=1`
corank, `Γ·Q_b = (d•γ)⊗ω` (`γ` the free `a`-vector over the pivot box, `d=‖Q_b‖` a fixed scalar);
integrating the fragile-column residual `‖(of C)·v + d•γ‖²` over BOTH the `C`-box and the free `γ`-box is
`≤ 2^a·(2^{a·u}·|v_{j₀}|^{−a}) · scaledRadialEuclid(W,c')` — the free-direction integral adds only the
finite volume factor `2^a`, NO singularity, a direct consequence of R2's β-invariance
(`edge_C_shift_bound` is uniform in the shift `d•γ`). δ-FREE: in the edge window `c' > a/2` the RHS
`scaledRadialEuclid = W^{a/2−c'}·B` is finite (`B = ∫_{ℝ^a}(1+‖s‖²)^{−c'} < ⊤` for `a < 2c'`) and gives
the clean power `W^{a/2−c'}` — no log at the leaf (the full-space comparator diverges at `c' = a/2`, which
the window excludes; any tie-log/δ-fold is a bounded-radial matter in the downstream `W`-integral). This
exposes the `|v_{j₀}|^{−a}` constant; its DISPOSAL over the reduced params (the exact
`v = Q̃ₚ·ω` structure, `ω` on the fragile sphere ⟹ `|v_{j₀}|^{−a}` bounded by `σ_min(Q̃ₚ)^{−a}`; and
whether R2's dropped-transverse bound suffices or the transverse must be kept) is a SEPARATE step, pending
satred's pinned computation — NOT settled here. -/
theorem edge_leaf_gamma_bound {a u : ℕ} (v : Fin (u + 1) → ℝ) (j₀ : Fin (u + 1)) (hj₀ : v j₀ ≠ 0)
    (d : ℝ) {W c' : ℝ} (hW : 0 < W) :
    (∫⁻ γ in Set.pi Set.univ (fun _ : Fin a => Set.Icc (-1 : ℝ) 1),
        ∫⁻ C in Set.pi Set.univ (fun _ : Fin a => Set.pi Set.univ (fun _ : Fin (u + 1) => Set.Icc (-1 : ℝ) 1)),
          ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v i + d * γ i) ^ 2) ^ (-c')))
      ≤ ENNReal.ofReal (2 ^ a * (2 ^ (a * u) * (|v j₀| ^ a)⁻¹))
          * ∫⁻ x : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((W + ‖x‖ ^ 2) ^ (-c')) := by
  classical
  set radial := ∫⁻ x : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((W + ‖x‖ ^ 2) ^ (-c')) with hradial
  set K : ℝ≥0∞ := ENNReal.ofReal (2 ^ (a * u) * (|v j₀| ^ a)⁻¹) with hK
  have hγvol : volume (Set.pi Set.univ (fun _ : Fin a => Set.Icc (-1 : ℝ) 1))
      = ENNReal.ofReal (2 ^ a) := by
    rw [volume_pi_pi]
    simp only [Real.volume_Icc]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (1 : ℝ) - (-1) = 2 from by ring, ← ENNReal.ofReal_pow (by norm_num)]
  calc (∫⁻ γ in Set.pi Set.univ (fun _ : Fin a => Set.Icc (-1 : ℝ) 1),
          ∫⁻ C in Set.pi Set.univ (fun _ : Fin a => Set.pi Set.univ (fun _ : Fin (u + 1) => Set.Icc (-1 : ℝ) 1)),
            ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v i + d * γ i) ^ 2) ^ (-c')))
      ≤ ∫⁻ _γ in Set.pi Set.univ (fun _ : Fin a => Set.Icc (-1 : ℝ) 1), K * radial :=
        lintegral_mono (fun γ => edge_C_shift_bound v j₀ hj₀ (fun i => d * γ i) hW)
    _ = K * radial * ENNReal.ofReal (2 ^ a) := by rw [setLIntegral_const, hγvol]
    _ = ENNReal.ofReal (2 ^ a * (2 ^ (a * u) * (|v j₀| ^ a)⁻¹)) * radial := by
        rw [hK, mul_right_comm, ← ENNReal.ofReal_mul (by positivity), mul_comm (2 ^ (a * u) * (|v j₀| ^ a)⁻¹)]

/-- Non-vacuity witness: `a = 1`, `u+1 = 2` columns, `v = ![1, 0]` (so `v 0 = 1 ≠ 0`), any shift, `W = 1`,
`c' = 1` (`a = 1 < 2 = 2c'`); the shifted pivot-box integral is finite. -/
example (β : Fin 1 → ℝ) :
    (∫⁻ C in Set.pi Set.univ (fun _ : Fin 1 => Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-1 : ℝ) 1)),
        ENNReal.ofReal ((1 + ∑ i, ((Matrix.of C).mulVec ![1, 0] i + β i) ^ 2) ^ (-(1 : ℝ)))) < ⊤ :=
  edge_C_shift_lt_top ![1, 0] 0 (by norm_num) β (by norm_num) (by norm_num)

end DLNFibre.DLN.RLCT
