import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialInt
import DLNFibre.DLN.RLCT.Validate.RouteMSJGramResidual
import DLNFibre.DLN.RLCT.Validate.RouteMSJProjRadial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.PosDef

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJQBoxCore` — the abstract Q-box integrability core

**Thread `genm-catI-integrability`, Cat I good-stratum keystone.** The network-free integrability
core the paper's Cat I stratum bottoms out on:

    ∫⁻_{Q ∈ box} det(Q Qᵀ)^{−a/2} < ⊤   whenever   a < q − b + 1,

where `Q` ranges over the box `(ball 0 R)^b` of `b`-tuples of vectors in `ℝ^q` (rows of a `b × q`
matrix), `Q Qᵀ = gram ℝ Q` is the Gram matrix of the rows, and the exponent bound `q − b + 1` is the
codimension of the rank-`< b` (determinantal) locus. Everything is in `∫⁻` / `ENNReal`, so Tonelli
applies unconditionally.

Proof: a Tonelli row-recursion on `b`. Peel one row `w` (measure-preserving
`piFinSuccAbove` split + `setLIntegral_prod_symm`); the Gram determinant factors
(`RouteMSJGramResidual.det_gram_cons`) as `det(gram rest) · ‖P_{V⊥} w‖²` with `V = span(rows)`,
so the
`w`-integral is a projection radial integral bounded uniformly by the piece-P2 constant
(`RouteMSJProjRadial.projection_rpow_lintegral_uniform`, with `dim V⊥ ≥ q − b + 1 > a`); the outer
integral is the `(b−1)`-row instance (IH). Base `b = 0`: the Gram is the empty matrix, `det = 1`,
integrand `≡ 1`, integral `= vol(point) < ⊤`.

## Scope / carried interfaces (NOT proved here)
This is the abstract, free-`Q` core. It is the **leaf** of the DLN Cat I reduction; the two
DLN-facing
steps that feed it are carried as separate interfaces (see the statement card):
* the absorption change-of-variables (integrate out `A₀`), and
* the product-structure / atom recursion `corankGram(A') = Q_b Q_bᵀ`, `Q_b = Y·A_{≥2}` — this does
  **not** fold cleanly into `[this core] ∘ [loss IH]`; it recurses one chain-length deeper into the
  `(S, J)` atom (task #111 / sjdecomp). This core is where that recursion bottoms out (the
  dominant-minor chart, `J = unit`).

S2-FREE: pure measure theory + the two landed bricks. Intended axiom footprint
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Matrix
open scoped ENNReal InnerProductSpace

/-- `(d · t²)^{−a/2} = d^{−a/2} · t^{−a}` for `d, t ≥ 0` (the row-peel integrand split). -/
private lemma rpow_mul_sq (a d t : ℝ) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    (d * t ^ 2) ^ (-a / 2) = d ^ (-a / 2) * t ^ (-a) := by
  rw [Real.mul_rpow hd (by positivity)]
  congr 1
  rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht]
  congr 1
  push_cast
  ring

/-- Measurability of the Q-box integrand `Q ↦ ofReal(det(gram Q)^{−a/2})`. -/
private lemma measurable_gramDetRpow (a : ℝ) (m : ℕ) :
    Measurable (fun Q : Fin m → EuclideanSpace ℝ (Fin q) =>
      ENNReal.ofReal ((Matrix.gram ℝ Q).det ^ (-a / 2))) := by
  have hcont : Continuous
      (fun Q : Fin m → EuclideanSpace ℝ (Fin q) => (Matrix.gram ℝ Q).det) := by
    apply Continuous.matrix_det
    refine continuous_matrix (fun i j => ?_)
    simp only [Matrix.gram_apply]
    fun_prop
  exact ENNReal.measurable_ofReal.comp
    (((by fun_prop : Measurable (fun t : ℝ => t ^ (-a / 2)))).comp hcont.measurable)

/-- **Row peel (Tonelli).** The box integral over `b+1` rows equals the iterated integral: outer
over
the first `b` rows, inner over the prepended row `w`. Measure-preserving `piFinSuccAbove` split. -/
private lemma lintegral_box_succ_eq {n : ℕ} (R : ℝ)
    (F : (Fin (n + 1) → EuclideanSpace ℝ (Fin q)) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ Q in Set.univ.pi (fun _ : Fin (n + 1) => Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R), F Q)
      = ∫⁻ rest in Set.univ.pi (fun _ : Fin n => Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R),
          ∫⁻ w in Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R, F (Fin.cons w rest) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin q)) 0
    with he
  have hmp : MeasurePreserving e (volume : Measure (Fin (n + 1) → EuclideanSpace ℝ (Fin q)))
      ((volume : Measure (EuclideanSpace ℝ (Fin q))).prod
        (volume : Measure (Fin n → EuclideanSpace ℝ (Fin q)))) := by
    have h := measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => (volume : Measure (EuclideanSpace ℝ (Fin q)))) 0
    simpa only [← volume_pi] using h
  have hpre : e ⁻¹' ((Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R) ×ˢ
      Set.univ.pi (fun _ : Fin n => Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R))
      = Set.univ.pi (fun _ : Fin (n + 1) => Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R) := by
    ext Q
    simp only [he, MeasurableEquiv.piFinSuccAbove_apply, Set.mem_preimage, Set.mem_prod,
      Set.mem_pi, Set.mem_univ, true_implies]
    rw [Fin.forall_fin_succ]
    tauto
  have hCoV := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding (F ∘ e.symm)
    ((Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R) ×ˢ
      Set.univ.pi (fun _ : Fin n => Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R))
  rw [hpre] at hCoV
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] at hCoV
  rw [hCoV, setLIntegral_prod_symm (fun p => F (e.symm p))
    ((hF.comp e.symm.measurable).aemeasurable)]
  refine lintegral_congr fun rest => lintegral_congr fun w => ?_
  congr 1
  rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
  simp [Fin.insertNthEquiv, Fin.insertNth_zero']

/-- **The abstract Q-box integrability core.** For `Q` ranging over the box of `b`-tuples of
`ℝ^q`-vectors (rows), `∫⁻ det(Q Qᵀ)^{−a/2} < ⊤` whenever `a < q − b + 1`. Tonelli row-recursion on
`b`, consuming the Gram row-residual factorisation (`det_gram_cons`) and the uniform projection
radial
bound (`projection_rpow_lintegral_uniform`). -/
theorem qbox_lintegral_lt_top {q : ℕ} {a : ℝ} :
    ∀ (b : ℕ), b ≤ q → a < (q : ℝ) - (b : ℝ) + 1 → ∀ (R : ℝ),
      (∫⁻ Q in Set.univ.pi (fun _ : Fin b => Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R),
        ENNReal.ofReal ((Matrix.gram ℝ Q).det ^ (-a / 2))) < ⊤ := by
  intro b
  induction b with
  | zero =>
      intro _ _ R
      have hint : (fun Q : Fin 0 → EuclideanSpace ℝ (Fin q) =>
          ENNReal.ofReal ((Matrix.gram ℝ Q).det ^ (-a / 2))) = fun _ => 1 := by
        funext Q; rw [Matrix.det_fin_zero, Real.one_rpow, ENNReal.ofReal_one]
      rw [hint, MeasureTheory.setLIntegral_one]
      exact measure_lt_top _ _
  | succ n ih =>
      intro hbq ha R
      push_cast at ha
      -- the P2 uniform constant, at rank `r = q − n`
      have hrn : n < q := by omega
      have hr1 : 1 ≤ q - n := by omega
      have hrq : q - n ≤ q := by omega
      have haC : a < ((q - n : ℕ) : ℝ) := by
        rw [Nat.cast_sub (le_of_lt hrn)]; linarith
      obtain ⟨C, hC_top, hC⟩ :=
        projection_rpow_lintegral_uniform q (q - n) hr1 hrq haC R
      -- inductive hypothesis at `b = n`
      have hIH : (∫⁻ rest in Set.univ.pi
            (fun _ : Fin n => Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R),
          ENNReal.ofReal ((Matrix.gram ℝ rest).det ^ (-a / 2))) < ⊤ :=
        ih (by omega) (by linarith) R
      -- peel the top row
      rw [lintegral_box_succ_eq R _ (measurable_gramDetRpow a (n + 1))]
      calc
        (∫⁻ rest in Set.univ.pi
              (fun _ : Fin n => Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R),
            ∫⁻ w in Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R,
              ENNReal.ofReal ((Matrix.gram ℝ (Fin.cons w rest)).det ^ (-a / 2)))
            ≤ ∫⁻ rest in Set.univ.pi
                (fun _ : Fin n => Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R),
              ENNReal.ofReal ((Matrix.gram ℝ rest).det ^ (-a / 2)) * C := by
          refine lintegral_mono fun rest => ?_
          -- rewrite the inner integrand via the Gram row-residual factorisation
          have hsplit : (fun w : EuclideanSpace ℝ (Fin q) =>
                ENNReal.ofReal ((Matrix.gram ℝ (Fin.cons w rest)).det ^ (-a / 2)))
              = fun w => ENNReal.ofReal ((Matrix.gram ℝ rest).det ^ (-a / 2))
                  * ENNReal.ofReal
                      (‖(Submodule.span ℝ (Set.range rest))ᗮ.starProjection w‖ ^ (-a)) := by
            have hdr : 0 ≤ (Matrix.gram ℝ rest).det :=
              Matrix.PosSemidef.det_nonneg (Matrix.posSemidef_gram ℝ rest)
            funext w
            rw [det_gram_cons rest w, rpow_mul_sq a _ _ hdr (norm_nonneg _),
              ENNReal.ofReal_mul (Real.rpow_nonneg hdr _)]
          rw [hsplit, MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          -- finrank of the orthogonal complement is ≥ q − n
          have hfin : q - n ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range rest))ᗮ := by
            have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range rest)) ≤ n := by
              have := finrank_range_le_card (R := ℝ) rest
              simpa only [Set.finrank, Fintype.card_fin] using this
            have h2 := Submodule.finrank_add_finrank_orthogonal
              (K := Submodule.span ℝ (Set.range rest))
            rw [finrank_euclideanSpace_fin] at h2
            omega
          gcongr
          exact hC _ hfin
        _ = (∫⁻ rest in Set.univ.pi
              (fun _ : Fin n => Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R),
            ENNReal.ofReal ((Matrix.gram ℝ rest).det ^ (-a / 2))) * C := by
          rw [lintegral_mul_const' _ _ hC_top.ne]
        _ < ⊤ := ENNReal.mul_lt_top hIH hC_top

/-- Non-vacuity witness: the hypotheses are satisfiable at genuinely singular data — `q = 2`,
`b = 1`, exponent `a = 1` (`1 < 2 = q − b + 1`), where the integrand `‖w‖^{−1}` has a real
(non-removable) singularity at the origin, and the integral is finite. -/
example (R : ℝ) :
    (∫⁻ Q in Set.univ.pi (fun _ : Fin 1 => Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R),
      ENNReal.ofReal ((Matrix.gram ℝ Q).det ^ (-(1 : ℝ) / 2))) < ⊤ :=
  qbox_lintegral_lt_top 1 (by norm_num) (by norm_num) R

end DLNFibre.DLN.RLCT
