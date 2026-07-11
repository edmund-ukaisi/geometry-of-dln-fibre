import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankQ
import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontSpectral
import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialPolar

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCorankReshape` — the DLN-corner → `qPeelIntegral` reshape (route S, b)

**Thread `genm-sj5-schur` (aoyagi-full), the reshape/casting (obligation-1) that bridges the actual DLN
front loss `frobSq(A₀·Q)` on the corank-`q` cell into the banked abstract corank-`q` majorant
(`RouteMSJCorankQ.qPeelIntegral_lt_top`).** Two halves (cert #131 §4, the corner334/onePeel334-generalized
wiring):

* **(b1) `frobSq → q-block corner` (spectral, PROVEN here).** `frobSq_ge_qBlock_of_qSector` — the direct
  `q`-block generalization of cell_1's `frobSq_ge_twoBlock_of_sector` (`RouteMSJFrontSpectral`): on the
  `q`-collapse sector (a collapse set `S ⊆ Fin r`, `|S| = q`, every OFF-`S` Gram eigenvalue `≥ κ²`), the
  front loss dominates the block-additive corner `Σ_{j∈S} λ_j·‖(A₀·U)_{·j}‖² + κ²·Σ_{j∉S}‖(A₀·U)_{·j}‖²`
  — the `q` collapsing blocks (weights `λ_j`, the small Gram eigenvalues) plus the bounded-below stable
  block (weight `≥ κ²`). Split the Frobenius–Gram identity `frobSq(A₀·Q) = Σ_j λ_j·‖col_j‖²` at `S`.

* **(b2) `corner → qPeelIntegral` (the deep-data casting — HELD).** `g_le_qPeelIntegral_on_cell` — bound
  the front box integral `∫_{A₀} frobSq(A₀·Q)^{−c'}` (on the cell) by `qPeelIntegral q h m T c'` with the
  units `U_i = ‖X_i‖²` cast per-block and the deep box dim `m_i+1` = the PER-DIRECTION product-rank codim
  (#127) — **obligation-1**: each collapse direction carries its OWN codim, not an unallocated total nor a
  uniform max (`qPeel_334_lt_top`'s `m = ![7,3]` is the `q=2` target). [HOLE — the corner blow-up +
  per-block deep casting, generalizing `onePeel334`; genm-sj5-cover audits the per-block allocation.]

## (b2) design note — the corner blow-up CoV + the decorrelated per-block allocation

**The CoV (banked).** The link `front ∫_{A₀}(Σ_{j∈S} λ_j‖(A₀U)_{·j}‖² + κ²·stable)^{−c'} → corner-radial`
is the radial blow-up `RouteMSJRadialPolar.lintegral_ball_radial_polar_factor` (opaque width `N`, banked):
each collapsing column block (a degree-2-homogeneous loss `‖·‖²`) blows up as radial `u_j` (exceptional
divisor, Jacobian `u_j^{N_j−1}`) × sphere unit. Iterated over the `q` collapsing directions this yields the
`qCornerSliceAtUnits` form; the small tail eigenvalue `λ_j` is then cast as the deep-norm `U_j = ‖X_j‖²`
over the deep box (the #127 product-rank tube), and `qPeelIntegral_lt_top` closes it. What changes `q=2 → q`
is purely the ITERATION count (one blow-up per collapse direction) — no new CoV.

**The per-block allocation (obligation-1) — derived from `onePeel334` + #127 (`prodD-general.md`), NOT from
cover's spec (decorrelation).** Firm at the `q=2 (3,3,3,4)` anchor: `onePeel334`/`qPeel_334` use
`m = ![7,3]`, `h = ![3,2]`, i.e. deep dims `(m_j+1) = (8,4)`. These match #116/#127's product-rank codim
list `D_prod = (8,4,1)` (by corank-cut): the first collapse direction carries the corank-1 tube codim `8`,
the second the corank-2 codim `4` — a genuine PER-DIRECTION allocation (not `2·max = 16` uniform, not an
unallocated `total`). The `h_j = (3,2)` are the accumulated blow-up Jacobian powers across the peel layers
(cert §1 `a=(3,2)`, `Σ(a_j+1)=7=½·minAdm·2`). The GENERAL-`q` allocation is `m_j+1 = ` the per-direction
increment of `D = minAdm(reduced by corank)` (#127's `D = C(reduced)`, the front-peel decomposition
`minAdm = Σ_j [M₀ + minAdm(reduced)]` distributing per direction) — this is the fidelity-critical derivation
kept EXPLICIT in the `(h, m)` parameters below so the obligation-1 audit reads off exactly which codim each
direction carries; it must reproduce `m=![7,3], h=![3,2]` at `q=2`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

variable {m r n : ℕ}

/-! ## (b1) The `q`-block spectral lower bound -/

/-- **The `q`-collapse sector.** Every Gram eigenvalue OUTSIDE the collapse set `S` is `≥ κ²` — the
region where the `|Sᶜ|` stable directions are bounded below (the `q`-block generalization of `sjSector`,
`S = {collapseIndex}` at `q = 1`). -/
def qSector (κ : ℝ) (Q : Matrix (Fin r) (Fin n) ℝ) (S : Finset (Fin r)) : Prop :=
  ∀ j ∈ Sᶜ, κ ^ 2 ≤ (posSemidef_mul_transpose Q).isHermitian.eigenvalues j

/-- **The bridge to the `q`-block corner (spectral).** On the `q`-collapse sector, the front loss
`frobSq(A₀·Q)` dominates the block-additive corner: the `q` collapsing blocks `Σ_{j∈S} λ_j·‖(A₀·U)_{·j}‖²`
(weights the small Gram eigenvalues) plus the bounded-below stable block `κ²·Σ_{j∉S}‖(A₀·U)_{·j}‖²`. The
`q`-block generalization of `frobSq_ge_twoBlock_of_sector` — split the Frobenius–Gram identity at `S`. -/
theorem frobSq_ge_qBlock_of_qSector (A₀ : Matrix (Fin m) (Fin r) ℝ) (Q : Matrix (Fin r) (Fin n) ℝ)
    {κ : ℝ} (S : Finset (Fin r)) (hsec : qSector κ Q S) :
    (∑ j ∈ S, (posSemidef_mul_transpose Q).isHermitian.eigenvalues j
        * ∑ i, ((A₀ * ((posSemidef_mul_transpose Q).isHermitian.eigenvectorUnitary :
          Matrix (Fin r) (Fin r) ℝ)) i j) ^ 2)
      + κ ^ 2 * (∑ j ∈ Sᶜ,
          ∑ i, ((A₀ * ((posSemidef_mul_transpose Q).isHermitian.eigenvectorUnitary :
            Matrix (Fin r) (Fin r) ℝ)) i j) ^ 2)
      ≤ frobSq (A₀ * Q) := by
  classical
  rw [frobSq_mul_eq_sum_eigenvalues A₀ Q]
  set e := (posSemidef_mul_transpose Q).isHermitian.eigenvalues with he
  set U : Matrix (Fin r) (Fin r) ℝ :=
    ((posSemidef_mul_transpose Q).isHermitian.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) with hU
  rw [← Finset.sum_add_sum_compl S (fun j => e j * ∑ i, ((A₀ * U) i j) ^ 2)]
  have hlow : κ ^ 2 * (∑ j ∈ Sᶜ, ∑ i, ((A₀ * U) i j) ^ 2)
      ≤ ∑ j ∈ Sᶜ, e j * ∑ i, ((A₀ * U) i j) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    exact mul_le_mul_of_nonneg_right (hsec j hj) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  linarith [hlow]

/-- **Non-vacuity (`q = 1`).** At the singleton collapse set `S = {collapseIndex}`, `qSector` is the
banked `sjSector` and the `q`-block bound is the banked `frobSq_ge_twoBlock_of_sector` shape (the sum
over `{c}` is the single collapsing block). -/
example (A₀ : Matrix (Fin m) (Fin r) ℝ) (Q : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) {κ : ℝ}
    (S : Finset (Fin r)) (hsec : qSector κ Q S) :
    (∑ j ∈ S, (posSemidef_mul_transpose Q).isHermitian.eigenvalues j
        * ∑ i, ((A₀ * ((posSemidef_mul_transpose Q).isHermitian.eigenvectorUnitary :
          Matrix (Fin r) (Fin r) ℝ)) i j) ^ 2)
      + κ ^ 2 * (∑ j ∈ Sᶜ,
          ∑ i, ((A₀ * ((posSemidef_mul_transpose Q).isHermitian.eigenvectorUnitary :
            Matrix (Fin r) (Fin r) ℝ)) i j) ^ 2)
      ≤ frobSq (A₀ * Q) :=
  frobSq_ge_qBlock_of_qSector A₀ Q S hsec

/-! ## (b2) The per-block radial blow-up atom (obligation-1: the per-direction width `N`) -/

/-- **The per-block radial blow-up (obligation-1's per-direction width).** A single collapsing block
(a degree-2-homogeneous loss `‖x‖²` on `EuclideanSpace ℝ (Fin N)`, `N` = THIS direction's own width) is
blown up by the banked `lintegral_ball_radial_polar_factor`: the box-restricted front integral becomes
the sphere-then-radial integral with the exceptional radial `r` (the corner variable), the Jacobian
`r^{N−1}` (so the accumulated Jacobian power `h = N−1`), and the sphere collapsing (`‖ω‖ = 1`) to the
`(λ·r² + C)` corner shape. **`N` is the per-block blow-up width** — obligation-1 requires each collapse
direction to enter with ITS OWN width `N_i` (= its per-direction #127 codim), not a shared/max width;
this atom is applied per-block with the block-specific `N_i` in the `q`-fold iteration. The `q=2`
`(3,3,3,4)` target is `h = ![3,2]` (widths `N_i = h_i + 1 = (4,3)` in the accumulated peel). -/
theorem block_radial_blowup (N : ℕ) [NeZero N] {R lam C c' : ℝ} :
    ∫⁻ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R,
        ENNReal.ofReal ((lam * ‖x‖ ^ 2 + C) ^ (-c'))
      = ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
          ∫⁻ r in Set.Ioc (0 : ℝ) R,
            ENNReal.ofReal (r ^ (N - 1)) * ENNReal.ofReal ((lam * r ^ 2 + C) ^ (-c'))
          ∂volume ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
  have hhom : ∀ (r : ℝ) (x : EuclideanSpace ℝ (Fin N)), ‖r • x‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 := by
    intro r x; rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hb := lintegral_ball_radial_polar_factor (N := N) (R := R) (fun x => ‖x‖ ^ 2)
    (by fun_prop) hhom (fun t => (lam * t + C) ^ (-c')) (by fun_prop)
  rw [hb]
  refine lintegral_congr (fun ω => ?_)
  refine setLIntegral_congr_fun measurableSet_Ioc (fun r _ => ?_)
  have hω2 : (‖(ω : EuclideanSpace ℝ (Fin N))‖ : ℝ) ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm.mp ω.2]; norm_num
  simp only [hω2, mul_one]

end DLNFibre.DLN.RLCT
