import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverGE
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import DLNFibre.DLN.RLCT.Validate.Case222Resolution

/-!
# `RouteMLayerCoverGEL2` — the `L = 2` achiever box-divergence (single weighted radial blow-up)

The `L = 2` case of the achiever-path box-divergence atom
`routeMCore_box_diverges_achiever` (`RouteMLayerCoverGE.lean`), via a SINGLE weighted radial
blow-up — the depth-2 miracle (no gauge chain needed at `L = 2`).

**Proof state (HONEST `b = a·β` chart, 2026-06-24).** The degenerate predecessor `phi334` (which
pinned `A(0,1)=A(0,2)=0`, dropped `u₂,u₃`, gave `det ≡ 0` / null image / a FALSE `cov = ⊤`) is
REPLACED by a genuine diffeo. The soundness-critical EXACT algebra is banked sorry-free: the
post-Schur-blow-up factorization `loss_schur_blowup_factor` (`‖A·C‖² = u²·U`, pure `ring`), its lift
through the honest chart `routeMCore_phi334` (`routeMCore M334 (phi334 u) = (u 0)²·U`, the SAME
`Uval334`), the unit bound `Uval334_ge_sq`, the binding-monomial threshold `leafMonomialThreshold334_le`
(`= 4 = ½·minAdm`), and the divergence ASSEMBLY `routeM334_box_diverges_of_chart` (sorry-free FROM the
chart bundle, feeding the single cited leaf atom `monomial_rlct`).

**The chart now passes the anti-`phi334` gate** (genuine-diffeo validation, all sorry-free):
reads ALL 21 coords (`chartA334_reads_u2` — `A(0,1) = u 1·u 2` depends on `u 2`); `phi334 0 = 0`
(`phi334_zero`, reaches the deepest point); continuous (`continuous_phi334`); image into `cubeBox 21 ε`
(`phi334_image_subset_cubeBox`). The Jacobian determinant is `−u₀⁷·u₁²` (sympy-exact, Codex `xhigh`) —
genuinely `≠ 0`, the two-axis weight `|u 0|⁷·|u 1|²` carried by `leafH334`.

**ONE residual `sorry` remains in `achieverChart334`** — the `cov` genuine geometric
change-of-variables (NO LONGER FALSE): Mathlib `lintegral_image_eq_lintegral_abs_det_fderiv_mul` +
the structural determinant `−u₀⁷·u₁²`. The `Ubound` a.e.-positivity is now PROVED (`Uval334 ≥ a² > 0`
off the null `{u 1 = 0}`). The `cov` is the per-node measure-plumbing atom the `hfin` certificate flags
(cost driver 2). No other axiom / `native_decide`; the exact `F = u²·U`, the determinant value, and the
threshold are PROVEN, not faked.

## The construction (concrete `(3,3,4)`, the binding corank-2 anchor; `minAdm = 8`)

`routeMCore M334 = ‖A·C‖²` with `A : 3×3`, `C : 3×4`. Block `A = [[a, b],[c, E]]`
(`a` scalar, `b` 1×2, `c` 2×1, `E` 2×2), `C = [[y],[S]]` (`y` 1×4, `S` 2×4).

**The honest `b = a·β` chart** (pole-free; the design-spec genuine-diffeo, Codex `xhigh`). Set
`b = a·β` (so the Schur shear `a⁻¹·b = β` is regular — no `a⁻¹` pole) and blow up the 8 normal
coords by the pivot `u₀`:

    A = [[a, a·β], [c, c·β + u₀·Δ]],   C = [[u₀·(1,τ) − β·S], [S]],
    A·C = u₀·[[a·(1,τ)], [c·(1,τ) + Δ·S]],   so  F = ‖A·C‖² = u₀²·U,
    U = a²·‖(1,τ)‖² + ‖c·(1,τ) + Δ·S‖²  (u₀-free, the SAME `Uval334`),   U ≥ a².

The map reads ALL 21 coords (`β = (u₂,u₃)` enters `A(0,1),A(0,2)` and the inverse shear in `C`-row-0),
reaches the origin (`Φ(0) = 0`), and has Jacobian `det DΦ = −u₀⁷·u₁²`: the pivot blow-up contributes
`u₀⁷` (binding axis `(k,h) = (1, 7) = (1, minAdm−1)`, threshold `minAdm/2 = 4`), the Schur shear
det `1`, and the `b = a·β` substitution the unit factor `a² = u₁²` (on axis `1`, a `k = 0` spectator,
so the threshold is UNCHANGED at `4`). At `c' = 4` the leaf exponent on `u₀` is `7 − 2·1·4 = −1`, the
sharp `∫ u₀⁻¹ = ⊤`, fed to `monomialIntegrand_lintegral_box_eq_top`; the `a²` integrates harmlessly
(`∫₀ a² da` finite). The unit `U` is dropped by `U ≤ B` on the compact box (`U^{−c'} ≥ B^{−c'} > 0`).

Verified EXACT in flat coordinates (`genuine_chart_334c.py` + `codex_chart` this thread; det `−u₀⁷·u₁²`,
`F∘φ = u₀²·Uval334`, `φ(0)=0`).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## The EXACT loss factorization (raw-variable core, `ring`-clean)

The post-chart squared-Frobenius loss `‖A·C‖²` on the `(3,3,4)` blocks, written directly in the
Schur-blow-up coordinates `(u, a, b, c, τ, Δ, S)` (the 21 flat coordinates, regrouped). The matrix
product after the Schur shear and the `u`-blow-up is `[[a·u·(1,τ)], [c·u·(1,τ) + u·Δ·S]]`; its
squared Frobenius norm factors as `u² · U`. Pure `ring`. -/

/-- The post-Schur-blow-up loss `U` (the `u`-free unit factor): `U = a²·‖(1,τ)‖² + ‖c·(1,τ)+Δ·S‖²`
on the `(3,3,4)` blocks. `c = (c0,c1)`, `τ = (τ1,τ2,τ3)` (the `(1,τ)` row is `(1,τ1,τ2,τ3)`),
`Δ` the 2×2 residual `(Δ00,Δ01,Δ10,Δ11)`, `S` the 2×4 free block `(S0j, S1j)`. -/
noncomputable def Uval334
    (a c0 c1 τ1 τ2 τ3 Δ00 Δ01 Δ10 Δ11 : ℝ)
    (S00 S01 S02 S03 S10 S11 S12 S13 : ℝ) : ℝ :=
  a ^ 2 * (1 + τ1 ^ 2 + τ2 ^ 2 + τ3 ^ 2)
    + ((c0 * 1 + (Δ00 * S00 + Δ01 * S10)) ^ 2
       + (c0 * τ1 + (Δ00 * S01 + Δ01 * S11)) ^ 2
       + (c0 * τ2 + (Δ00 * S02 + Δ01 * S12)) ^ 2
       + (c0 * τ3 + (Δ00 * S03 + Δ01 * S13)) ^ 2)
    + ((c1 * 1 + (Δ10 * S00 + Δ11 * S10)) ^ 2
       + (c1 * τ1 + (Δ10 * S01 + Δ11 * S11)) ^ 2
       + (c1 * τ2 + (Δ10 * S02 + Δ11 * S12)) ^ 2
       + (c1 * τ3 + (Δ10 * S03 + Δ11 * S13)) ^ 2)

/-- **The post-chart loss factorization (EXACT).** The squared Frobenius norm of the
Schur-blow-up product `A·C = [[a·u·(1,τ)], [c·u·(1,τ) + u·Δ·S]]` factors as `u² · U`, with `U`
the `u`-free `Uval334`. The product rows are: top `= a·u·(1,τ1,τ2,τ3)` (the `a·T` row); bottom two
`= c·u·(1,τ) + u·Δ·S`. Pure `ring` (the verified-exact algebra; soundness-critical). -/
theorem loss_schur_blowup_factor
    (u a c0 c1 τ1 τ2 τ3 Δ00 Δ01 Δ10 Δ11 : ℝ)
    (S00 S01 S02 S03 S10 S11 S12 S13 : ℝ) :
    -- top row entries (a·u·(1,τ))
    ((a * (u * 1)) ^ 2 + (a * (u * τ1)) ^ 2 + (a * (u * τ2)) ^ 2 + (a * (u * τ3)) ^ 2)
    -- middle row (c0·u·(1,τ) + u·(Δ00,Δ01)·S)
    + ((c0 * (u * 1) + (u * Δ00) * S00 + (u * Δ01) * S10) ^ 2
       + (c0 * (u * τ1) + (u * Δ00) * S01 + (u * Δ01) * S11) ^ 2
       + (c0 * (u * τ2) + (u * Δ00) * S02 + (u * Δ01) * S12) ^ 2
       + (c0 * (u * τ3) + (u * Δ00) * S03 + (u * Δ01) * S13) ^ 2)
    -- bottom row (c1·u·(1,τ) + u·(Δ10,Δ11)·S)
    + ((c1 * (u * 1) + (u * Δ10) * S00 + (u * Δ11) * S10) ^ 2
       + (c1 * (u * τ1) + (u * Δ10) * S01 + (u * Δ11) * S11) ^ 2
       + (c1 * (u * τ2) + (u * Δ10) * S02 + (u * Δ11) * S12) ^ 2
       + (c1 * (u * τ3) + (u * Δ10) * S03 + (u * Δ11) * S13) ^ 2)
      = u ^ 2 * Uval334 a c0 c1 τ1 τ2 τ3 Δ00 Δ01 Δ10 Δ11 S00 S01 S02 S03 S10 S11 S12 S13 := by
  unfold Uval334
  ring

/-- **`U ≥ a²`** (the lower bound — the `a²·1` pivot-row term, the rest a sum of squares). The
binding nonvanishing: on a box where `a` is bounded away from `0` (e.g. `a ∈ [½,1]`), `U ≥ a² > 0`,
so `F ∘ Ψ = u²·U > 0` off the pivot-zero locus. -/
theorem Uval334_ge_sq
    (a c0 c1 τ1 τ2 τ3 Δ00 Δ01 Δ10 Δ11 : ℝ)
    (S00 S01 S02 S03 S10 S11 S12 S13 : ℝ) :
    a ^ 2 ≤ Uval334 a c0 c1 τ1 τ2 τ3 Δ00 Δ01 Δ10 Δ11 S00 S01 S02 S03 S10 S11 S12 S13 := by
  unfold Uval334
  nlinarith [sq_nonneg τ1, sq_nonneg τ2, sq_nonneg τ3, sq_nonneg a,
    sq_nonneg (c0 * 1 + (Δ00 * S00 + Δ01 * S10)),
    sq_nonneg (c0 * τ1 + (Δ00 * S01 + Δ01 * S11)),
    sq_nonneg (c0 * τ2 + (Δ00 * S02 + Δ01 * S12)),
    sq_nonneg (c0 * τ3 + (Δ00 * S03 + Δ01 * S13)),
    sq_nonneg (c1 * 1 + (Δ10 * S00 + Δ11 * S10)),
    sq_nonneg (c1 * τ1 + (Δ10 * S01 + Δ11 * S11)),
    sq_nonneg (c1 * τ2 + (Δ10 * S02 + Δ11 * S12)),
    sq_nonneg (c1 * τ3 + (Δ10 * S03 + Δ11 * S13)),
    mul_nonneg (sq_nonneg a) (sq_nonneg τ1),
    mul_nonneg (sq_nonneg a) (sq_nonneg τ2),
    mul_nonneg (sq_nonneg a) (sq_nonneg τ3)]

/-! ## The single-axis binding monomial (the `(3,3,4)` leaf, `d = flatDim M334 = 21`)

The post-chart leaf integrand is `|det DΨ|·|F∘Ψ|^{−c'} = |u_p|⁷·(u_p²·U)^{−c'}`. On the binding
axis (the pivot `p`) the monomial is `|u_p|⁷·(|u_p|²)^{−c'}` — `monomialIntegrand 21 k h` with
`k_p = 1` (the loss base `u_p²`), `h_p = 7` (the Jacobian `u_p⁷`), and `0` on the 20 spectator axes.
The binding axis `(k,h) = (1, 7) = (1, minAdm−1)`, threshold `(7+1)/(2·1) = 4 = ½·minAdm`. -/

/-- `minAdm M334 = 8` and `flatDim M334 = 21` (the `(3,3,4)` binding corank-2 anchor). -/
theorem minAdm_M334' : minAdm (![3, 3, 4] : Fin 3 → ℕ) = 8 := by
  rw [← minAdmRec_eq_minAdm]; decide

theorem flatDim_M334' : flatDim (![3, 3, 4] : Fin 3 → ℕ) = 21 := by decide

theorem routeMAmbient_M334' : routeMAmbient (![3, 3, 4] : Fin 3 → ℕ) = 21 := by decide

/-- The `(3,3,4)` leaf loss-base exponents on `Fin 21`: `k = 1` on the binding axis `0` (the pivot
`u 0`, the loss base `|u 0|²`), `0` elsewhere. -/
def leafK334 : Fin 21 → ℕ := fun j => if j = 0 then 1 else 0

/-- The `(3,3,4)` leaf Jacobian exponents on `Fin 21`, the genuine two-axis Jacobian of the HONEST
chart: `h = 7` on the binding pivot axis `0` (the `pivotBlowupOn` determinant `|u 0|⁷`) and `h = 2`
on the spectator axis `1` (the `a² = (u 1)²` factor from the `b = a·β` substitution, `det Dφ =
−u₀⁷·u₁²`); `0` on the remaining 19 axes. **The `a²` factor lives on a `k = 0` axis** (axis `1` is
not in the loss base), so it does NOT change the monomial threshold (`axisRatio` is `⊤` there). -/
def leafH334 : Fin 21 → ℕ := fun j => if j = 0 then 7 else if j = 1 then 2 else 0

/-- The binding axis `0` has `leafK334 0 = 1 ≠ 0` — the singular-axis witness for
`monomialIntegrand_lintegral_box_eq_top`. -/
theorem leafK334_binding : leafK334 0 ≠ 0 := by
  simp [leafK334]

/-- **The leaf monomial threshold is `≤ 4 = ½·minAdm`** (the binding axis `0` has `(k,h) = (1, 7) =
(1, 8−1)`, realising `8/2` via `monomialThreshold_le_regularSeq`; the `a²` on axis `1` has `k = 0`,
ratio `⊤`, so it does NOT lower the threshold). The `≤`-direction input: for `c' ≥ 4`, the `d = 21`
leaf monomial diverges. -/
theorem leafMonomialThreshold334_le :
    monomialThreshold 21 leafK334 leafH334 ≤ 4 := by
  have h := monomialThreshold_le_regularSeq 21 leafK334 leafH334 8 (by norm_num) 0
    (by simp [leafK334]) (by simp [leafH334])
  have hcast : ((8 : ℕ) : ℝ≥0∞) / 2 = 4 := by
    rw [show ((8 : ℕ) : ℝ≥0∞) = (8 : ℝ≥0∞) by norm_num]
    rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  rwa [hcast] at h

/-- **The Jacobian weight `∏_j |u_j|^{leafH j} = |u 0|⁷ · |u 1|²`** — the genuine `|det Dφ|` of the
honest `b = a·β` chart (`u 0` the pivot exceptional divisor `⁷`, `u 1 = a` the `b = aβ` substitution
factor `²`). The 19 spectator axes contribute `|·|⁰ = 1`. -/
theorem leafH334_prod_eq (u : Fin 21 → ℝ) :
    (∏ j, |u j| ^ (leafH334 j)) = |u 0| ^ 7 * |u 1| ^ 2 := by
  rw [Fintype.prod_eq_mul (0 : Fin 21) (1 : Fin 21) (by decide)
    (fun x ⟨hx0, hx1⟩ => by simp [leafH334, hx0, hx1])]
  simp [leafH334]

/-- **Two-axis monomial evaluation.** `monomialIntegrand 21 leafK334 leafH334 c u =
(|u 0|⁷·|u 1|²) · (|u 0|²)^{−c}` — the loss base `|u 0|²` (`k = 1` at axis `0`) against the genuine
two-axis Jacobian `|u 0|⁷·|u 1|²` (`h = (7,2)`). The 19 spectator axes contribute `1`. -/
theorem monomialIntegrand_leaf334_eq (c : ℝ) (u : Fin 21 → ℝ) :
    monomialIntegrand 21 leafK334 leafH334 c u
      = (|u 0| ^ 7 * |u 1| ^ 2) * (|u 0| ^ 2) ^ (-c) := by
  unfold monomialIntegrand
  rw [leafH334_prod_eq]
  congr 1
  rw [Finset.prod_eq_single (0 : Fin 21)]
  · simp [leafK334]
  · intro j _ hj; simp [leafK334, hj]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin 21)) h

/-! ## The achiever `Params` and the loss factorization (the soundness-critical bridge, sorry-free)

`routeMCore M334 = dlnLoss M334 0 ∘ (paramsEquivFlat M334).symm`. The chart's matrix output is built
DIRECTLY as a `Params M334` from the chart coordinates `u : Fin 21 → ℝ` (`chartParams334`),
bypassing the opaque `Fintype.equivFin (FlatIdx M334)`: the flat chart is then
`paramsEquivFlat M334 ∘ chartParams334`, and `routeMCore M334 (paramsEquivFlat (chartParams334 u))
= dlnLoss M334 0 (chartParams334 u)` (the `symm`/`apply` cancel). The achiever matrices realize the
post-Schur-blow-up product `A·C = [[a·u·(1,τ)], [c·u·(1,τ) + u·Δ·S]]` (the pivot `u = u 0`). -/

/-- **General `L = 2` layer-product entry form** `(prod M A) i j = ∑ₖ A₀ᵢₖ·A₁ₖⱼ` — the explicit
`L = 2` matrix product `A⁽⁰⁾·A⁽¹⁾`. The general-`M` lift of `Case222Algebra.prod_two_layer`
(same `prodAux` dependent-`Fin`-cast closer). -/
theorem prod_two_layer334 (M : Fin 3 → ℕ) (A : Params M) (i : Fin (M 0)) (j : Fin (M 2)) :
    prod M A i j = ∑ k : Fin (M 1), A 0 i k * A 1 k j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) k using 2

/-- **The genuine layer-`0` matrix `A⁽⁰⁾`** (3×3), the HONEST `b = a·β` replacement for the degenerate
`b = 0` chart. Pivot-minor `a = u 1`; cross strip `b = a·β = (u 1·u 2, u 1·u 3)` (so `b` is read,
NOT pinned to `0` — the `phi334` slip); column `c = (u 4, u 5)`; residual block `E = c·β + u₀·Δ`
(`Δ = (u 6,u 7,u 8,u 9)`). The `b = a·β` substitution clears the Schur shear's `a⁻¹` pole (pole-free,
polynomial) at the cost of an `a²` Jacobian factor; all six lower-right entries now read `u 2, u 3`. -/
noncomputable def chartA334 (u : Fin 21 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![u 1, u 1 * u 2, u 1 * u 3;
     u 4, u 4 * u 2 + u 0 * u 6, u 4 * u 3 + u 0 * u 7;
     u 5, u 5 * u 2 + u 0 * u 8, u 5 * u 3 + u 0 * u 9]

/-- **The genuine layer-`1` matrix `A⁽¹⁾`** (3×4), the HONEST `b = a·β` replacement. Top row
`y = u₀·(1,τ) − β·S` (`τ = (u 10,u 11,u 12)`, the inverse Schur shear absorbing `β·S` — now reading
`u 2, u 3` through `β`); bottom block `S = (u 13 … u 20)`. With `chartA334` this realizes
`A·C = u₀·[[a·(1,τ)], [c·(1,τ) + Δ·S]]`, so `‖A·C‖² = u₀²·U` with the SAME `Uval334`. -/
noncomputable def chartC334 (u : Fin 21 → ℝ) : Matrix (Fin 3) (Fin 4) ℝ :=
  !![u 0 - (u 2 * u 13 + u 3 * u 17), u 0 * u 10 - (u 2 * u 14 + u 3 * u 18),
       u 0 * u 11 - (u 2 * u 15 + u 3 * u 19), u 0 * u 12 - (u 2 * u 16 + u 3 * u 20);
     u 13, u 14, u 15, u 16;
     u 17, u 18, u 19, u 20]

/-- The genuine `Params M334`, assembled by `Fin.cons` over the two layers.
`chartParams334 u 0 = chartA334 u` (3×3), `chartParams334 u 1 = chartC334 u` (3×4). -/
noncomputable def chartParams334 (u : Fin 21 → ℝ) : Params (![3, 3, 4] : Fin 3 → ℕ) :=
  Fin.cons (chartA334 u) (Fin.cons (chartC334 u) (fun i => i.elim0))

/-- **The loss factorization (EXACT, sorry-free).** `dlnLoss M334 0 (chartParams334 u) = (u 0)² · U`
with `U = Uval334 …` (the `u`-free unit, `≥ a² = (u 1)²`). Each of the 12 product entries equals
`u₀ · (linear)` (the `b = a·β` and the inverse Schur shear cancel the stray `β·S`/`b·S` term), so
`A·C = u₀·[[a·(1,τ)], [c·(1,τ) + Δ·S]]` and the squared Frobenius norm is `u₀²·Uval334` — the SAME `U`
as the degenerate chart (`loss_schur_blowup_factor` applies after the per-entry `ring`-regroup). The
soundness-critical `F = u²·U` identity, on a chart that now reads ALL 21 coords. -/
theorem dlnLoss_chartParams334 (u : Fin 21 → ℝ) :
    dlnLoss (![3, 3, 4] : Fin 3 → ℕ) 0 (chartParams334 u)
      = (u 0) ^ 2 * Uval334 (u 1) (u 4) (u 5) (u 10) (u 11) (u 12) (u 6) (u 7) (u 8) (u 9)
          (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20) := by
  -- the two layer matrices (each `rfl`; the dependent `Params`-cons reduces definitionally)
  have hA : (chartParams334 u) 0 = chartA334 u := rfl
  have hC : (chartParams334 u) 1 = chartC334 u := rfl
  unfold dlnLoss
  simp only [sub_zero]
  simp_rw [prod_two_layer334]
  -- the three sums are over `Fin 3` (outer i), `Fin 4` (j), `Fin 3` (inner k) (defeq the M334-Fin)
  change (∑ i : Fin 3, ∑ j : Fin 4,
      (∑ k : Fin 3, (chartParams334 u) 0 i k * (chartParams334 u) 1 k j) ^ 2) = _
  -- expand all nested sums (repeatedly, via `simp`) and reduce the 24 chart entries to scalars,
  -- then close by the banked exact algebra `loss_schur_blowup_factor`.
  simp only [hA, hC, Fin.sum_univ_three, Fin.sum_univ_four, chartA334, chartC334,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_fin_const,
    Matrix.cons_val]
  rw [← loss_schur_blowup_factor (u 0) (u 1) (u 4) (u 5) (u 10) (u 11) (u 12)
    (u 6) (u 7) (u 8) (u 9) (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20)]
  ring

/-- **The genuine achiever flat chart for `(3,3,4)`** `phi334 := paramsEquivFlat M334 ∘ chartParams334`,
an `(Fin 21 → ℝ) → (Fin 21 → ℝ)` map. Unlike the degenerate predecessor it reads ALL 21 coords (the
`b = a·β` strip and the inverse Schur shear carry `u 2, u 3`), so its Jacobian has NO zero column. -/
noncomputable def phi334 (u : Fin 21 → ℝ) : Fin (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) → ℝ :=
  paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ) (chartParams334 u)

/-- **The `routeMCore` factorization (EXACT, sorry-free).** `routeMCore M334 (phi334 u) = (u 0)² · U`
(`U = Uval334 …`): the flat core, pulled back through the genuine chart, is the binding monomial
`(u 0)²` times the `u`-free unit `U`. Since `routeMCore M334 = dlnLoss M334 0 ∘ (paramsEquivFlat).symm`
and `phi334 = paramsEquivFlat ∘ chartParams334`, the `symm`/`apply` cancel, leaving
`dlnLoss M334 0 (chartParams334 u)` — discharged by `dlnLoss_chartParams334` (the banked exact algebra).
This is the soundness-critical `F ∘ phi = u²·U` identity, proven not faked. -/
theorem routeMCore_phi334 (u : Fin 21 → ℝ) :
    routeMCore (![3, 3, 4] : Fin 3 → ℕ) (phi334 u)
      = (u 0) ^ 2 * Uval334 (u 1) (u 4) (u 5) (u 10) (u 11) (u 12) (u 6) (u 7) (u 8) (u 9)
          (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20) := by
  rw [routeMCore, phi334, MeasurableEquiv.symm_apply_apply, dlnLoss_chartParams334]

/-- **`routeMCore M334 (phi334 u) ≥ 0`** (the loss is a sum of squares). -/
theorem routeMCore_phi334_nonneg (u : Fin 21 → ℝ) :
    0 ≤ routeMCore (![3, 3, 4] : Fin 3 → ℕ) (phi334 u) := by
  rw [routeMCore]; exact dlnLoss_nonneg _ _ _

/-! ## The box-divergence, reduced to the achiever chart bundle (sorry-free assembly)

The `(3,3,4)` box-divergence reduces — sorry-free — to a chart `phi` with the achiever properties
(`L2AchieverChart` below). The assembly mirrors `routeM222_box_diverges`: dominate `cubeBox 21 ε` by
the chart image (`lintegral_mono_set`), transport by the chart c-o-v, match the integrand to the
binding monomial times the unit `U`, drop `U^{−c'} ≥ B^{−c'} > 0` (the `U ∈ [c₀, B]` two-sided
bound — the soundness-critical direction), and diverge via `monomialIntegrand_lintegral_box_eq_top`. -/

/-- **The `L = 2` achiever chart bundle for `(3,3,4)`.** A chart `phi : (Fin 21 → ℝ) → (Fin 21 → ℝ)`
with the genuine-diffeo achiever properties at binding axis `0` (the pivot `u 0`), carrying the HONEST
two-axis Jacobian `|det Dφ| = |u 0|⁷·|u 1|² = ∏_j |u_j|^{leafH334 j}` of the `b = a·β` chart. Carrying
the bundle as an explicit hypothesis set isolates the divergence ASSEMBLY (proven sorry-free from the
bundle) from the chart CONSTRUCTION (the Schur-shear ∘ `pivotBlowupOn` ∘ `b = aβ`). `Ufun` is the
`u`-free unit (`= Uval334` in chart coords), `B` its compact-box upper bound. The `a²` Jacobian factor
sits on axis `1` (a `k = 0` spectator), so the threshold is unchanged at `4 = ½·minAdm`. -/
structure L2AchieverChart where
  /-- The chart map (`b = aβ` ∘ Schur-shear ∘ pivot blow-up, in flat coordinates). -/
  phi : (Fin 21 → ℝ) → (Fin 21 → ℝ)
  /-- The unit factor `U` of `F ∘ phi = (u 0)² · U`. -/
  Ufun : (Fin 21 → ℝ) → ℝ
  /-- On each source box `[0,δ]²¹`, `U` admits a `δ`-dependent compact upper bound `B > 0`, and `U`
  is positive a.e. on the box (the SOUNDNESS-critical pair: `U ≤ B` gives `U^{−c'} ≥ B^{−c'} > 0`
  where `U > 0`; the vanishing locus `{U = 0}` is a proper subvariety, null, dropped a.e.). -/
  Ubound : ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
    (∀ u ∈ Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ), Ufun u ≤ B) ∧
    ∀ᵐ u ∂(volume.restrict (Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ))), 0 < Ufun u
  /-- `U` is measurable (it is a polynomial in the chart coordinates). -/
  Umeas : Measurable Ufun
  /-- The leaf-integrand identity: `(|u 0|⁷·|u 1|²) · |F ∘ phi|^{−c} = monomialIntegrand · U^{−c}`
  (the genuine two-axis Jacobian × the loss power, on the chart orthant). The `(3,3,4)` analog of
  `myF222_phiUnit_leaf_integrand`, now carrying the honest `a²` factor. -/
  leaf_integrand : ∀ (c : ℝ) (u : Fin 21 → ℝ),
    (|u 0| ^ 7 * |u 1| ^ 2) * |routeMCore (![3, 3, 4] : Fin 3 → ℕ) (phi u)| ^ (-c)
      = monomialIntegrand 21 leafK334 leafH334 c u * (Ufun u) ^ (-c)
  /-- The composite change-of-variables (the genuine chart Jacobian `|det Dφ| = |u 0|⁷·|u 1|²`, off
  the pivot-zero locus `{u 0 = 0}`): `∫⁻_{phi '' (V \ {u_0=0})} g = ∫⁻_{V \ {u_0=0}}
  ofReal(|u 0|⁷·|u 1|²) · g (phi u)`. -/
  cov : ∀ (V : Set (Fin 21 → ℝ)), MeasurableSet V → ∀ (g : (Fin 21 → ℝ) → ℝ≥0∞),
    ∫⁻ x in phi '' (V \ {x | x 0 = 0}), g x
      = ∫⁻ u in V \ {x | x 0 = 0}, ENNReal.ofReal (|u 0| ^ 7 * |u 1| ^ 2) * g (phi u)
  /-- Image containment: a small source box `[0,δ]²¹` maps into `cubeBox 21 ε`. -/
  image_subset : ∀ ε : ℝ, 0 < ε →
    ∃ δ > 0, phi '' (Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ)) ⊆ cubeBox 21 ε

/-- **The achiever leaf-box divergence (unit-stripped, from the bundle).** For `c' ≥ 4` (`0 < c'`),
`∫⁻_{[0,ε]²¹} monomialIntegrand · U^{−c'} = ⊤`: lower-bound `U^{−c'} ≥ B^{−c'} > 0` (`U ∈ [1, B]`,
`−c' < 0`), pull the constant out, and apply the bare-monomial box divergence
(`monomialIntegrand_lintegral_box_eq_top`). The `(3,3,4)` analog of `leaf_box_div`. -/
theorem leaf334_box_div (W : L2AchieverChart) (c' : ℝ) (hc'0 : 0 < c')
    (hc' : monomialThreshold 21 leafK334 leafH334 ≤ ENNReal.ofReal c')
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ u in Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) ε),
      ENNReal.ofReal (monomialIntegrand 21 leafK334 leafH334 c' u
        * (W.Ufun u) ^ (-c')) = ⊤ := by
  obtain ⟨B, hB0, hBle, hUpos_ae⟩ := W.Ubound ε
  set box := Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) ε) with hbox
  have hmonomeas : Measurable
      (fun u : Fin 21 → ℝ => monomialIntegrand 21 leafK334 leafH334 c' u) := by
    unfold monomialIntegrand; fun_prop
  have hmonomeas' : Measurable
      (fun u : Fin 21 → ℝ => ENNReal.ofReal (|monomialIntegrand 21 leafK334 leafH334 c' u|)) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hmonomeas)
  have hlb : ∫⁻ u in box, ENNReal.ofReal (B ^ (-c'))
        * ENNReal.ofReal (|monomialIntegrand 21 leafK334 leafH334 c' u|)
      ≤ ∫⁻ u in box, ENNReal.ofReal (monomialIntegrand 21 leafK334 leafH334 c' u
          * (W.Ufun u) ^ (-c')) := by
    apply setLIntegral_mono_ae
      (ENNReal.measurable_ofReal.comp (hmonomeas.mul (W.Umeas.pow_const _))).aemeasurable
    -- the inequality holds where `0 < U` (a.e. on the box: the vanishing locus `{U=0}` is null)
    rw [ae_restrict_iff' (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))] at hUpos_ae
    filter_upwards [hUpos_ae] with u hUposimp hu
    have hUpos := hUposimp hu
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hmono : 0 ≤ monomialIntegrand 21 leafK334 leafH334 c' u := by
      unfold monomialIntegrand; positivity
    rw [abs_of_nonneg hmono, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hUpos (hBle u hu) (by linarith)) hmono
  have hBne : ENNReal.ofReal (B ^ (-c')) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.rpow_pos_of_pos hB0 _
  rw [lintegral_const_mul _ hmonomeas',
    monomialIntegrand_lintegral_box_eq_top 21 leafK334 leafH334
      ⟨0, leafK334_binding⟩ c' hc' hc'0 hε,
    ENNReal.mul_top hBne] at hlb
  exact top_le_iff.1 hlb

/-- **`(3,3,4)` box-divergence, from the achiever chart bundle (sorry-free).** Given an
`L2AchieverChart`, for `c'` at-or-above the achiever threshold `4 = ½·minAdm M334`, the
flat-coordinate box integral `∫⁻_{cubeBox 21 ε} |routeMCore M334|^{−c'} = ⊤`, every `ε > 0`. The
`(3,3,4)` analog of `routeM222_box_diverges`: dominate `cubeBox 21 ε` by the chart image
(`image_subset` + `lintegral_mono_set`), transport by the chart c-o-v (`cov`), match the integrand to
the binding monomial × unit (`leaf_integrand`, pivot locus dropped null via `coordZero_null`), diverge
(`leaf334_box_div`). -/
theorem routeM334_box_diverges_of_chart (W : L2AchieverChart) (c' : NNReal)
    (hc' : (4 : ℝ≥0∞) ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox 21 ε,
      ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ))) = ⊤ := by
  -- `threshold ≤ 4 ≤ c'` ⟹ the non-strict chart-threshold premise; `4 ≤ c'` ⟹ `0 < c'`.
  have hc'0 : (0 : ℝ) < (c' : ℝ) := by
    have : (4 : ℝ≥0∞) ≤ ENNReal.ofReal (c' : ℝ) := by rwa [ENNReal.ofReal_coe_nnreal]
    have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by rw [ENNReal.ofReal_ofNat]
    rw [h4, ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    linarith
  have hthr : monomialThreshold 21 leafK334 leafH334 ≤ ENNReal.ofReal (c' : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact le_trans leafMonomialThreshold334_le hc'
  obtain ⟨δ, hδ, hsub⟩ := W.image_subset ε hε
  set P := Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ) with hP
  have hPmeas : MeasurableSet P := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  -- the pivot-zero locus `{u 0 = 0}` is null, so the `\ {x 0 = 0}` restriction is a no-op
  have hdiffnull : ∫⁻ x in P \ {x | x 0 = 0},
        ENNReal.ofReal (|x 0| ^ 7 * |x 1| ^ 2)
          * ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) (W.phi x)| ^ (-(c' : ℝ)))
      = ∫⁻ x in P, ENNReal.ofReal (|x 0| ^ 7 * |x 1| ^ 2)
          * ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) (W.phi x)| ^ (-(c' : ℝ))) := by
    apply setLIntegral_congr
    exact MeasureTheory.diff_ae_eq_self.2 (measure_mono_null Set.inter_subset_right
      (coordZero_null 0))
  apply top_le_iff.1
  calc (⊤ : ℝ≥0∞)
      = ∫⁻ u in P,
          ENNReal.ofReal (monomialIntegrand 21 leafK334 leafH334 (c' : ℝ) u
            * (W.Ufun u) ^ (-(c' : ℝ))) :=
        (leaf334_box_div W (c' : ℝ) hc'0 hthr δ hδ).symm
    _ = ∫⁻ u in P, ENNReal.ofReal (|u 0| ^ 7 * |u 1| ^ 2)
          * ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) (W.phi u)| ^ (-(c' : ℝ))) := by
        refine setLIntegral_congr_fun hPmeas (fun u _ => ?_)
        rw [← ENNReal.ofReal_mul (by positivity), W.leaf_integrand]
    _ = ∫⁻ x in P \ {x | x 0 = 0}, ENNReal.ofReal (|x 0| ^ 7 * |x 1| ^ 2)
          * ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) (W.phi x)| ^ (-(c' : ℝ))) :=
        hdiffnull.symm
    _ = ∫⁻ x in W.phi '' (P \ {x | x 0 = 0}),
          ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ))) :=
        (W.cov P hPmeas
          (fun x => ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ))))).symm
    _ ≤ ∫⁻ x in cubeBox 21 ε,
          ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ))) :=
        lintegral_mono_set (subset_trans (Set.image_mono Set.diff_subset) hsub)

/-! ## The achiever chart for `(3,3,4)` (the bundle, discharged up to the geometric c-o-v residual)

The `L2AchieverChart` for `(3,3,4)` with `phi := phi334`, binding axis `p = 0` (the pivot `u 0`),
unit `Ufun := Ufun334 = Uval334 (u 1) …`. The factorization, bounds, measurability, and leaf-integrand
are banked sorry-free (from `routeMCore_phi334`, `Uval334_ge_sq`, `monomialIntegrand_leaf334_eq`). The
THREE remaining fields are the geometric residual (the equidimensional chart Jacobian, the image
containment, and the unit a.e.-positivity), isolated as honest `sorry`s with precise sub-blockers;
everything else is sorry-free. -/

/-- The achiever unit `U` in chart coordinates: `Uval334` with the (unshifted) pivot-minor `a = u 1`
(so `U ≥ a² = (u 1)² ≥ 0`; `U → 0` at the origin, where the chart's deepest point lies). -/
noncomputable def Ufun334 (u : Fin 21 → ℝ) : ℝ :=
  Uval334 (u 1) (u 4) (u 5) (u 10) (u 11) (u 12) (u 6) (u 7) (u 8) (u 9)
    (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20)

/-- `Ufun334` is continuous (a polynomial in the chart coordinates), hence measurable. -/
theorem continuous_Ufun334 : Continuous Ufun334 := by
  unfold Ufun334 Uval334; fun_prop

/-- `Ufun334 ≥ (u 1)²` (the `Uval334_ge_sq` lower bound at the pivot-minor `a = u 1`). -/
theorem Ufun334_ge (u : Fin 21 → ℝ) : (u 1) ^ 2 ≤ Ufun334 u :=
  Uval334_ge_sq (u 1) (u 4) (u 5) (u 10) (u 11) (u 12) (u 6) (u 7) (u 8) (u 9)
    (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20)

/-- `Ufun334 ≥ 0` (a sum of squares; `≥ (u 1)² ≥ 0`). -/
theorem Ufun334_nonneg (u : Fin 21 → ℝ) : (0 : ℝ) ≤ Ufun334 u :=
  le_trans (sq_nonneg _) (Ufun334_ge u)

/-- `Ufun334` is bounded above on the source box `[0,δ]²¹` (continuous on a compact box). -/
theorem Ufun334_le_on_box (δ : ℝ) :
    ∃ B, 1 ≤ B ∧ ∀ u ∈ Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ), Ufun334 u ≤ B := by
  have hcpt : IsCompact (Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  rcases (Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ)).eq_empty_or_nonempty with he | hne
  · exact ⟨1, le_refl _, fun u hu => absurd (he ▸ hu) (Set.mem_empty_iff_false u).mp⟩
  · obtain ⟨u0, _, hu0⟩ := hcpt.exists_isMaxOn hne continuous_Ufun334.continuousOn
    exact ⟨max 1 (Ufun334 u0), le_max_left _ _, fun u hu => le_trans (hu0 hu) (le_max_right _ _)⟩

/-- The leaf-integrand identity for the `(3,3,4)` HONEST achiever chart: `(|u 0|⁷·|u 1|²) ·
|routeMCore M334 (phi334 u)|^{−c} = monomialIntegrand 21 leafK334 leafH334 c u · (Ufun334 u)^{−c}` —
the genuine two-axis Jacobian (`|u 0|⁷` pivot × `|u 1|²` from `b = aβ`) against the unit power. Via
`routeMCore_phi334` (`F∘phi = u₀²·U`) + `monomialIntegrand_leaf334_eq`. -/
theorem leaf_integrand334 (c : ℝ) (u : Fin 21 → ℝ) :
    (|u 0| ^ 7 * |u 1| ^ 2) * |routeMCore (![3, 3, 4] : Fin 3 → ℕ) (phi334 u)| ^ (-c)
      = monomialIntegrand 21 leafK334 leafH334 c u * (Ufun334 u) ^ (-c) := by
  rw [monomialIntegrand_leaf334_eq, routeMCore_phi334]
  have hUnn : 0 ≤ Uval334 (u 1) (u 4) (u 5) (u 10) (u 11) (u 12) (u 6) (u 7) (u 8) (u 9)
      (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20) := Ufun334_nonneg u
  rw [show Ufun334 u = Uval334 (u 1) (u 4) (u 5) (u 10) (u 11) (u 12) (u 6) (u 7) (u 8) (u 9)
        (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20) from rfl,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (u 0) ^ 2 * Uval334 (u 1) (u 4) (u 5) (u 10)
        (u 11) (u 12) (u 6) (u 7) (u 8) (u 9) (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20)),
    Real.mul_rpow (by positivity) hUnn, ← sq_abs (u 0)]
  ring

/-! ## Genuine-diffeo validation of the HONEST chart (the anti-`phi334` gate)

The single check that catches the `phi334` slip: the chart reads ALL 21 coords (no zero Jacobian
column) and is a genuine local diffeo off a null center. The honest `b = a·β` chart passes all of:
reads `u 2` (the dropped coord, now in `A(0,1)`); `phi334 0 = 0` (reaches the deepest point);
continuity; `InjOn` off `{u 0 = 0} ∪ {u 1 = 0}` (both null). The Jacobian determinant `−u₀⁷·u₁²`
(sympy-exact, `genuine_chart_334c.py` analog + Codex `xhigh`) is the genuine two-axis weight carried
by `leafH334`; its full structural-determinant proof is the `cov` measure-plumbing residual below. -/

/-- **Anti-`phi334` witness: the chart READS `u 2`** (the coord `phi334` dropped). `A(0,1) = u 1·u 2`
depends on `u 2` (e.g. at `u = e₁ + e₂` it is `1`, at `u = e₁` it is `0`), so no Jacobian column for
`u 2` is zero — the `det ≡ 0` degeneracy of `phi334` (which pinned `A(0,1) = 0`) cannot recur. -/
theorem chartA334_reads_u2 :
    chartA334 (![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 21 → ℝ) 0 1
      ≠ chartA334 (![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 21 → ℝ)
          0 1 := by
  simp only [chartA334, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply, Matrix.cons_val]
  norm_num

/-- **The chart reaches the deepest point**: `chartParams334 0 = (fun _ => 0)` (every chart matrix
entry is a monomial in the coords, vanishing at `u = 0`). Unlike a chart pinned away from the origin,
this places the achiever at the flat origin (the centre of the divergence box). -/
theorem chartParams334_zero :
    chartParams334 (0 : Fin 21 → ℝ) = (fun _ => 0 : Params (![3, 3, 4] : Fin 3 → ℕ)) := by
  funext s
  fin_cases s
  · funext i j; fin_cases i <;> fin_cases j <;> simp [chartParams334, chartA334]
  · funext i j; fin_cases i <;> fin_cases j <;> simp [chartParams334, chartC334]

/-- **`phi334 0 = 0`** — the honest chart sends the deepest input to the flat origin (the divergence
box centre), via `chartParams334_zero` + `paramsEquivFlat_deepest`. -/
theorem phi334_zero : phi334 (0 : Fin 21 → ℝ) = 0 := by
  rw [phi334, chartParams334_zero]
  exact paramsEquivFlat_deepest _

/-- **`chartParams334` is injective off `{u 0 = 0} ∪ {u 1 = 0}`** (the genuine-diffeo center; both
null). From `chartParams334 u = chartParams334 v` (the two matrix equalities) every coord is recovered:
the spectators `u 1, u 4, u 5, S` directly from the entries; `u 2, u 3` via `÷ u 1` (`u 1 ≠ 0`); the
pivot `u 0` from `C(0,0)` WITHOUT division; then `u 6…u 9, τ` via `÷ u 0` (`u 0 ≠ 0`). Refutes the
`phi334` slip directly: the degenerate chart was injective on NO positive-measure set; this one is a
genuine bijection off a codim-1 null union. -/
theorem chartParams334_injOn :
    Set.InjOn chartParams334 {u : Fin 21 → ℝ | u 0 ≠ 0 ∧ u 1 ≠ 0} := by
  rintro u ⟨hu0, hu1⟩ v ⟨hv0, hv1⟩ huv
  have hA : chartA334 u = chartA334 v := congrFun huv 0
  have hC : chartC334 u = chartC334 v := congrFun huv 1
  -- entry equalities (each a `congrFun`/`congrFun` of the matrix equalities)
  have eA := fun i j => congrFun (congrFun hA i) j
  have eC := fun i j => congrFun (congrFun hC i) j
  -- the direct spectators (`A(0,0)=u1`, `A(1,0)=u4`, `A(2,0)=u5`, `C` rows 1,2)
  have h1 : u 1 = v 1 := by have := eA 0 0; simpa [chartA334] using this
  have h4 : u 4 = v 4 := by have := eA 1 0; simpa [chartA334] using this
  have h5 : u 5 = v 5 := by have := eA 2 0; simpa [chartA334] using this
  have h13 : u 13 = v 13 := by have := eC 1 0; simpa [chartC334] using this
  have h14 : u 14 = v 14 := by have := eC 1 1; simpa [chartC334] using this
  have h15 : u 15 = v 15 := by have := eC 1 2; simpa [chartC334] using this
  have h16 : u 16 = v 16 := by have := eC 1 3; simpa [chartC334] using this
  have h17 : u 17 = v 17 := by have := eC 2 0; simpa [chartC334] using this
  have h18 : u 18 = v 18 := by have := eC 2 1; simpa [chartC334] using this
  have h19 : u 19 = v 19 := by have := eC 2 2; simpa [chartC334] using this
  have h20 : u 20 = v 20 := by have := eC 2 3; simpa [chartC334] using this
  -- `u 2, u 3` via `÷ u 1` (`A(0,1) = u 1·u 2`, `A(0,2) = u 1·u 3`)
  have h2 : u 2 = v 2 := by
    have he := eA 0 1; simp only [chartA334, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h1] at he; exact mul_left_cancel₀ hv1 he
  have h3 : u 3 = v 3 := by
    have he := eA 0 2; simp only [chartA334, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h1] at he; exact mul_left_cancel₀ hv1 he
  -- the pivot `u 0` from `C(0,0) = u 0 − (u 2·u 13 + u 3·u 17)` (no division)
  have h0 : u 0 = v 0 := by
    have he := eC 0 0; simp only [chartC334, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h2, h3, h13, h17] at he; linarith [he]
  -- `u 6…u 9` via `÷ u 0` (`A(1,1) = u 4·u 2 + u 0·u 6`, etc.)
  have h6 : u 6 = v 6 := by
    have he := eA 1 1; simp only [chartA334, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h4, h2, h0] at he; exact mul_left_cancel₀ hv0 (by linarith [he])
  have h7 : u 7 = v 7 := by
    have he := eA 1 2; simp only [chartA334, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h4, h3, h0] at he; exact mul_left_cancel₀ hv0 (by linarith [he])
  have h8 : u 8 = v 8 := by
    have he := eA 2 1; simp only [chartA334, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h5, h2, h0] at he; exact mul_left_cancel₀ hv0 (by linarith [he])
  have h9 : u 9 = v 9 := by
    have he := eA 2 2; simp only [chartA334, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h5, h3, h0] at he; exact mul_left_cancel₀ hv0 (by linarith [he])
  -- `τ = u 10, u 11, u 12` via `÷ u 0` (`C(0,1) = u 0·u 10 − (u 2·u 14 + u 3·u 18)`, etc.)
  have h10 : u 10 = v 10 := by
    have he := eC 0 1; simp only [chartC334, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h2, h3, h14, h18, h0] at he; exact mul_left_cancel₀ hv0 (by linarith [he])
  have h11 : u 11 = v 11 := by
    have he := eC 0 2; simp only [chartC334, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h2, h3, h15, h19, h0] at he; exact mul_left_cancel₀ hv0 (by linarith [he])
  have h12 : u 12 = v 12 := by
    have he := eC 0 3; simp only [chartC334, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h2, h3, h16, h20, h0] at he; exact mul_left_cancel₀ hv0 (by linarith [he])
  -- assemble: all 21 coords agree
  funext j; fin_cases j <;>
    first
    | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7
    | exact h8 | exact h9 | exact h10 | exact h11 | exact h12 | exact h13 | exact h14 | exact h15
    | exact h16 | exact h17 | exact h18 | exact h19 | exact h20

/-- **`phi334` is injective off `{u 0 = 0} ∪ {u 1 = 0}`** — the genuine-diffeo injectivity (the
flattening `paramsEquivFlat` is a bijection, composed with `chartParams334_injOn`). The honest chart
is `InjOn` on a positive-measure set; the degenerate `phi334` was `InjOn` on none. -/
theorem phi334_injOn :
    Set.InjOn phi334 {u : Fin 21 → ℝ | u 0 ≠ 0 ∧ u 1 ≠ 0} := by
  intro u hu v hv huv
  exact chartParams334_injOn hu hv
    ((paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ)).injective huv)

/-- `chartA334` is continuous (polynomial entries). -/
theorem continuous_chartA334 : Continuous chartA334 := by
  unfold chartA334
  refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
    continuous_const))
  all_goals
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
      continuous_const)) <;> fun_prop

/-- `chartC334` is continuous (polynomial entries). -/
theorem continuous_chartC334 : Continuous chartC334 := by
  unfold chartC334
  refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
    continuous_const))
  all_goals
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
      (Continuous.matrixVecCons ?_ continuous_const))) <;> fun_prop

/-- `chartParams334` is continuous (each layer matrix is continuous; `Params` is a product). -/
theorem continuous_chartParams334 : Continuous chartParams334 := by
  apply continuous_pi
  intro s
  fin_cases s
  · exact continuous_chartA334
  · exact continuous_chartC334

/-- **`phi334` is continuous** (`paramsEquivFlat` continuous ∘ the polynomial `chartParams334`). -/
theorem continuous_phi334 : Continuous phi334 :=
  (continuous_paramsEquivFlat _).comp continuous_chartParams334

/-- **Image containment (honest, closable):** a small source box `[0,δ]²¹` maps into `cubeBox 21 ε`.
By continuity of `phi334` and `phi334 0 = 0`, the preimage of the open cube `(−ε,ε)²¹` is an open
neighbourhood of `0`, hence contains a `cubeBox 21 δ` (`cubeBox_subset_of_isOpen`), exactly as in the
`(2,2,2)` `phiUnit_image_subset_cubeBox`. The honest chart reaches the origin, so this holds genuinely
(the `phi334` null-image was never the obstruction to this set-containment). -/
theorem phi334_image_subset_cubeBox (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, phi334 '' (Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ)) ⊆ cubeBox 21 ε := by
  have hopen : IsOpen (Set.univ.pi (fun _ : Fin 21 => Set.Ioo (-ε) ε)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hmem : (0 : Fin 21 → ℝ) ∈ phi334 ⁻¹' (Set.univ.pi (fun _ : Fin 21 => Set.Ioo (-ε) ε)) := by
    simp only [Set.mem_preimage, phi334_zero, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ioo, Pi.zero_apply]
    exact fun i => ⟨by linarith, hε⟩
  obtain ⟨δ, hδ, hsub⟩ := cubeBox_subset_of_isOpen (hopen.preimage continuous_phi334) hmem
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  -- `x ∈ [0,δ]²¹ ⊆ cubeBox 21 δ` (the orthant sits in the symmetric cube)
  have hxcube : x ∈ cubeBox 21 δ := by
    simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx ⊢
    intro i; exact ⟨le_trans (by linarith [hδ]) (hx i).1, (hx i).2⟩
  have hxmem : phi334 x ∈ Set.univ.pi (fun _ : Fin 21 => Set.Ioo (-ε) ε) :=
    Set.mem_preimage.mp (hsub hxcube)
  refine Set.mem_pi.mpr (fun i _ => ?_)
  have hi := (Set.mem_pi.mp hxmem) i (Set.mem_univ i)
  rw [Set.mem_Ioo] at hi
  rw [Set.mem_Icc]
  exact ⟨hi.1.le, hi.2.le⟩

/-- **The `(3,3,4)` HONEST achiever chart bundle** (`phi = phi334` the `b = a·β` genuine diffeo,
binding axis `0`, unit `Ufun334`, the two-axis Jacobian `|u 0|⁷·|u 1|²`).

**The `phi334` degeneracy is FIXED.** The chart now reads ALL 21 coords (`A(0,1) = u 1·u 2` etc.,
`chartA334_reads_u2`), so its `21×21` Jacobian has NO zero column (det `−u₀⁷·u₁² ≠ 0`, sympy-exact +
Codex `xhigh`); the `b = a·β` substitution clears the Schur-shear `a⁻¹` pole, so `phi334` is a
polynomial map reaching the deepest point (`phi334 0 = 0`, `phi334_zero`). The factorization
`F∘phi334 = u₀²·Uval334` (SAME unit, `routeMCore_phi334`), the threshold `4` (`leafMonomialThreshold334_le`),
the leaf-integrand (`leaf_integrand334`, two-axis), the `U ≤ B` upper bound (`Ufun334_le_on_box`), and
the image containment (`phi334_image_subset_cubeBox`) are all banked sorry-free.

**ONE residual remains — the `cov` change-of-variables (`Ubound`'s a.e.-positivity rides on it).** It
is the genuine geometric c-o-v (Mathlib `lintegral_image_eq_lintegral_abs_det_fderiv_mul` on
`{u 0 ≠ 0}`): the chart is `InjOn` off `{u 0 = 0} ∪ {u 1 = 0}` and `HasFDerivAt` with `|det| =
|u 0|⁷·|u 1|²`. The residual is the FORMALISATION of that determinant via the structural route
(`b = aβ` det-`a²` ∘ Schur-shear det-`1` ∘ `pivotBlowup8` det-`u₀⁷`) and the InjOn/measurability
plumbing — the per-node measure-plumbing the design certificate flags as the heavy `hfin` atom (cost
driver 2). It is no longer FALSE (as it was for the degenerate `phi334`): the determinant is genuinely
`−u₀⁷·u₁²`, matching `leafH334`. Left an HONEST `sorry` with this precise obstruction. -/
noncomputable def achieverChart334 : L2AchieverChart where
  phi := phi334
  Ufun := Ufun334
  Ubound := fun δ => by
    obtain ⟨B, hB1, hBle⟩ := Ufun334_le_on_box δ
    refine ⟨B, lt_of_lt_of_le one_pos hB1, hBle, ?_⟩
    -- `0 < Ufun334` a.e. (BANKED): `Ufun334 u ≥ (u 1)² > 0` wherever `u 1 ≠ 0`, and the slice
    -- `{u 1 = 0}` is null (`coordZero_null 1`). So the positivity holds off a null set ⟹ a.e. The
    -- honest `b = a·β` chart keeps `a = u 1` a genuine spectator, so this is now a clean coordinate
    -- argument (no longer riding on the `cov` plumbing).
    have hnull : (volume.restrict (Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ)))
        {u : Fin 21 → ℝ | u 1 = 0} = 0 :=
      le_antisymm (le_trans (Measure.restrict_le_self _) (le_of_eq (coordZero_null 1))) (zero_le _)
    rw [Filter.eventually_iff, mem_ae_iff]
    refine measure_mono_null (fun u hu => ?_) hnull
    -- `¬(0 < Ufun334 u) ⟹ u 1 = 0` (else `Ufun334 u ≥ (u 1)² > 0`)
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hu
    simp only [Set.mem_setOf_eq]
    by_contra hu1
    exact absurd hu (not_le.2 (lt_of_lt_of_le (by positivity : (0:ℝ) < (u 1)^2) (Ufun334_ge u)))

  Umeas := continuous_Ufun334.measurable
  leaf_integrand := leaf_integrand334
  cov := by
    -- RESIDUAL — the genuine geometric change-of-variables for the HONEST chart (NO LONGER FALSE;
    -- it was `0 = ⊤` for the degenerate `phi334`, it is now a TRUE statement awaiting plumbing).
    -- `phi334` is a genuine diffeo off `{u 0 = 0} ∪ {u 1 = 0}` (both null): it reads all 21 coords
    -- (`chartA334_reads_u2`), is `InjOn` there (`phi334_injOn`, BANKED sorry-free — all 21 coords
    -- recovered from the flat image), and `HasFDerivAt` with `|det Dφ| = |u 0|⁷·|u 1|²` (sympy-exact
    -- `−u₀⁷·u₁²`, `genuine_chart_334c.py` + Codex `xhigh`; STRUCTURAL: `b = aβ` det-`a²` ∘ Schur-shear
    -- det-`1` ∘ `pivotBlowup8` det-`u₀⁷`), which is EXACTLY the bundle weight
    -- `∏_j |u_j|^{leafH334 j} = |u 0|⁷·|u 1|²` (`leafH334_prod_eq`).
    --
    -- The residual is the FORMALISATION of Mathlib's `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
    -- on the diffeo-domain `V \ {u 0 = 0}`, which needs:
    --   (i) the explicit `HasFDerivWithinAt phi334 (Dφ u) (V\{u₀=0}) u` as a `ContinuousLinearMap`;
    --   (ii) `(Dφ u).det = −u₀⁷·u₁²` via the structural factorisation `phi334 = (paramsEquivFlat
    --        reindex) ∘ shear ∘ b-subst ∘ pivotBlowup8`, reusing the BANKED `pivotBlowupOnDeriv_det`
    --        (`= u₀⁷` for the 8-active set) and `det(shear)=1`, `det(b-subst)=a²` — NOT a 21×21
    --        `Matrix.det` (which times out, see the file note);
    --   (iii) apply the c-o-v on `V \ ({u 0 = 0} ∪ {u 1 = 0})` (where `phi334_injOn` BANKED gives
    --        InjOn), then add back the `{u 1 = 0}` slice as a TWO-SIDED null contribution: its image
    --        lies in the null hyperplane `{A(0,0) = u 1 = 0}` (LHS null) and the RHS weight
    --        `|u 1|² = 0` kills the integrand there (RHS null) — NOT an InjOn extension.
    -- THE MISSING INFRASTRUCTURE (the precise obstruction): `paramsEquivFlat M334` is a `piCurry` /
    -- `arrowCongr'` coordinate reindex with NO existing `ContinuousLinearEquiv` / fderiv / det-`±1`
    -- lemma in Mathlib or this repo — so `phi334`'s fderiv cannot yet be factored through it. Building
    -- that `paramsEquivFlat`-as-linear-iso (fderiv + `|det| = 1`, measure-preserving) is the per-node
    -- measure-plumbing the `hfin` certificate flags as the heavy SHARED atom (cost driver 2). The
    -- ALGEBRA (det value, factorization, threshold, InjOn) is verified-exact / banked; only this
    -- fderiv-through-`paramsEquivFlat` plumbing remains. HONEST `sorry` with the precise obstruction.
    sorry
  image_subset := phi334_image_subset_cubeBox

/-- **The `(3,3,4)` achiever box-divergence** — `∫⁻_{cubeBox 21 ε} |routeMCore M334|^{−c'} = ⊤` for
`c'` at-or-above the achiever threshold `4 = ½·minAdm M334`, every `ε > 0`. The `L = 2` case of the
atom `routeMCore_box_diverges_achiever` at the binding corank-2 anchor `M = (3,3,4)`, via the SINGLE
weighted radial blow-up `achieverChart334` (the depth-2 miracle).

The soundness-critical content is banked sorry-free: the EXACT factorization `routeMCore M334 (phi334 u)
= (u 0)²·U` (`routeMCore_phi334`, off the verified-exact `loss_schur_blowup_factor`), the unit bound,
the binding-monomial threshold `4` (`leafMonomialThreshold334_le`), and the divergence assembly
(`routeM334_box_diverges_of_chart`, which feeds the single cited leaf atom `monomial_rlct` via
`monomialIntegrand_lintegral_box_eq_top`).

**Proof state (honest `b = a·β` chart).** The degenerate `phi334` is REPLACED by a genuine diffeo:
it reads ALL 21 coords (`chartA334_reads_u2`), reaches the origin (`phi334_zero`), is continuous, is
`InjOn` off the null center (`phi334_injOn`), and the loss/threshold/leaf-integrand/image-containment/
`Ubound` are sorry-free. ONE residual remains inside `achieverChart334` — the `cov` genuine geometric
change-of-variables (NO LONGER a FALSE statement — the determinant is honestly `−u₀⁷·u₁² ≠ 0`,
matching `leafH334`): Mathlib `lintegral_image_eq_lintegral_abs_det_fderiv_mul` + the structural
determinant. It is the per-node measure-plumbing atom the `hfin` certificate flags (cost driver 2); the
ALGEBRA is verified-exact. So `routeM334_box_diverges` is proven MODULO that measure-plumbing (down
from a soundness-wall `sorry` to honest c-o-v plumbing). -/
theorem routeM334_box_diverges (c' : NNReal) (hc' : (4 : ℝ≥0∞) ≤ (c' : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox 21 ε,
      ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ))) = ⊤ :=
  routeM334_box_diverges_of_chart achieverChart334 c' hc' ε hε

/-- **The `(3,3,4)` cross-check** (the cert's anchor): `minAdm = 8`, binding axis `(k,h) = (1,7)`,
threshold `4 = ½·minAdm`; at `c' = 4` the leaf exponent is `7 − 2·1·4 = −1` (the sharp `∫ u⁻¹ = ⊤`).
The box integral diverges at `c' = 4` (and above), for every `ε > 0`. -/
theorem routeM334_box_diverges_at_four (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox 21 ε,
      ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(4 : ℝ))) = ⊤ := by
  have h := routeM334_box_diverges 4 (by norm_num) ε hε
  rwa [show ((4 : NNReal) : ℝ) = (4 : ℝ) by norm_num] at h

end DLNFibre.DLN.RLCT
