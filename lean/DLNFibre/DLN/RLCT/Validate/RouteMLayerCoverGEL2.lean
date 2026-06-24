import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverGE
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import DLNFibre.DLN.RLCT.Validate.Case222Resolution

/-!
# `RouteMLayerCoverGEL2` — the `L = 2` achiever box-divergence (single weighted radial blow-up)

The `L = 2` case of the achiever-path box-divergence atom
`routeMCore_box_diverges_achiever` (`RouteMLayerCoverGE.lean`), via a SINGLE weighted radial
blow-up — the depth-2 miracle (no gauge chain needed at `L = 2`).

**Proof state.** The soundness-critical EXACT algebra is banked sorry-free: the post-Schur-blow-up
factorization `loss_schur_blowup_factor` (`‖A·C‖² = u²·U`, pure `ring`), its lift through the actual
chart `routeMCore_phi334` (`routeMCore M334 (phi334 u) = (u 0)²·U`), the unit bound `Uval334_ge_sq`,
the binding-monomial threshold `leafMonomialThreshold334_le` (`= 4 = ½·minAdm`), and the divergence
ASSEMBLY `routeM334_box_diverges_of_chart` (sorry-free FROM the chart bundle, feeding the single cited
leaf atom `monomial_rlct`). The capstone `routeM334_box_diverges` (and the `(3,3,4)` cross-check at
`c' = 4`) follow by applying the assembly to the chart `achieverChart334`.

The THREE residual `sorry`s are all in `achieverChart334`, the GEOMETRIC chart construction. No other
axiom / `native_decide`; the exact `F = u²·U` is PROVEN, not faked.

**⛔ SOUNDNESS FLAW (2026-06-24).** One of those three — the `cov` change-of-variables — is a FALSE
statement, so the chart bundle `achieverChart334` is VACUOUS and the capstone `routeM334_box_diverges`
HAS NO HONEST PROOF as currently architected (it builds only via the `sorry` in `cov`). The chart
`chartParams334` pins `A(0,1)=A(0,2)=0` and drops the input coords `u₂,u₃`, so `phi334 : ℝ²¹ → ℝ²¹`
has Jacobian `det ≡ 0` (rank 19) and Lebesgue-null image; the `cov` field then asserts `0 = ⊤`.
Confirmed by sympy + independent Codex `xhigh`. The headline STATEMENT may still be true; this is a
broken proof route, needing a controller-level chart redesign (make `b=(u₂,u₃)` free + shear back to
flat coords, see the `achieverChart334` docstring). Details + the re-triage of all three residuals are
in that docstring and the inline `cov` sub-blocker.

## The construction (concrete `(3,3,4)`, the binding corank-2 anchor; `minAdm = 8`)

`routeMCore M334 = ‖A·C‖²` with `A : 3×3`, `C : 3×4`. Block `A = [[a, b],[c, E]]`
(`a` scalar, `b` 1×2, `c` 2×1, `E` 2×2), `C = [[y],[S]]` (`y` 1×4, `S` 2×4).

**Schur change** (det `1`, a triangular shear in `(E, y)`): `T := y + a⁻¹·b·S`,
`D := E − c·a⁻¹·b`, giving the EXACT factorization

    A·C = [[a·T], [c·T + D·S]].

**Weighted blow-up** of the 8 normal coordinates `(T, D)` by the pivot `u`: `T = u·(1, τ)`
(`τ : Fin 3 → ℝ`, the pivot is the `T₀ = u` slot), `D = u·Δ` (`Δ : 2×2`). Then EXACTLY

    F ∘ Ψ = u² · U,   U = a²·‖(1,τ)‖² + ‖c·(1,τ) + Δ·S‖²  (u-free),   U ≥ a².

The Schur chart has det `1`; the 8-coordinate pivot blow-up has det `u^{8−1} = u⁷` (binding axis
`(k,h) = (1, 7) = (1, minAdm−1)`, threshold `minAdm/2 = 4`). At `c' = 4` the leaf exponent is
`7 − 2·1·4 = −1`, the sharp `∫ u⁻¹ = ⊤`, fed to `monomialIntegrand_lintegral_box_eq_top`. The unit
`U` is dropped by `U ≤ C` on the compact box (`U^{−c'} ≥ C^{−c'} > 0`).

Verified EXACT in flat coordinates (`/tmp/schur_check.py`, this thread's `codex/l2-chart-answer.md`).
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

/-- The `(3,3,4)` leaf loss-base exponents on `Fin 21`: `k = 1` on a single binding axis `p`, `0`
elsewhere (the loss base `(|u_p|²)`). -/
def leafK334 (p : Fin 21) : Fin 21 → ℕ := fun j => if j = p then 1 else 0

/-- The `(3,3,4)` leaf Jacobian exponents on `Fin 21`: `h = 7 = minAdm − 1` on the binding axis `p`
(the `pivotBlowupOn` determinant `|u_p|⁷`), `0` elsewhere. -/
def leafH334 (p : Fin 21) : Fin 21 → ℕ := fun j => if j = p then 7 else 0

/-- The binding axis has `leafK334 p p = 1 ≠ 0` — the singular-axis witness for
`monomialIntegrand_lintegral_box_eq_top`. -/
theorem leafK334_binding (p : Fin 21) : leafK334 p p ≠ 0 := by
  simp [leafK334]

/-- **The leaf monomial threshold is `≤ 4 = ½·minAdm`** (the binding axis `(k,h) = (1, 7) = (1, 8−1)`
realises `8/2` via `monomialThreshold_le_regularSeq`). The `≤`-direction input: for `c' ≥ 4`, the
`d = 21` leaf monomial diverges. -/
theorem leafMonomialThreshold334_le (p : Fin 21) :
    monomialThreshold 21 (leafK334 p) (leafH334 p) ≤ 4 := by
  have h := monomialThreshold_le_regularSeq 21 (leafK334 p) (leafH334 p) 8 (by norm_num) p
    (by simp [leafK334]) (by simp [leafH334])
  have hcast : ((8 : ℕ) : ℝ≥0∞) / 2 = 4 := by
    rw [show ((8 : ℕ) : ℝ≥0∞) = (8 : ℝ≥0∞) by norm_num]
    rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  rwa [hcast] at h

/-- **Single-axis monomial evaluation.** `monomialIntegrand 21 (leafK334 p) (leafH334 p) c u =
|u p|⁷ · (|u p|²)^{−c}` — the 20 spectator axes contribute `|·|⁰ = 1`, leaving only the binding
axis `p` (`h_p = 7`, `2·k_p = 2`). -/
theorem monomialIntegrand_leaf334_eq (p : Fin 21) (c : ℝ) (u : Fin 21 → ℝ) :
    monomialIntegrand 21 (leafK334 p) (leafH334 p) c u
      = |u p| ^ 7 * (|u p| ^ 2) ^ (-c) := by
  unfold monomialIntegrand leafK334 leafH334
  rw [Finset.prod_eq_single p, Finset.prod_eq_single p]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ p) h
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ p) h

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

/-- The achiever layer-`0` matrix `A⁽⁰⁾` (3×3): pivot-minor `a = u 1`, column-0 cross strip
`c = (u 4, u 5)`, residual block blown up by the pivot (`u·Δ`), top cross strip `b = 0`. The minor `a`
is UNSHIFTED, so the chart passes through the flat origin (`phi334 0 = 0`, the deepest point) and the
unit `U ≥ a² = (u 1)²` vanishes there — hence the divergence drops the null `{U = 0}` a.e. (the
`Ubound` field) rather than relying on a positive lower bound. -/
noncomputable def chartA334 (u : Fin 21 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![u 1, 0, 0;
     u 4, u 0 * u 6, u 0 * u 7;
     u 5, u 0 * u 8, u 0 * u 9]

/-- The achiever layer-`1` matrix `A⁽¹⁾` (3×4): top row `= (u 0)·(1, τ)` (pivot `u 0` in slot `(0,0)`,
`τ = (u 10, u 11, u 12)`), bottom block `S = (u 13 … u 20)`. -/
noncomputable def chartC334 (u : Fin 21 → ℝ) : Matrix (Fin 3) (Fin 4) ℝ :=
  !![u 0, u 0 * u 10, u 0 * u 11, u 0 * u 12;
     u 13, u 14, u 15, u 16;
     u 17, u 18, u 19, u 20]

/-- The achiever `Params M334` (the post-Schur-blow-up matrices), assembled by `Fin.cons` over the
two layers. `chartParams334 u 0 = chartA334 u` (3×3), `chartParams334 u 1 = chartC334 u` (3×4). -/
noncomputable def chartParams334 (u : Fin 21 → ℝ) : Params (![3, 3, 4] : Fin 3 → ℕ) :=
  Fin.cons (chartA334 u) (Fin.cons (chartC334 u) (fun i => i.elim0))

/-- **The loss factorization (EXACT, sorry-free).** `dlnLoss M334 0 (chartParams334 u) = (u 0)² · U`
with `U = Uval334 …` (the `u`-free unit, `≥ a² = (u 1)²`). Expand `dlnLoss` via `prod_two_layer334`
(the `Fin 3 / Fin 4 / Fin 3` sums), read off the 12 matrix entries, and apply
`loss_schur_blowup_factor` (the banked exact algebra). This is the soundness-critical `F = u²·U`
identity, proven not faked. -/
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

/-- **The achiever flat chart for `(3,3,4)`** `phi334 := paramsEquivFlat M334 ∘ chartParams334`, an
`(Fin 21 → ℝ) → (Fin 21 → ℝ)` map (the Schur-blow-up matrices, reindexed into flat coordinates). -/
noncomputable def phi334 (u : Fin 21 → ℝ) : Fin (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) → ℝ :=
  paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ) (chartParams334 u)

/-- **The `routeMCore` factorization (EXACT, sorry-free).** `routeMCore M334 (phi334 u) = (u 0)² · U`
(`U = Uval334 …`): the flat core, pulled back through the achiever chart, is the binding monomial
`(u 0)²` times the `u`-free unit `U`. Since `routeMCore M334 = dlnLoss M334 0 ∘ (paramsEquivFlat).symm`
and `phi334 = paramsEquivFlat ∘ chartParams334`, the `symm`/`apply` cancel, leaving
`dlnLoss M334 0 (chartParams334 u)` — discharged by `dlnLoss_chartParams334` (the banked exact algebra).
This is the soundness-critical `F ∘ phi = u²·U` identity, proven not faked. -/
theorem routeMCore_phi334 (u : Fin 21 → ℝ) :
    routeMCore (![3, 3, 4] : Fin 3 → ℕ) (phi334 u)
      = (u 0) ^ 2 * Uval334 (u 1) (u 4) (u 5) (u 10) (u 11) (u 12) (u 6) (u 7) (u 8) (u 9)
          (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20) := by
  rw [routeMCore, phi334, MeasurableEquiv.symm_apply_apply, dlnLoss_chartParams334]

/-- **`routeMCore M334 (phi334 u) ≥ 0`** and `> 0` off the pivot-zero locus `{u 0 = 0}` (the unit
`U ≥ a² = (u 1)² ≥ 0`, and `(u 0)² > 0` when `u 0 ≠ 0`; combined with `U ≥ (u 1)²` the product is
`≥ 0`, and the loss is a sum of squares so `≥ 0` directly). Recorded as the nonvanishing the
divergence integrand needs. -/
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
with the single-weighted-blow-up achiever properties at binding axis `p`. Carrying the bundle as an
explicit hypothesis set isolates the divergence ASSEMBLY (proven sorry-free from the bundle) from the
chart CONSTRUCTION (the Schur-shear ∘ `pivotBlowupOn`, discharged separately). `Ufun` is the `u`-free
unit (`= Uval334` in chart coords), `B` its compact-box upper bound, `c₀` its lower bound. -/
structure L2AchieverChart where
  /-- The chart map (Schur-shear ∘ pivot blow-up, in flat coordinates). -/
  phi : (Fin 21 → ℝ) → (Fin 21 → ℝ)
  /-- The binding axis (the blow-up pivot). -/
  p : Fin 21
  /-- The unit factor `U` of `F ∘ phi = (u_p)² · U`. -/
  Ufun : (Fin 21 → ℝ) → ℝ
  /-- On each source box `[0,δ]²¹`, `U` admits a `δ`-dependent compact upper bound `B > 0`, and `U`
  is positive a.e. on the box (the SOUNDNESS-critical pair: `U ≤ B` gives `U^{−c'} ≥ B^{−c'} > 0`
  where `U > 0`; the achiever curve passes through the origin so `U → 0` there, but the vanishing
  locus `{U = 0}` is a proper subvariety, null, dropped a.e.). -/
  Ubound : ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
    (∀ u ∈ Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ), Ufun u ≤ B) ∧
    ∀ᵐ u ∂(volume.restrict (Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ))), 0 < Ufun u
  /-- `U` is measurable (it is a polynomial in the chart coordinates). -/
  Umeas : Measurable Ufun
  /-- The leaf-integrand identity: `|u_p|⁷ · |F ∘ phi|^{−c} = monomialIntegrand · U^{−c}` (the
  binding monomial against the unit power), on the chart orthant. The `(3,3,4)` analog of
  `myF222_phiUnit_leaf_integrand`. -/
  leaf_integrand : ∀ (c : ℝ) (u : Fin 21 → ℝ),
    |u p| ^ 7 * |routeMCore (![3, 3, 4] : Fin 3 → ℕ) (phi u)| ^ (-c)
      = monomialIntegrand 21 (leafK334 p) (leafH334 p) c u * (Ufun u) ^ (-c)
  /-- The composite change-of-variables (the chart Jacobian `|det| = |u_p|⁷`, off the pivot-zero
  locus): `∫⁻_{phi '' ((V \ {u_p=0}))} g = ∫⁻_{V \ {u_p=0}} ofReal(|u_p|⁷) · g (phi u)`. -/
  cov : ∀ (V : Set (Fin 21 → ℝ)), MeasurableSet V → ∀ (g : (Fin 21 → ℝ) → ℝ≥0∞),
    ∫⁻ x in phi '' (V \ {x | x p = 0}), g x
      = ∫⁻ u in V \ {x | x p = 0}, ENNReal.ofReal (|u p| ^ 7) * g (phi u)
  /-- Image containment: a small source box `[0,δ]²¹` maps into `cubeBox 21 ε`. -/
  image_subset : ∀ ε : ℝ, 0 < ε →
    ∃ δ > 0, phi '' (Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ)) ⊆ cubeBox 21 ε

/-- **The achiever leaf-box divergence (unit-stripped, from the bundle).** For `c' ≥ 4` (`0 < c'`),
`∫⁻_{[0,ε]²¹} monomialIntegrand · U^{−c'} = ⊤`: lower-bound `U^{−c'} ≥ B^{−c'} > 0` (`U ∈ [1, B]`,
`−c' < 0`), pull the constant out, and apply the bare-monomial box divergence
(`monomialIntegrand_lintegral_box_eq_top`). The `(3,3,4)` analog of `leaf_box_div`. -/
theorem leaf334_box_div (W : L2AchieverChart) (c' : ℝ) (hc'0 : 0 < c')
    (hc' : monomialThreshold 21 (leafK334 W.p) (leafH334 W.p) ≤ ENNReal.ofReal c')
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ u in Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) ε),
      ENNReal.ofReal (monomialIntegrand 21 (leafK334 W.p) (leafH334 W.p) c' u
        * (W.Ufun u) ^ (-c')) = ⊤ := by
  obtain ⟨B, hB0, hBle, hUpos_ae⟩ := W.Ubound ε
  set box := Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) ε) with hbox
  have hmonomeas : Measurable
      (fun u : Fin 21 → ℝ => monomialIntegrand 21 (leafK334 W.p) (leafH334 W.p) c' u) := by
    unfold monomialIntegrand; fun_prop
  have hmonomeas' : Measurable
      (fun u : Fin 21 → ℝ => ENNReal.ofReal (|monomialIntegrand 21 (leafK334 W.p) (leafH334 W.p) c' u|)) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hmonomeas)
  have hlb : ∫⁻ u in box, ENNReal.ofReal (B ^ (-c'))
        * ENNReal.ofReal (|monomialIntegrand 21 (leafK334 W.p) (leafH334 W.p) c' u|)
      ≤ ∫⁻ u in box, ENNReal.ofReal (monomialIntegrand 21 (leafK334 W.p) (leafH334 W.p) c' u
          * (W.Ufun u) ^ (-c')) := by
    apply setLIntegral_mono_ae
      (ENNReal.measurable_ofReal.comp (hmonomeas.mul (W.Umeas.pow_const _))).aemeasurable
    -- the inequality holds where `0 < U` (a.e. on the box: the vanishing locus `{U=0}` is null)
    rw [ae_restrict_iff' (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))] at hUpos_ae
    filter_upwards [hUpos_ae] with u hUposimp hu
    have hUpos := hUposimp hu
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hmono : 0 ≤ monomialIntegrand 21 (leafK334 W.p) (leafH334 W.p) c' u := by
      unfold monomialIntegrand; positivity
    rw [abs_of_nonneg hmono, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hUpos (hBle u hu) (by linarith)) hmono
  have hBne : ENNReal.ofReal (B ^ (-c')) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.rpow_pos_of_pos hB0 _
  rw [lintegral_const_mul _ hmonomeas',
    monomialIntegrand_lintegral_box_eq_top 21 (leafK334 W.p) (leafH334 W.p)
      ⟨W.p, leafK334_binding W.p⟩ c' hc' hc'0 hε,
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
  have hthr : monomialThreshold 21 (leafK334 W.p) (leafH334 W.p) ≤ ENNReal.ofReal (c' : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact le_trans (leafMonomialThreshold334_le W.p) hc'
  obtain ⟨δ, hδ, hsub⟩ := W.image_subset ε hε
  set P := Set.univ.pi (fun _ : Fin 21 => Set.Icc (0 : ℝ) δ) with hP
  have hPmeas : MeasurableSet P := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  -- the pivot-zero locus is null, so the `\ {x_p = 0}` restriction is a no-op
  have hdiffnull : ∫⁻ x in P \ {x | x W.p = 0},
        ENNReal.ofReal (|x W.p| ^ 7) * ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) (W.phi x)|
          ^ (-(c' : ℝ)))
      = ∫⁻ x in P, ENNReal.ofReal (|x W.p| ^ 7)
          * ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) (W.phi x)| ^ (-(c' : ℝ))) := by
    apply setLIntegral_congr
    exact MeasureTheory.diff_ae_eq_self.2 (measure_mono_null Set.inter_subset_right
      (coordZero_null W.p))
  apply top_le_iff.1
  calc (⊤ : ℝ≥0∞)
      = ∫⁻ u in P,
          ENNReal.ofReal (monomialIntegrand 21 (leafK334 W.p) (leafH334 W.p) (c' : ℝ) u
            * (W.Ufun u) ^ (-(c' : ℝ))) :=
        (leaf334_box_div W (c' : ℝ) hc'0 hthr δ hδ).symm
    _ = ∫⁻ u in P, ENNReal.ofReal (|u W.p| ^ 7)
          * ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) (W.phi u)| ^ (-(c' : ℝ))) := by
        refine setLIntegral_congr_fun hPmeas (fun u _ => ?_)
        rw [← ENNReal.ofReal_mul (by positivity), W.leaf_integrand]
    _ = ∫⁻ x in P \ {x | x W.p = 0}, ENNReal.ofReal (|x W.p| ^ 7)
          * ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) (W.phi x)| ^ (-(c' : ℝ))) :=
        hdiffnull.symm
    _ = ∫⁻ x in W.phi '' (P \ {x | x W.p = 0}),
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

/-- The leaf-integrand identity for the `(3,3,4)` achiever chart: `|u₀|⁷ · |routeMCore M334 (phi334
u)|^{−c} = monomialIntegrand 21 (leafK334 0) (leafH334 0) c u · (Ufun334 u)^{−c}` — the binding
monomial against the unit power. Via `routeMCore_phi334` (`F∘phi = u₀²·U`) + `monomialIntegrand_leaf334_eq`. -/
theorem leaf_integrand334 (c : ℝ) (u : Fin 21 → ℝ) :
    |u 0| ^ 7 * |routeMCore (![3, 3, 4] : Fin 3 → ℕ) (phi334 u)| ^ (-c)
      = monomialIntegrand 21 (leafK334 0) (leafH334 0) c u * (Ufun334 u) ^ (-c) := by
  rw [monomialIntegrand_leaf334_eq, routeMCore_phi334]
  have hUnn : 0 ≤ Uval334 (u 1) (u 4) (u 5) (u 10) (u 11) (u 12) (u 6) (u 7) (u 8) (u 9)
      (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20) := Ufun334_nonneg u
  rw [show Ufun334 u = Uval334 (u 1) (u 4) (u 5) (u 10) (u 11) (u 12) (u 6) (u 7) (u 8) (u 9)
        (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20) from rfl,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (u 0) ^ 2 * Uval334 (u 1) (u 4) (u 5) (u 10)
        (u 11) (u 12) (u 6) (u 7) (u 8) (u 9) (u 13) (u 14) (u 15) (u 16) (u 17) (u 18) (u 19) (u 20)),
    Real.mul_rpow (by positivity) hUnn, ← sq_abs (u 0)]
  ring

/-- **The `(3,3,4)` achiever chart bundle** (`phi = phi334`, binding axis `p = 0`, unit `Ufun334`).
The factorization / bounds / measurability / leaf-integrand are banked sorry-free.

**SOUNDNESS FLAW (found 2026-06-24, confirmed by sympy + independent Codex `xhigh`): the `cov`
field is a FALSE statement, so this bundle is VACUOUS and `routeM334_box_diverges` cannot be honestly
completed with `phi334` as currently defined. This is an ARCHITECTURAL defect, not measure-plumbing.**

  Reason. `chartParams334` pins the two `A`-entries `A(0,1) = A(0,2) = 0` to CONSTANTS and never
  reads the input coords `u 2`, `u 3`. So as a map `phi334 : (Fin 21 → ℝ) → (Fin 21 → ℝ)`:
  • its 21×21 Jacobian is rank `19`, `det ≡ 0` (NOT `|u₀|⁷`) — kernel directions `∂/∂u₂, ∂/∂u₃`;
  • its image lies in the codim-2 set `{x | x_{A01} = x_{A02} = 0}`, which is Lebesgue-NULL in `ℝ²¹`;
  • it is `InjOn` on no positive-measure set.
  The `cov` field asserts `∫⁻_{phi '' (V\{x₀=0})} g = ∫⁻_{V\{x₀=0}} ofReal(|u₀|⁷)·g(phi u)`. The LHS
  integrates over a null image set, so `= 0` for the assembly's `g ≥ 0`; the RHS carries weight
  `|u₀|⁷ > 0` a.e. and is the DIVERGENT monomial integral (`= ⊤`). The field therefore asserts
  `0 = ⊤`. Mathlib's `lintegral_image_eq_lintegral_abs_det_fderiv_mul` requires `InjOn` + the actual
  derivative `det`; here that `det ≡ 0`, so it yields `∫_{image} g = ∫ ofReal(0)·g(phi) = 0`, never
  `|u₀|⁷`. The forbidden-to-touch sorry-free assembly `routeM334_box_diverges_of_chart` is correct
  GIVEN a bundle; it is the bundle (this chart) that cannot exist. The HEADLINE STATEMENT may still
  be true — this is a broken proof route, not a refutation — but it has no honest Lean proof here.

  Minimal fix (controller-level redesign; NOT done here — it changes the soundness-critical
  `dlnLoss_chartParams334` / `routeMCore_phi334`, which this thread is gated against altering):
  make `b = (u₂,u₃)` GENUINELY FREE and use the Schur shear back to flat coords (`T = y − a⁻¹bS`,
  `D = E + ca⁻¹b`) composed with the 8-coord pivot blow-up (`y = u₀·(1,τ)`, `E = u₀·Δ`). The product
  is still `A·C = [[a·y],[c·y + E·S]]` so the loss factor `u₀²·U` SURVIVES, while `b` stays a coord
  and the map becomes a genuine diffeo with `|det| = |u₀|⁷`. CAVEAT (Codex): the shear is regular only
  off `{a = u₁ ≠ 0}`, but the achiever curve passes through the origin (`a = 0`); the `a⁻¹bS` terms
  then create a separate `image_subset` / exceptional-locus obstruction that the redesign must resolve
  (e.g. shift `a` away from `0`, or take the shear's exceptional locus into the dropped null set).

**RESIDUALS, re-triaged against the flaw:**
- `cov`: FALSE as stated (see above). NOT closable with this `phi334`. Honest `sorry` retained; this
  is the soundness wall surfaced to the controller.
- `image_subset` (`phi334 '' [0,δ]²¹ ⊆ cubeBox 21 ε`): independently TRUE and closable (continuity +
  `phi334 0 = 0`; image-null does not block set-containment) — but stated against the to-be-redesigned
  `phi334`, so left `sorry` pending the chart redesign rather than proved against a chart that changes.
- `Ubound` a.e.-positivity (`0 < Ufun334` a.e.): independently TRUE and closable (`Ufun334 ≥ (u₁)²`,
  vanishing locus a proper subvariety) — `Ufun334` SURVIVES the redesign; left `sorry` for the same
  reason (kept with the bundle it belongs to). -/
noncomputable def achieverChart334 : L2AchieverChart where
  phi := phi334
  p := 0
  Ufun := Ufun334
  Ubound := fun δ => by
    obtain ⟨B, hB1, hBle⟩ := Ufun334_le_on_box δ
    refine ⟨B, lt_of_lt_of_le one_pos hB1, hBle, ?_⟩
    -- RESIDUAL: `0 < Ufun334` a.e. on `[0,δ]²¹` — i.e. the vanishing locus `{Ufun334 = 0}` is null.
    -- This residual is independently TRUE and closable: `Ufun334 = Uval334(u1,…) ≥ 0` vanishes only
    -- on the proper algebraic subvariety `{u1 = 0 ∧ c·(1,τ)+Δ·S = 0}` (codim ≥ 1, measure-zero,
    -- independent of the pivot `u 0`); `ae_iff` + `measure_mono_null` onto that subvariety (a finite
    -- union of coordinate-defined determinantal loci, each null by `addHaar`-of-proper-submanifold).
    -- LEFT `sorry`: the bundle is VACUOUS (the `cov` field below is a FALSE statement — see the
    -- `achieverChart334` docstring), so closing this honest field cannot make the headline sound;
    -- the chart needs a controller-level redesign that will change `phi334` (and may change this
    -- field's surrounding chart, though `Ufun334` itself survives). Not proved against a chart that
    -- is to be replaced.
    sorry
  Umeas := continuous_Ufun334.measurable
  leaf_integrand := leaf_integrand334
  cov := by
    -- ⛔ SOUNDNESS WALL — this field is a FALSE statement; it has NO honest proof with this `phi334`.
    -- `phi334 = paramsEquivFlat M334 ∘ chartParams334` pins `A(0,1)=A(0,2)=0` (constants) and never
    -- reads `u 2`, `u 3`, so its 21×21 Jacobian has `det ≡ 0` (rank 19, NOT `|u₀|⁷`) and its image
    -- is Lebesgue-NULL in `ℝ²¹`. The field then asserts `0 = ⊤` (null-image LHS vs the divergent
    -- weighted RHS). Confirmed by sympy (`det J = 0`, rank 19) + independent Codex `xhigh`. The
    -- earlier sub-blocker (factor `chartParams334 = schurShear ∘ pivotBlowupOn active₈ 0`) is WRONG:
    -- `chartParams334` is not such a composite — `b = (u₂,u₃)` are dropped, not shear-absorbed. The
    -- FIX is a controller-level chart redesign (make `b` free, shear back to flat; see the
    -- `achieverChart334` docstring), which alters the gated soundness-critical `dlnLoss_chartParams334`
    -- / `routeMCore_phi334` and so is OUT OF SCOPE for this thread. Honest `sorry` retained.
    sorry
  image_subset := by
    -- RESIDUAL: `phi334 '' [0,δ]²¹ ⊆ cubeBox 21 ε` for a small `δ`. Independently TRUE and closable:
    -- `phi334` is continuous (`paramsEquivFlat` continuous ∘ `chartParams334` polynomial) and
    -- `phi334 0 = 0` (every chart entry vanishes at `u = 0`), so the preimage of the open cube
    -- `(−ε,ε)²¹` is an open nbhd of `0` and contains a `cubeBox 21 δ` (`cubeBox_subset_of_isOpen`),
    -- as in `phiUnit_image_subset_cubeBox`. The image being Lebesgue-null does NOT block this
    -- set-containment.
    -- LEFT `sorry`: the bundle is VACUOUS (the `cov` field is a FALSE statement — see the
    -- `achieverChart334` docstring), so this field is stated against a `phi334` that the controller
    -- redesign will change; not proved against a chart that is to be replaced.
    sorry

/-- **The `(3,3,4)` achiever box-divergence** — `∫⁻_{cubeBox 21 ε} |routeMCore M334|^{−c'} = ⊤` for
`c'` at-or-above the achiever threshold `4 = ½·minAdm M334`, every `ε > 0`. The `L = 2` case of the
atom `routeMCore_box_diverges_achiever` at the binding corank-2 anchor `M = (3,3,4)`, via the SINGLE
weighted radial blow-up `achieverChart334` (the depth-2 miracle).

The soundness-critical content is banked sorry-free: the EXACT factorization `routeMCore M334 (phi334 u)
= (u 0)²·U` (`routeMCore_phi334`, off the verified-exact `loss_schur_blowup_factor`), the unit bound,
the binding-monomial threshold `4` (`leafMonomialThreshold334_le`), and the divergence assembly
(`routeM334_box_diverges_of_chart`, which feeds the single cited leaf atom `monomial_rlct` via
`monomialIntegrand_lintegral_box_eq_top`).

**⛔ NO HONEST PROOF as architected.** This term builds only because `achieverChart334.cov` is a
`sorry`, and that `cov` field is a FALSE statement (the chart `phi334` has `det ≡ 0` and Lebesgue-null
image — see the `achieverChart334` docstring). So `routeM334_box_diverges` is NOT sorry-free in any
honest sense; the chart needs a controller-level redesign before this can stand. The STATEMENT is
plausibly true; the PROOF route via this chart cannot be completed. -/
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
