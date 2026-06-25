import DLNFibre.DLN.RLCT.Validate.RadialResidualPower
import DLNFibre.DLN.RLCT.Validate.RouteMSchur
import DLNFibre.DLN.RLCT.Validate.Case334RouteStep
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet

/-!
# `RouteM334Hfin` — the `(3,3,4)` upper-bound finiteness (the N4 depth-2 rank-stratified hfin instance)

The `(3,3,4)` instance of the hfin upper bound: for `c' < ½·minAdm M334 = 4`,

    ∫⁻_{routeMBaseNbhd M334} |routeMCore M334 x|^{−c'} < ⊤.

This is the `cover_le` premise of `routeMLayerCover_of_atoms` for `M = (3,3,4)`, the companion of the
banked achiever-path box-divergence atom `routeM334_box_diverges` (the lower bound,
`RouteMLayerCoverGEL2.lean`). UNLIKE `(4,4,2,2)` (closed via the iterated-fibre route, `RouteM4422Hfin`),
`(3,3,4)` is corank-2 and the iterated-fibre route UNDERSHOOTS (it caps at `min(3/2, 6) = 3/2 ≪ 4`,
pp-r1-genM-2 §Q2). It needs the **rank-stratified radial-Schur recursion** with the genuine ADDITIVE
disjoint-sum threshold `4 = 2 + 2` (the `‖T‖²` Morse spectator rlct `2` ⊕ the `‖Δ·S‖²` core rlct
`λ_{2,4} = 2`).

## The route (pp-r1-genM-2 §Q1–Q3, decorrelated-Codex confirmed; thread 28 cert + `codex/`)

The additive threshold is reached by the residual-power convolution atom `radial_morse_residual_power_le`
(banked S2-free, `RadialResidualPower.lean`): the `‖T‖²` peel leaves a residual power
`w^{−(c' − 2)}` of the core `w = ‖Δ·S‖²`, which the core integral then absorbs at the SHIFTED exponent
`c'' = c' − 2 < 2` via the `r² = 4`-chart Δ-blow-up cover (a-axis divisor `r²/2 = 2` ⊗ the rank-1 N2a
leaf `(∑col²)·‖row·S‖²`). Threshold equivalence: `c' < 4 ⟺ c'' < 2 = λ_{2,4}`.

## STATUS — partial (the WHOLE additive-threshold composition banked; the frame transport the ONE gap)

* **Banked (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`, S2-FREE):**
  - `matTranspose`/`measurePreserving_matTranspose` — the matrix-transpose MP (the documented thrashing
    piece, the S-first fibre's plumbing).
  - `core_T_peel_le` + `core_T_peel_le_ae` — the residual-power `‖T‖²`-peel (Tonelli, threshold `2`),
    the latter null-set-aware (the core vanishes on `{Δ·S = 0}`), built on the banked
    `radial_morse_residual_power_le`.
  - `core334_S_fibre_le` + `core334_lt_top` — the corank-2 core finiteness `∫_{Δ,S} frobSq(Δ·S)^{−c''} < ⊤`
    for `c'' < 2`, via the S-FIRST transpose-fibre route (`frobSq_rmatMul_transpose` → `fibre_lintegral_mul_le`
    at `p/2 = 4/2 = 2` → the `2×2` Morse leaf `frobSq22_box_lt_top`), AVOIDING the radial minor-pivot
    recursion / `schur_minorPivot_split`.
  - `corePoly334`/`corePoly334_ne_zero`/`flat334`/`measurePreserving_flat334`/`frobSq_core334_ne_zero_ae` —
    the `{frobSq(Δ·S) = 0}` null set (the polynomial-zero-set route via the MP flatten).
  - `resolved334_lt_top` — the KEYSTONE: the full `4 = 2 + 2` composition
    `∫_{Δ,S,T} (∑ Tᵢ² + frobSq(Δ·S))^{−c'} < ⊤` for `2 < c' < 4`. The end-to-end additive-threshold
    verification, all the above wired together.
* **Gap (ONE precisely-named `sorry`):** `routeMCore_M334_threshold_lt_top` rests ONLY on the FRAME
  TRANSPORT — the measure-preserving cover-up-to-null bringing the flat `frobSq(A0·A1)` (A0 3×3, A1 3×4,
  over `(−1,1)^21`) into the `‖T‖² ⊕ frobSq(Δ·S)` normal form of `resolved334_lt_top`, via the Schur-frame
  `g5_pivotNode`/`recStep` atlas (the `(2,2,2)` `myF222_threshold_lt_top'` analog at the `r²`-chart scale).
  The singularity is the A1-rank-drop (nonlinear/rank-local — no elementary global reparametrization). The
  achiever chart `chartParams334`/`Uval334` (`RouteMLayerCoverGEL2`) realises it on the LOWER-bound side; the
  UPPER-bound full cover is the remaining measure-theoretic long pole.

## S2-hygiene
The hfin CONCLUSION is S2-FREE (Morse leaves, the residual-power atom, Tonelli, the rank-1 leaf, the
transpose-fibre, the polynomial null set). Every banked piece above is `#print axioms`-clean
`[propext, Classical.choice, Quot.sound]` — NO `monomial_rlct`, NO new axiom.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## `minAdm M334 = 8` (the threshold value `½·minAdm = 4`) -/

/-- `minAdm (![3,3,4]) = 8` (so the hfin threshold is `c' < ½·minAdm = 4`). The `minAdm`-function value
matching `Case334RouteStep.minAdm_M334`'s `.toNat` form (the `minAdm` def is exactly that `.toNat`). -/
theorem minAdm_M334_eq : minAdm (![3, 3, 4] : Fin 3 → ℕ) = 8 := minAdm_M334

/-! ## The Tonelli `‖T‖²`-peel via the residual-power convolution atom (BUILT)

The disjoint-sum cell `(‖T‖² + W)^{−c'}` — `T` an `(m+1)`-dim Morse spectator, `W = core ≥ 0` — peels
the `T`-block by the new residual-power atom, leaving `Cresid · W^{−(c' − (m+1)/2)}`: the core at the
SHIFTED exponent. The Tonelli outer-integral over the core variables then closes from the core's
finiteness at `c'' = c' − (m+1)/2`. This is the additive-threshold bridge the crude Morse-peel could not
supply (pp §Q1). -/

/-- **The Tonelli `T`-peel bound.** For an `(m+1)`-dim Morse spectator block `T` over `[−Tw,Tw]^{m+1}`
disjoint from a strictly-positive core value `w(z) > 0`, with `c'` ABOVE the Morse threshold `(m+1)/2`,
the joint integral is bounded by `Cresid` times the core integral at the SHIFTED exponent `c' − (m+1)/2`:

    ∫_z ∫_T (∑ Tᵢ² + w z)^{−c'} ≤ Cresid (m+1) c' · ∫_z (w z)^{−(c' − (m+1)/2)}.

The disjoint-sum additive-threshold glue: `radial_morse_residual_power_le` (banked) per fixed `z` gives
the residual power, then `lintegral_const_mul'` pulls `Cresid` out. S2-FREE. (Only the per-`z`
positivity `hwpos` is consumed — the inner residual-power atom needs `w z > 0`, not measurability of `w`.) -/
theorem core_T_peel_le {m k : ℕ} (c' : ℝ) (hc' : (m + 1 : ℝ) / 2 < c')
    (Tw : ℝ) (hTw : 0 < Tw) (w : (Fin k → ℝ) → ℝ) (hwpos : ∀ z, 0 < w z)
    (Z : Set (Fin k → ℝ)) :
    ∫⁻ z in Z, ∫⁻ T in morseBox (m + 1) Tw,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))
      ≤ ENNReal.ofReal (Cresid (m + 1) c')
        * ∫⁻ z in Z, ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) := by
  -- per fixed `z`: the inner `T`-integral ≤ ofReal(Cresid · (w z)^{−(c'−(m+1)/2)}) by the new atom
  have hinner : ∀ z, ∫⁻ T in morseBox (m + 1) Tw,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))
      ≤ ENNReal.ofReal (Cresid (m + 1) c')
        * ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) := by
    intro z
    rw [← ENNReal.ofReal_mul (Cresid_nonneg _ _)]
    exact radial_morse_residual_power_le m c' hc' Tw hTw (w z) (hwpos z)
  calc ∫⁻ z in Z, ∫⁻ T in morseBox (m + 1) Tw,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))
      ≤ ∫⁻ z in Z, ENNReal.ofReal (Cresid (m + 1) c')
          * ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) :=
        lintegral_mono (fun z => hinner z)
    _ = ENNReal.ofReal (Cresid (m + 1) c')
          * ∫⁻ z in Z, ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top

/-- **The a.e. Tonelli `T`-peel bound (the null-set-aware variant).** As `core_T_peel_le`, but with the
core positivity needed only A.E. on `Z` (`hwpos : ∀ᵐ z ∂volume.restrict Z, 0 < w z`) — the realistic
hypothesis, since the determinantal core `frobSq (Δ·S)` vanishes on a positive-codimension NULL set (where
the inner `T`-integral genuinely diverges for `c' ≥ 2`, but which the outer lintegral ignores). The bound
`∫_T (∑Tᵢ² + w z)^{−c'} ≤ Cresid·(w z)^{−(c'−(m+1)/2)}` holds per `z` with `w z > 0` (the banked atom), so
`lintegral_mono_ae` upgrades the a.e. positivity to the integral inequality. S2-FREE. -/
theorem core_T_peel_le_ae {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c' : ℝ) (hc' : (m + 1 : ℝ) / 2 < c')
    (Tw : ℝ) (hTw : 0 < Tw) (w : Ω → ℝ) (Z : Set Ω)
    (hwpos : ∀ᵐ z ∂(μ.restrict Z), 0 < w z) :
    (∫⁻ z in Z, (∫⁻ T in morseBox (m + 1) Tw,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))) ∂μ)
      ≤ ENNReal.ofReal (Cresid (m + 1) c')
        * ∫⁻ z in Z, ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ := by
  calc (∫⁻ z in Z, (∫⁻ T in morseBox (m + 1) Tw,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))) ∂μ)
      ≤ ∫⁻ z in Z, ENNReal.ofReal (Cresid (m + 1) c')
          * ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ := by
        refine lintegral_mono_ae (hwpos.mono (fun z hz => ?_))
        rw [← ENNReal.ofReal_mul (Cresid_nonneg _ _)]
        exact radial_morse_residual_power_le m c' hc' Tw hTw (w z) hz
    _ = ENNReal.ofReal (Cresid (m + 1) c')
          * ∫⁻ z in Z, ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top

/-! ## The corank-2 core route (S2-FREE, the transpose-fibre resolution — design note)

The core `‖Δ·S‖²` (Δ a `2×2` left factor, S a `2×4` right factor) integrated over both boxes is finite
for `c'' < 2 = λ_{2,4}` — WITHOUT the radial Δ-blow-up. Integrate S FIRST as the LEFT factor via the
transpose `frobSq(Δ·S) = frobSq(Sᵀ·Δᵀ)` (`frobSq_rmatMul_transpose` below): `Sᵀ` is `4×2` (p=4 rows), so
`fibre_lintegral_mul_le` (X=Sᵀ, p=4) gives the per-Δ bound at threshold `p/2 = 4/2 = 2`; then
`∫_Δ frobSq(Δ)^{−c''}` is the `2×2 = 4`-dim Morse leaf (`frobSq22_box_lt_top`, threshold `4/2 = 2`). Both
factors `≥ 2`, so the core resolves at `c'' < 2` (numerically pinned). This sidesteps the nested
minor-pivot recursion (pp §Q3: the inner threshold `5/2 > 2` never binds; the S-first fibre realises it
directly). The transpose-box measure-preserving reshape (`matTranspose` MP) is the one remaining plumbing
piece for the core-integral wiring; the transpose entrywise identity is banked below. -/

/-- The transpose entrywise identity `frobSq (Δ·S) = frobSq (Sᵀ·Δᵀ)`: `(Sᵀ·Δᵀ)ⱼᵢ = (Δ·S)ᵢⱼ`, so the
sum-of-squares is the same (a `Finset.sum_comm` + per-entry `ring`). The S-first fibre's algebraic core. -/
theorem frobSq_rmatMul_transpose {n p q : ℕ} (Δ : Fin p → Fin n → ℝ) (S : Fin n → Fin q → ℝ) :
    frobSq (rmatMul Δ S) = frobSq (rmatMul (fun j k => S k j) (fun k i => Δ i k)) := by
  unfold frobSq rmatMul
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  congr 1
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ## The matrix-transpose measure-preserving reshape (the S-first fibre's plumbing)

The transpose `S : Fin n → Fin q → ℝ ↦ Sᵀ : Fin q → Fin n → ℝ` (`Sᵀ j k = S k j`) is a coordinate
reindexing of the `n·q` entries — measure-preserving. Built from the `e22`/`MeasurableEquiv.piCurry` +
`arrowCongr'` pattern (`MatMulFibre.e22`): uncurry `Fin n → Fin q → ℝ` to `(Σ _:Fin n, Fin q) → ℝ`,
reindex by the sigma-swap `(Σ _:Fin q, Fin n) ≃ (Σ _:Fin n, Fin q)` (`sigmaEquivProd`/`prodComm`), and
re-curry to `Fin q → Fin n → ℝ`. -/

/-- The sigma-swap reindex `(_ : Fin n) × Fin q ≃ (_ : Fin q) × Fin n` (uncurry both to products,
swap by `prodComm`). The index equiv the transpose `arrowCongr'` rides on (domain `Σ_n Fin q` → codomain
`Σ_q Fin n`, the direction `arrowCongr'` reindexes). -/
def sigmaSwapEquiv (n q : ℕ) : ((_ : Fin n) × Fin q) ≃ ((_ : Fin q) × Fin n) :=
  (Equiv.sigmaEquivProd (Fin n) (Fin q)).trans
    ((Equiv.prodComm (Fin n) (Fin q)).trans (Equiv.sigmaEquivProd (Fin q) (Fin n)).symm)

/-- **The matrix transpose as a `MeasurableEquiv`** `(Fin n → Fin q → ℝ) ≃ᵐ (Fin q → Fin n → ℝ)`. Built
from sorry-free MP bricks (the `e22` pattern): `piCurry.symm` (uncurry to `Σ_n Fin q → ℝ`), `arrowCongr'`
(the `sigmaSwapEquiv` reindex to `Σ_q Fin n → ℝ`), `piCurry` (re-curry to `Fin q → Fin n → ℝ`). -/
noncomputable def matTranspose (n q : ℕ) : (Fin n → Fin q → ℝ) ≃ᵐ (Fin q → Fin n → ℝ) :=
  ((MeasurableEquiv.piCurry (fun (_ : Fin n) (_ : Fin q) => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr' (sigmaSwapEquiv n q) (MeasurableEquiv.refl ℝ))).trans
    (MeasurableEquiv.piCurry (fun (_ : Fin q) (_ : Fin n) => ℝ))

/-- `matTranspose n q S j k = S k j` (the transpose reads the transposed entry). -/
theorem matTranspose_apply (n q : ℕ) (S : Fin n → Fin q → ℝ) (j : Fin q) (k : Fin n) :
    matTranspose n q S j k = S k j := rfl

theorem measurePreserving_matTranspose (n q : ℕ) :
    MeasurePreserving (matTranspose n q)
      (volume : Measure (Fin n → Fin q → ℝ)) (volume : Measure (Fin q → Fin n → ℝ)) := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCurry (fun (_ : Fin n) (_ : Fin q) => ℝ)).symm
      (volume : Measure (Fin n → Fin q → ℝ)) (volume : Measure ((_ : Fin n) × Fin q → ℝ)) :=
    (measurePreserving_piCurry (fun (_ : Fin n) (_ : Fin q) => ℝ)
      (fun _ _ => (volume : Measure ℝ))).symm
      (MeasurableEquiv.piCurry (fun (_ : Fin n) (_ : Fin q) => ℝ))
  have h2 : MeasurePreserving
      (MeasurableEquiv.arrowCongr' (sigmaSwapEquiv n q) (MeasurableEquiv.refl ℝ))
      (volume : Measure ((_ : Fin n) × Fin q → ℝ)) (volume : Measure ((_ : Fin q) × Fin n → ℝ)) :=
    volume_preserving_arrowCongr' (sigmaSwapEquiv n q) (MeasurableEquiv.refl ℝ)
      (MeasurePreserving.id _)
  have h3 : MeasurePreserving
      (MeasurableEquiv.piCurry (fun (_ : Fin q) (_ : Fin n) => ℝ))
      (volume : Measure ((_ : Fin q) × Fin n → ℝ)) (volume : Measure (Fin q → Fin n → ℝ)) :=
    measurePreserving_piCurry (fun (_ : Fin q) (_ : Fin n) => ℝ)
      (fun _ _ => (volume : Measure ℝ))
  exact (h1.trans h2).trans h3

/-! ## The corank-2 core finiteness (BUILT, S2-FREE — the S-first transpose-fibre resolution)

`∫_{Δ box}∫_{S box} frobSq(Δ·S)^{−c''} < ⊤` for `c'' < 2 = λ_{2,4}` (Δ a `2×2` left factor, S a `2×4`
right factor). The S-first route (docstring §"corank-2 core route", decorrelated-Codex confirmed): integrate
`S` FIRST as the LEFT factor via the transpose `frobSq(Δ·S) = frobSq(Sᵀ·Δᵀ)` (`frobSq_rmatMul_transpose`),
where `Sᵀ` is `4×2` (p=4 rows). `fibre_lintegral_mul_le` (X=Sᵀ, p=4) bounds the per-Δ S-integral at the
fibre threshold `p/2 = 4/2 = 2`, then `∫_Δ frobSq(Δ)^{−c''}` is the `2×2 = 4`-dim Morse leaf
(`frobSq22_box_lt_top`, threshold `4/2 = 2`). Both factors realise `2`, so the core resolves at `c'' < 2`
WITHOUT the nested minor-pivot radial recursion (`schur_minorPivot_split`). S2-FREE. -/

/-- **The corank-2 core S-integral bound (per fixed Δ, BUILT).** For `0 < c'' < 2`, integrating the
`2×4` free block `S` first (via its transpose `Sᵀ`, a `4×2` left factor, MP by `matTranspose`) bounds the
per-Δ core integral by `fibreConst 4 2 2 1 c''` times `frobSq(Δ)^{−c''}`:

    ∫_{S box} frobSq(Δ·S)^{−c''} dS ≤ fibreConst 4 2 2 1 c'' · frobSq(Δ)^{−c''}.

The transpose `frobSq(Δ·S) = frobSq(Sᵀ·Δᵀ)` routes the `4` (S-columns = product columns) into the
left-factor row-count, so the fibre threshold is `p/2 = 4/2 = 2`. -/
theorem core334_S_fibre_le (c'' : ℝ) (hc0 : 0 < c'') (hc2 : c'' < 2) (Δ : Fin 2 → Fin 2 → ℝ) :
    ∫⁻ S in matBox 2 4 1, ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))
      ≤ fibreConst 4 2 2 1 c'' * ENNReal.ofReal ((frobSq Δ) ^ (-c'')) := by
  -- rewrite the integrand by the transpose identity `frobSq(Δ·S) = frobSq(Sᵀ·Δᵀ)`
  have hrw : ∀ S : Fin 2 → Fin 4 → ℝ,
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))
        = ENNReal.ofReal ((frobSq (rmatMul (matTranspose 2 4 S) (fun k i => Δ i k))) ^ (-c'')) := by
    intro S
    rw [frobSq_rmatMul_transpose Δ S]
    rfl
  rw [setLIntegral_congr_fun (matBox_measurableSet 2 4 1) (fun S _ => hrw S)]
  -- transport the S-box via `matTranspose` (MP) to the Sᵀ-box `matBox 4 2 1`
  have hmp := measurePreserving_matTranspose 2 4
  have hpre : matBox 2 4 1 = matTranspose 2 4 ⁻¹' matBox 4 2 1 := by
    ext S
    simp only [matBox, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h j k; rw [matTranspose_apply]; exact h k j
    · intro h k j; have := h j k; rwa [matTranspose_apply] at this
  rw [hpre,
    hmp.setLIntegral_comp_preimage_emb (matTranspose 2 4).measurableEmbedding
      (fun X => ENNReal.ofReal ((frobSq (rmatMul X (fun k i => Δ i k))) ^ (-c''))) (matBox 4 2 1)]
  -- the fibre lemma: X = Sᵀ (p=4,n=2,q=2), Y = Δᵀ, threshold c'' < p/2 = 2
  have hbound := fibre_lintegral_mul_le (p := 4) (n := 2) (q := 2) (by norm_num) (by norm_num)
    (by norm_num) 1 one_pos c'' hc0 (by norm_num; linarith) (fun k i => Δ i k)
  -- frobSq Δᵀ = frobSq Δ
  have hfrobT : frobSq (fun k i => Δ i k) = frobSq Δ := by
    unfold frobSq; rw [Finset.sum_comm]
  rwa [hfrobT] at hbound

/-- **The corank-2 core finiteness (BUILT, S2-FREE).** `∫_{Δ box}∫_{S box} frobSq(Δ·S)^{−c''} < ⊤` for
`c'' < 2 = λ_{2,4}`. The S-first transpose-fibre route: `core334_S_fibre_le` (per-Δ S-bound, threshold 2)
feeding the `2×2 = 4`-dim Morse leaf `frobSq22_box_lt_top` (threshold 2). Both factors realise `2`. The
`c'' = 0` case is the trivial constant-`1` integral over the finite-volume box. -/
theorem core334_lt_top (c'' : ℝ) (hc0 : 0 ≤ c'') (hc2 : c'' < 2) :
    ∫⁻ Δ in matBox 2 2 1, ∫⁻ S in matBox 2 4 1,
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'')) < ⊤ := by
  rcases eq_or_lt_of_le hc0 with hc0' | hc0'
  · -- c'' = 0: the integrand is (·)^0 = 1, the double integral is vol·vol < ⊤
    have hzero : c'' = 0 := hc0'.symm
    have hone : ∀ (Δ : Fin 2 → Fin 2 → ℝ) (S : Fin 2 → Fin 4 → ℝ),
        ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'')) = 1 := by
      intro Δ S; rw [hzero]; simp [Real.rpow_zero]
    have hvolfin : ∀ p n : ℕ, volume (matBox p n 1) < ⊤ := by
      intro p n
      have hcpt : IsCompact (matBox p n (1 : ℝ)) := by
        have heq : matBox p n (1 : ℝ)
            = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) := by
          ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
        rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
      exact hcpt.measure_lt_top
    simp only [hone]
    rw [setLIntegral_const]
    refine ENNReal.mul_lt_top ?_ (hvolfin 2 2)
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.one_lt_top (hvolfin 2 4)
  · -- 0 < c'' < 2: the S-first fibre bound, then the Δ Morse leaf
    calc ∫⁻ Δ in matBox 2 2 1, ∫⁻ S in matBox 2 4 1,
            ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))
        ≤ ∫⁻ Δ in matBox 2 2 1, fibreConst 4 2 2 1 c'' * ENNReal.ofReal ((frobSq Δ) ^ (-c'')) :=
          lintegral_mono (fun Δ => core334_S_fibre_le c'' hc0' hc2 Δ)
      _ = fibreConst 4 2 2 1 c'' * ∫⁻ Δ in matBox 2 2 1, ENNReal.ofReal ((frobSq Δ) ^ (-c'')) := by
          rw [lintegral_const_mul' _ _
            (fibreConst_ne_top 4 2 2 1 c'' one_pos (by norm_num; linarith) (by norm_num) (by norm_num))]
      _ < ⊤ := by
          have hcfin := fibreConst_lt_top 4 2 2 1 c'' one_pos (by norm_num; linarith)
            (by norm_num) (by norm_num)
          exact ENNReal.mul_lt_top hcfin (frobSq22_box_lt_top 1 one_pos c'' hc2)

/-! ## The resolved-form finiteness (BUILT — the additive-threshold `4 = 2 + 2` composition)

The cover form the frame transport must reach: a `4`-dim Morse spectator block `T` disjoint-summed onto the
corank-2 core `frobSq (Δ·S)`. For `2 < c' < 4`, the joint integral

    ∫_{Δ box} ∫_{S box} ∫_{T box} (∑ᵢ Tᵢ² + frobSq (Δ·S))^{−c'}

is FINITE. This is the keystone verification that the additive threshold composes end-to-end: the T-peel
(`core_T_peel_le_ae`, the `‖T‖²` Morse spectator, threshold `(m+1)/2 = 4/2 = 2`) leaves the core at the
SHIFTED exponent `c'' = c' − 2 < 2`, which `core334_lt_top` resolves. The T-peel rides on the core being
`> 0` a.e. (the determinantal core vanishes on the null `{Δ·S = 0}` — `frobSq_core334_ne_zero_ae`). All
S2-FREE. -/

open MvPolynomial in
/-- The corank-2 core `frobSq (rmatMul Δ S)` as the evaluation of an `MvPolynomial (Fin 12) ℝ` in the
flattened `(Δ, S)` coords (Δ at coords `0..3`, S at coords `4..11`). The polynomial encoding for the
`ae_eval_ne_zero` null-set argument. -/
noncomputable def corePoly334 : MvPolynomial (Fin 12) ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 4,
    (∑ k : Fin 2,
      (!![X 0, X 1; X 2, X 3] : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 12) ℝ)) i k
        * (!![X 4, X 5, X 6, X 7; X 8, X 9, X 10, X 11]
          : Matrix (Fin 2) (Fin 4) (MvPolynomial (Fin 12) ℝ)) k j) ^ 2

open MvPolynomial in
/-- **`corePoly334 ≠ 0`** (the formal polynomial is not identically zero): at the slice
`Δ = I₂` (`X 0 = X 3 = 1`, `X 1 = X 2 = 0`), `S = !![1,0,0,0;0,0,0,0]` (`X 4 = 1`, rest `0`), the core
`frobSq (Δ·S) = frobSq (!![1,0,0,0;0,0,0,0]) = 1 ≠ 0`. -/
theorem corePoly334_ne_zero : corePoly334 ≠ 0 := by
  intro h0
  set w : Fin 12 → ℝ := Pi.single 0 1 + Pi.single 3 1 + Pi.single 4 1 with hw
  have hval : MvPolynomial.eval w corePoly334 = 1 := by
    rw [corePoly334]
    simp only [map_sum, map_pow, map_mul, Fin.sum_univ_two, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val', MvPolynomial.eval_X]
    simp only [hw, Pi.add_apply, Pi.single_apply]
    norm_num [Fin.ext_iff]
  rw [h0] at hval; simp at hval

/-- The flatten `(Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) → (Fin 12 → ℝ)`: reads the `Δ` entries
into coords `0..3` (row-major: `(0,0),(0,1),(1,0),(1,1)`) and the `S` entries into coords `4..11`
(row-major over `Fin 2 × Fin 4`). The explicit decode matching `corePoly334`'s `X`-index layout. -/
noncomputable def flat334 (p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)) : Fin 12 → ℝ :=
  fun k => if h : (k : ℕ) < 4 then p.1 ⟨(k : ℕ) / 2, by omega⟩ ⟨(k : ℕ) % 2, by omega⟩
    else p.2 ⟨((k : ℕ) - 4) / 4, by omega⟩ ⟨((k : ℕ) - 4) % 4, by omega⟩

/-- A matrix-space flatten `(Fin r → Fin n → ℝ) ≃ᵐ (Fin (r * n) → ℝ)` (the `e22`-pattern at general
`(r, n)`): `piCurry.symm` (uncurry to `Σ_r Fin n → ℝ`) then `arrowCongr'` by the
`sigmaEquivProd ∘ finProdFinEquiv` index equiv. -/
noncomputable def matToFlatEquiv (r n : ℕ) : (Fin r → Fin n → ℝ) ≃ᵐ (Fin (r * n) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin r) (_ : Fin n) => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr'
      ((Equiv.sigmaEquivProd (Fin r) (Fin n)).trans finProdFinEquiv) (MeasurableEquiv.refl ℝ))

theorem measurePreserving_matToFlatEquiv (r n : ℕ) :
    MeasurePreserving (matToFlatEquiv r n)
      (volume : Measure (Fin r → Fin n → ℝ)) (volume : Measure (Fin (r * n) → ℝ)) := by
  unfold matToFlatEquiv
  refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
    ((Equiv.sigmaEquivProd (Fin r) (Fin n)).trans finProdFinEquiv)
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))
  exact (measurePreserving_piCurry (fun (_ : Fin r) (_ : Fin n) => ℝ)
    (fun _ _ => (volume : Measure ℝ))).symm
    (MeasurableEquiv.piCurry (fun (_ : Fin r) (_ : Fin n) => ℝ))

/-- The combine `(Fin 4 → ℝ) × (Fin 8 → ℝ) ≃ᵐ (Fin 12 → ℝ)`: `sumPiEquivProdPi.symm` (to the `Fin 4 ⊕ Fin 8`
arrow) then `piCongrLeft` by `finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12`. -/
noncomputable def combine48 : ((Fin 4 → ℝ) × (Fin 8 → ℝ)) ≃ᵐ (Fin 12 → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 4 ⊕ Fin 8 => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin 12 => ℝ)
      (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12)))

theorem measurePreserving_combine48 :
    MeasurePreserving combine48
      (volume : Measure ((Fin 4 → ℝ) × (Fin 8 → ℝ))) (volume : Measure (Fin 12 → ℝ)) := by
  unfold combine48
  have hsum : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 4 ⊕ Fin 8 => ℝ)).symm
      (volume : Measure ((Fin 4 → ℝ) × (Fin 8 → ℝ)))
      (volume : Measure (Fin 4 ⊕ Fin 8 → ℝ)) :=
    volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 4 ⊕ Fin 8 => ℝ)
  have hcongr : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 12 => ℝ)
        (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12))
      (volume : Measure (Fin 4 ⊕ Fin 8 → ℝ)) (volume : Measure (Fin 12 → ℝ)) :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin 12 => ℝ)
      (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12)
  exact hsum.trans hcongr

/-- `flat334` as the composition `combine48 ∘ (matToFlatEquiv 2 2 ×ᵐ matToFlatEquiv 2 4)` — a
coordinate reindexing of the `4 + 8 = 12` real entries, hence measure-preserving. -/
theorem measurePreserving_flat334 :
    MeasurePreserving flat334
      (volume : Measure ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)))
      (volume : Measure (Fin 12 → ℝ)) := by
  -- the composed MP map, then `flat334` = its coe (by `funext`/`fin_cases`, all `rfl`)
  have hcomp : MeasurePreserving
      (combine48 ∘ (Prod.map (matToFlatEquiv 2 2) (matToFlatEquiv 2 4)))
      (volume : Measure ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)))
      (volume : Measure (Fin 12 → ℝ)) := by
    refine MeasurePreserving.comp measurePreserving_combine48 ?_
    have hpp := (measurePreserving_matToFlatEquiv 2 2).prod (measurePreserving_matToFlatEquiv 2 4)
    rw [show (volume : Measure ((Fin 4 → ℝ) × (Fin 8 → ℝ))) = volume.prod volume from rfl]
    rw [show (volume : Measure ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ))) = volume.prod volume
      from rfl]
    exact hpp
  have heq : flat334 = combine48 ∘ (Prod.map (matToFlatEquiv 2 2) (matToFlatEquiv 2 4)) := by
    funext p k
    fin_cases k <;> rfl
  rw [heq]; exact hcomp

/-- `eval (flat334 p) corePoly334 = frobSq (rmatMul p.1 p.2)` — the flatten carries the formal polynomial
to the genuine determinantal core (the `X`-index layout of `corePoly334` matches `flat334`'s decode). -/
theorem eval_corePoly334_flat334 (p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)) :
    MvPolynomial.eval (flat334 p) corePoly334 = frobSq (rmatMul p.1 p.2) := by
  -- the 12 flatten decodes at the concrete `Fin 12` literals (each `rfl` — the `dite`/`/`/`%` reduce)
  have h0 : flat334 p 0 = p.1 0 0 := rfl
  have h1 : flat334 p 1 = p.1 0 1 := rfl
  have h2 : flat334 p 2 = p.1 1 0 := rfl
  have h3 : flat334 p 3 = p.1 1 1 := rfl
  have h4 : flat334 p 4 = p.2 0 0 := rfl
  have h5 : flat334 p 5 = p.2 0 1 := rfl
  have h6 : flat334 p 6 = p.2 0 2 := rfl
  have h7 : flat334 p 7 = p.2 0 3 := rfl
  have h8 : flat334 p 8 = p.2 1 0 := rfl
  have h9 : flat334 p 9 = p.2 1 1 := rfl
  have h10 : flat334 p 10 = p.2 1 2 := rfl
  have h11 : flat334 p 11 = p.2 1 3 := rfl
  rw [corePoly334]
  unfold frobSq rmatMul
  simp only [Fin.sum_univ_two, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
    Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val',
    map_sum, map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- **The corank-2 core is positive a.e.** (over the product `volume`): `∀ᵐ (Δ,S), 0 < frobSq (Δ·S)`.
The core `frobSq (rmatMul Δ S) = eval (flat334 (Δ,S)) corePoly334` (a nonzero polynomial,
`corePoly334_ne_zero`), so `{(Δ,S) | frobSq (Δ·S) = 0}` is the `flat334`-preimage of the Lebesgue-null
`{x | eval x corePoly334 = 0}` (`MvPolynomial.ae_eval_ne_zero`), null since `flat334` is MP; the `frobSq ≥ 0`
sharpening turns `≠ 0` into `> 0`. The a.e. positivity the T-peel (`core_T_peel_le_ae`) consumes. -/
theorem frobSq_core334_ne_zero_ae :
    ∀ᵐ p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) ∂(volume),
      0 < frobSq (rmatMul p.1 p.2) := by
  -- pull back the a.e.-nonvanishing of `corePoly334` along the MP flatten `flat334`
  have hae : ∀ᵐ x : Fin 12 → ℝ, MvPolynomial.eval x corePoly334 ≠ 0 :=
    MvPolynomial.ae_eval_ne_zero corePoly334 corePoly334_ne_zero
  have hmeasSet : MeasurableSet {x : Fin 12 → ℝ | MvPolynomial.eval x corePoly334 ≠ 0} :=
    (MvPolynomial.measurableSet_zeroSet corePoly334).compl.congr (by ext x; simp)
  have hpull : ∀ᵐ p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) ∂(volume),
      MvPolynomial.eval (flat334 p) corePoly334 ≠ 0 := by
    rw [← measurePreserving_flat334.map_eq] at hae
    exact (ae_map_iff measurePreserving_flat334.measurable.aemeasurable hmeasSet).1 hae
  refine hpull.mono (fun p hp => ?_)
  rw [eval_corePoly334_flat334] at hp
  exact lt_of_le_of_ne (frobSq_nonneg _) (Ne.symm hp)

/-- **The resolved-form finiteness (BUILT — the `4 = 2 + 2` additive-threshold composition).** For
`2 < c' < 4`, the `‖T‖² ⊕ frobSq (Δ·S)` cell core integral (T a `4`-dim Morse spectator, Δ a `2×2`
residual, S a `2×4` free block) is finite:

    ∫_{Δ box} ∫_{S box} ∫_{T box} (∑ᵢ Tᵢ² + frobSq (Δ·S))^{−c'} < ⊤.

The T-peel (`core_T_peel_le_ae`, m+1 = 4, threshold 2) leaves the core at the shifted exponent
`c'' = c' − 2 < 2`, resolved by `core334_lt_top`. Rides on `frobSq_core334_ne_zero_ae` (core `> 0` a.e.).
S2-FREE. The shape the frame transport must deliver. -/
theorem resolved334_lt_top (c' : ℝ) (hc2 : 2 < c') (hc4 : c' < 4) :
    ∫⁻ Δ in matBox 2 2 1, ∫⁻ S in matBox 2 4 1, ∫⁻ T in morseBox 4 1,
      ENNReal.ofReal ((∑ i, (T i) ^ 2 + frobSq (rmatMul Δ S)) ^ (-c')) < ⊤ := by
  -- combine the outer ∫_Δ∫_S into ∫_{(Δ,S)} over the product (Tonelli), apply the a.e. T-peel,
  -- then un-combine the residual to ∫_Δ∫_S = core334_lt_top (c'-2).
  set w : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) → ℝ :=
    fun p => frobSq (rmatMul p.1 p.2) with hwdef
  -- the joint (p, T) integrand `(∑ T² + w p)^{−c'}` is measurable (needed for Tonelli)
  have hmeasT : Measurable (fun q : ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
      ENNReal.ofReal ((∑ i, (q.2 i) ^ 2 + w q.1) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    show Measurable (fun q : ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
        (∑ i, (q.2 i) ^ 2 + frobSq (rmatMul q.1.1 q.1.2)))
    unfold frobSq rmatMul; fun_prop
  -- Step 1: Tonelli ∫_Δ∫_S∫_T = ∫_{(Δ,S)}∫_T over the product box B = Δbox ×ˢ Sbox
  have hstep1 : ∫⁻ Δ in matBox 2 2 1, ∫⁻ S in matBox 2 4 1, ∫⁻ T in morseBox 4 1,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + frobSq (rmatMul Δ S)) ^ (-c'))
      = ∫⁻ p in (matBox 2 2 1 ×ˢ matBox 2 4 1), (∫⁻ T in morseBox 4 1,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w p) ^ (-c'))) ∂volume := by
    rw [Measure.volume_eq_prod (Fin 2 → Fin 2 → ℝ) (Fin 2 → Fin 4 → ℝ),
      setLIntegral_prod _ (Measurable.lintegral_prod_right hmeasT).aemeasurable]
  rw [hstep1]
  -- Step 2: the a.e. T-peel (m+1 = 4, m = 3): bound by Cresid · ∫_{(Δ,S)} w^{−(c'−2)}
  have hwpos : ∀ᵐ z ∂(volume.restrict (matBox 2 2 1 ×ˢ matBox 2 4 1)), 0 < w z :=
    ae_restrict_of_ae frobSq_core334_ne_zero_ae
  have hpeel := core_T_peel_le_ae (m := 3) (volume) c' (by norm_num; linarith) 1 one_pos w
    (matBox 2 2 1 ×ˢ matBox 2 4 1) hwpos
  refine lt_of_le_of_lt hpeel ?_
  -- Step 3: the residual ∫_{(Δ,S)} w^{−(c'−2)} = ∫_Δ∫_S frobSq(Δ·S)^{−(c'−2)} = core334_lt_top (c'-2)
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hmeasResid : Measurable
      (fun p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
        ENNReal.ofReal ((w p) ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2))) (by fun_prop)
    show Measurable (fun p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
        frobSq (rmatMul p.1 p.2))
    unfold frobSq rmatMul; fun_prop
  have hresid : (∫⁻ p in (matBox 2 2 1 ×ˢ matBox 2 4 1),
        ENNReal.ofReal ((w p) ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2))))
      = ∫⁻ Δ in matBox 2 2 1, ∫⁻ S in matBox 2 4 1,
          ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-(c' - 2))) := by
    rw [Measure.volume_eq_prod (Fin 2 → Fin 2 → ℝ) (Fin 2 → Fin 4 → ℝ),
      setLIntegral_prod _ hmeasResid.aemeasurable]
    refine setLIntegral_congr_fun (matBox_measurableSet 2 2 1) (fun Δ _ => ?_)
    refine setLIntegral_congr_fun (matBox_measurableSet 2 4 1) (fun S _ => ?_)
    rw [hwdef]; norm_num
  rw [hresid]
  exact core334_lt_top (c' - 2) (by linarith) (by linarith)

/-- **The `(3,3,4)` hfin upper bound (the N4 depth-2 instance, GAP = the frame transport ONLY).** For
`c' < ½·minAdm M334 = 4`, `∫⁻_{routeMBaseNbhd M334} |routeMCore M334 x|^{−c'} < ⊤`. The rank-stratified
analog of `routeMCore_M4422_threshold_lt_top`.

The additive-threshold composition `4 = 2 + 2` is **BUILT** (`resolved334_lt_top`, axiom-clean S2-free): the
`‖T‖²` Morse-spectator peel (`core_T_peel_le_ae`, threshold `2`) feeds the corank-2 core `frobSq (Δ·S)` at
the shifted exponent `c'' = c' − 2 < 2`, resolved by the S-first transpose-fibre route (`core334_lt_top`,
threshold `λ_{2,4} = 2`, avoiding the radial minor-pivot recursion). The core-`> 0`-a.e. fact the T-peel
rides on is BUILT (`frobSq_core334_ne_zero_ae`, via the polynomial `corePoly334` + the MP flatten
`flat334`).

GAP (`sorry`): the FRAME TRANSPORT alone — a measure-preserving cover-up-to-null of `routeMBaseNbhd M334 =
(−1,1)^21` bringing the flat `routeMCore M334 = frobSq(A0·A1)` (A0 3×3, A1 3×4) into the `‖T‖² ⊕ frobSq(Δ·S)`
normal form of `resolved334_lt_top`, via the Schur-frame blow-up `g5_pivotNode`/`recStep` atlas (the
`(2,2,2)` `myF222_threshold_lt_top'` analog at the `r²`-chart scale). The singularity binds at the
A1-rank-drop locus (nonlinear/rank-local — no elementary global reparametrization). The achiever chart
`chartParams334`/`Uval334` (`RouteMLayerCoverGEL2`) realises this transport on the lower-bound side; the
UPPER-bound full cover is the remaining measure-theoretic long pole. Everything DOWNSTREAM of the transport
(`resolved334_lt_top` + the T-peel + the core resolution + the null set) is BANKED sorry-free, axiom-clean. -/
theorem routeMCore_M334_threshold_lt_top (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm (![3, 3, 4] : Fin 3 → ℕ) : ℝ) / 2) :
    ∫⁻ x in routeMBaseNbhd (![3, 3, 4] : Fin 3 → ℕ),
      ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ))) < ⊤ := by
  rw [minAdm_M334_eq] at hc'
  have hc4 : (c' : ℝ) < 4 := by linarith
  -- The remaining gap: the frame transport reducing this to `resolved334_lt_top` (for `2 < c' < 4`)
  -- + the trivial `c' ≤ 2` finiteness. All downstream pieces (`resolved334_lt_top`,
  -- `core334_lt_top`, `core_T_peel_le_ae`, `frobSq_core334_ne_zero_ae`) are banked sorry-free.
  sorry

end DLNFibre.DLN.RLCT
