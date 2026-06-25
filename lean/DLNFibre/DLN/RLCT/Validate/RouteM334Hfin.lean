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

## STATUS — partial (the headline reduces to ONE gap: the `A0` radial-chart cover; gap NARROWED)

The headline `routeMCore_M334_threshold_lt_top` is no longer itself a `sorry`: it reduces, via the banked
clean MP plumbing `routeMCore_M334_le_matBox`, to the `A0` radial-chart cover `matBox334_blowup_lt_top`
(the sole remaining `sorry`), and the trivial `c' = 0` case. The blow-up's algebraic heart + the radial
divisor + the resolved normal form are all banked sorry-free.

* **Banked (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`, S2-FREE):**
  - The corank-2 resolution (the RHS of the gap): `matTranspose`/`measurePreserving_matTranspose`,
    `core_T_peel_le`(`_ae`), `core334_S_fibre_le`/`core334_lt_top` (S-first transpose-fibre, AVOIDING the
    minor-pivot recursion), `corePoly334`/`flat334`/`frobSq_core334_ne_zero_ae` (null set), and the KEYSTONE
    `resolved334_lt_top` — the `4 = 2 + 2` composition `∫_{Δ,S,T} (∑ Tᵢ² + frobSq(Δ·S))^{−c'} < ⊤`.
  - The clean MP plumbing (THIS file, new): `dlnLoss_M334_eq_frobSq`, `prod_M334_eq_rmatMul`, the MP
    reshape `eParams334` + `paramsBox334` + the preimage lemmas, and `routeMCore_M334_le_matBox` —
    dominate `(−1,1)^21` by `[−1,1]^21`, transport through `paramsEquivFlat` (MP) to the `Params` box,
    reshape (MP) to the two layer boxes, Tonelli. Mirrors `RouteM4422Hfin` steps 1–3. Axiom-clean.
  - The Schur-shear algebraic heart (THIS file, new — decorrelated-Codex `xhigh` route, sympy-verified):
    `lgammaShear_col_ge` (the per-column SOS bound), `frobSq_lgammaShear_ge` (the `L_γ` Frobenius
    comparability `≥ (1/5)·frobSq`), `rmatMul_angularR_eq` (the exact shear identity `R·A1 = L_γ·[T;Δ·S]`),
    `frobSq_schurNF_eq` (the `‖T‖² ⊕ frobSq(Δ·S)` split), and the combined `frobSq_angularR_ge`
    (`frobSq(R·A1) ≥ (1/5)·(∑T² + frobSq(Δ·S))`, ratios `|γ| ≤ 1`). Axiom-clean.
  - The radial divisor atom (THIS file, new): `radialAxis334_lt_top` — `∫_{[−1,1]} |a|^{8−2c'} < ⊤` for
    `c' < 9/2` (the `r²−1 = 8` blow-up Jacobian; threshold `9/2 > 4`, so never binding). Axiom-clean.
* **Gap (ONE precisely-named `sorry`):** `matBox334_blowup_lt_top` — the `A0` 9-chart radial cover assembly.
  Decompose: (i) cover `matBox 3 3 1 \ {A0=0}` by the `9` max-modulus-entry charts (`argmaxCellOn`/
  `univ_ae_cover` on flattened-A0, `coordZero_null` for the null complement); (ii) per chart, the radial
  c-o-v with Jacobian `|a|^8` (`pivotBlowupOn`/`g5_pivotNode`/`recStep`), the row/col permutation putting
  the pivot at `(0,0)` (frobSq permutation-invariant), the det-1 shear `T = y + β·S`; (iii) apply the banked
  `frobSq_angularR_ge` to lower-bound the integrand by the normal form, Tonelli-separate the radial factor
  (`radialAxis334_lt_top`), and rescale the residual box to feed `resolved334_lt_top`; (iv) `ENNReal.sum_lt_top`
  over the `9` charts (finite subadditivity — ties harmless). The highest-risk step (decorrelated-Codex):
  the radial-chart c-o-v + box-rescale (ii)+(iii). The achiever chart `chartParams334`/`Uval334`
  (`RouteMLayerCoverGEL2`) realises this transport for ONE pivot on the lower-bound side.

## S2-hygiene
The hfin CONCLUSION is S2-FREE. Every banked piece above is `#print axioms`-clean
`[propext, Classical.choice, Quot.sound]` — NO `monomial_rlct`, NO new axiom. The headline currently
carries `sorryAx` (from the lone `matBox334_blowup_lt_top` gap, NOT an axiom); closing the cover makes it
`[propext, Classical.choice, Quot.sound]`.
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

/-! ## The box-radius-`K` resolved-form finiteness (for the per-chart box-enlargement)

The per-chart radial change-of-variables on `(3,3,4)` produces, after the angular `de-shift`
(`Δ = raw − γβ`, the bounded ratios), a residual integral whose `Δ`, `S`, `T` variables range over
boxes ENLARGED beyond `[−1,1]` (`Δ ∈ [−2,2]^{2×2}`, `T ∈ [−3,3]^4`, `S ∈ [−1,1]^{2×4}`). The box-`K`
generalisation of the keystone `resolved334_lt_top`, derived by the SAME S-first transpose-fibre route at
box radius `K` (every underlying brick — `fibre_lintegral_mul_le`, `frobSq22_box_lt_top`,
`core_T_peel_le_ae` — is already box-radius-general). The per-chart bound dominates by this with `K = 3`. -/

/-- The box-`K` per-Δ S-fibre bound (box-radius-general `core334_S_fibre_le`). -/
theorem core334_S_fibre_box_le (K : ℝ) (hK : 0 < K) (c'' : ℝ) (hc0 : 0 < c'') (hc2 : c'' < 2)
    (Δ : Fin 2 → Fin 2 → ℝ) :
    ∫⁻ S in matBox 2 4 K, ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))
      ≤ fibreConst 4 2 2 K c'' * ENNReal.ofReal ((frobSq Δ) ^ (-c'')) := by
  have hrw : ∀ S : Fin 2 → Fin 4 → ℝ,
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))
        = ENNReal.ofReal ((frobSq (rmatMul (matTranspose 2 4 S) (fun k i => Δ i k))) ^ (-c'')) := by
    intro S
    rw [frobSq_rmatMul_transpose Δ S]
    rfl
  rw [setLIntegral_congr_fun (matBox_measurableSet 2 4 K) (fun S _ => hrw S)]
  have hmp := measurePreserving_matTranspose 2 4
  have hpre : matBox 2 4 K = matTranspose 2 4 ⁻¹' matBox 4 2 K := by
    ext S
    simp only [matBox, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h j k; rw [matTranspose_apply]; exact h k j
    · intro h k j; have := h j k; rwa [matTranspose_apply] at this
  rw [hpre,
    hmp.setLIntegral_comp_preimage_emb (matTranspose 2 4).measurableEmbedding
      (fun X => ENNReal.ofReal ((frobSq (rmatMul X (fun k i => Δ i k))) ^ (-c''))) (matBox 4 2 K)]
  have hbound := fibre_lintegral_mul_le (p := 4) (n := 2) (q := 2) (by norm_num) (by norm_num)
    (by norm_num) K hK c'' hc0 (by norm_num; linarith) (fun k i => Δ i k)
  have hfrobT : frobSq (fun k i => Δ i k) = frobSq Δ := by
    unfold frobSq; rw [Finset.sum_comm]
  rwa [hfrobT] at hbound

/-- The box-`K` corank-2 core finiteness (box-radius-general `core334_lt_top`). -/
theorem core334_box_lt_top (K : ℝ) (hK : 0 < K) (c'' : ℝ) (hc0 : 0 ≤ c'') (hc2 : c'' < 2) :
    ∫⁻ Δ in matBox 2 2 K, ∫⁻ S in matBox 2 4 K,
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'')) < ⊤ := by
  rcases eq_or_lt_of_le hc0 with hc0' | hc0'
  · -- c'' = 0: the integrand is (·)^0 = 1, the double integral is vol·vol < ⊤
    have hzero : c'' = 0 := hc0'.symm
    have hone : ∀ (Δ : Fin 2 → Fin 2 → ℝ) (S : Fin 2 → Fin 4 → ℝ),
        ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'')) = 1 := by
      intro Δ S; rw [hzero]; simp [Real.rpow_zero]
    have hvolfin : ∀ p n : ℕ, volume (matBox p n K) < ⊤ := by
      intro p n
      have hcpt : IsCompact (matBox p n K) := by
        have heq : matBox p n K
            = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin n => Set.Icc (-K) K)) := by
          ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
        rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
      exact hcpt.measure_lt_top
    simp only [hone]
    rw [setLIntegral_const]
    refine ENNReal.mul_lt_top ?_ (hvolfin 2 2)
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.one_lt_top (hvolfin 2 4)
  · calc ∫⁻ Δ in matBox 2 2 K, ∫⁻ S in matBox 2 4 K,
            ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))
        ≤ ∫⁻ Δ in matBox 2 2 K, fibreConst 4 2 2 K c'' * ENNReal.ofReal ((frobSq Δ) ^ (-c'')) :=
          lintegral_mono (fun Δ => core334_S_fibre_box_le K hK c'' hc0' hc2 Δ)
      _ = fibreConst 4 2 2 K c'' * ∫⁻ Δ in matBox 2 2 K, ENNReal.ofReal ((frobSq Δ) ^ (-c'')) := by
          rw [lintegral_const_mul' _ _
            (fibreConst_ne_top 4 2 2 K c'' hK (by norm_num; linarith) (by norm_num) (by norm_num))]
      _ < ⊤ := by
          have hcfin := fibreConst_lt_top 4 2 2 K c'' hK (by norm_num; linarith)
            (by norm_num) (by norm_num)
          exact ENNReal.mul_lt_top hcfin (frobSq22_box_lt_top K hK c'' hc2)

/-- **The box-radius-`K` resolved-form finiteness.** `∫_{Δ box K}∫_{S box K}∫_{T box K}
(∑ᵢ Tᵢ² + frobSq(Δ·S))^{−c'} < ⊤` for `2 < c' < 4`, every `K > 0`. The box-radius-general
`resolved334_lt_top`; the per-chart radial change-of-variables feeds this at `K = 3`. -/
theorem resolved334_box_lt_top (K : ℝ) (hK : 0 < K) (c' : ℝ) (hc2 : 2 < c') (hc4 : c' < 4) :
    ∫⁻ Δ in matBox 2 2 K, ∫⁻ S in matBox 2 4 K, ∫⁻ T in morseBox 4 K,
      ENNReal.ofReal ((∑ i, (T i) ^ 2 + frobSq (rmatMul Δ S)) ^ (-c')) < ⊤ := by
  set w : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) → ℝ :=
    fun p => frobSq (rmatMul p.1 p.2) with hwdef
  have hmeasT : Measurable (fun q : ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
      ENNReal.ofReal ((∑ i, (q.2 i) ^ 2 + w q.1) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    show Measurable (fun q : ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
        (∑ i, (q.2 i) ^ 2 + frobSq (rmatMul q.1.1 q.1.2)))
    unfold frobSq rmatMul; fun_prop
  have hstep1 : ∫⁻ Δ in matBox 2 2 K, ∫⁻ S in matBox 2 4 K, ∫⁻ T in morseBox 4 K,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + frobSq (rmatMul Δ S)) ^ (-c'))
      = ∫⁻ p in (matBox 2 2 K ×ˢ matBox 2 4 K), (∫⁻ T in morseBox 4 K,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w p) ^ (-c'))) ∂volume := by
    rw [Measure.volume_eq_prod (Fin 2 → Fin 2 → ℝ) (Fin 2 → Fin 4 → ℝ),
      setLIntegral_prod _ (Measurable.lintegral_prod_right hmeasT).aemeasurable]
  rw [hstep1]
  have hwpos : ∀ᵐ z ∂(volume.restrict (matBox 2 2 K ×ˢ matBox 2 4 K)), 0 < w z :=
    ae_restrict_of_ae frobSq_core334_ne_zero_ae
  have hpeel := core_T_peel_le_ae (m := 3) (volume) c' (by norm_num; linarith) K hK w
    (matBox 2 2 K ×ˢ matBox 2 4 K) hwpos
  refine lt_of_le_of_lt hpeel ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hmeasResid : Measurable
      (fun p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
        ENNReal.ofReal ((w p) ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2))) (by fun_prop)
    show Measurable (fun p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
        frobSq (rmatMul p.1 p.2))
    unfold frobSq rmatMul; fun_prop
  have hresid : (∫⁻ p in (matBox 2 2 K ×ˢ matBox 2 4 K),
        ENNReal.ofReal ((w p) ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2))))
      = ∫⁻ Δ in matBox 2 2 K, ∫⁻ S in matBox 2 4 K,
          ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-(c' - 2))) := by
    rw [Measure.volume_eq_prod (Fin 2 → Fin 2 → ℝ) (Fin 2 → Fin 4 → ℝ),
      setLIntegral_prod _ hmeasResid.aemeasurable]
    refine setLIntegral_congr_fun (matBox_measurableSet 2 2 K) (fun Δ _ => ?_)
    refine setLIntegral_congr_fun (matBox_measurableSet 2 4 K) (fun S _ => ?_)
    rw [hwdef]; norm_num
  rw [hresid]
  exact core334_box_lt_top K hK (c' - 2) (by linarith) (by linarith)

/-! ## The `Params M334` ↔ two-matrix-box reshape (the clean MP plumbing, mirrors `RouteM4422Hfin`)

The connecting plumbing identifying the flat-box integral of `routeMCore M334` with the two-matrix-box
integral `∫_{A0 box}∫_{A1 box} frobSq(A0·A1)^{−c'}`. The flat box `(−1,1)^21` is dominated by the closed
cube `[−1,1]^21`, transported through `paramsEquivFlat` (MP) to the `Params M334` box, then split into
the two per-layer matrix boxes via `eParams334` (an MP `piFinSuccAbove`/`piUnique` reshape) — peeling the
layers in the order `(A0, A1)`. This part is decision-independent (the blow-up bridge is separate). -/

/-- The flat decode `paramsEquivFlat H A (equivFin idx) = A idx.1.1 idx.1.2 idx.2` — a flat coordinate
reads back the layer matrix entry. (Re-derived locally to avoid importing `RouteM4422Hfin`, which would
collide on the `minAdm_M4422` dup; the `arrowCongr'`/`piCurry`/`Sigma.uncurry` unfold.) -/
theorem paramsEquivFlat_decode {L : ℕ} (H : Fin (L + 1) → ℕ) (A : Params H) (idx : FlatIdx H) :
    paramsEquivFlat H A (Fintype.equivFin (FlatIdx H) idx) = A idx.1.1 idx.1.2 idx.2 := by
  unfold paramsEquivFlat
  erw [MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply]
  simp only [MeasurableEquiv.coe_piCurry_symm]
  erw [Equiv.arrowCongr_apply]
  simp only [Function.comp_apply]
  erw [Equiv.symm_apply_apply]
  rfl

/-- `dlnLoss M334 0 A = frobSq (prod M334 A)` (the loss at target `0` is the squared Frobenius norm of
the layer product). -/
theorem dlnLoss_M334_eq_frobSq (A : Params (![3, 3, 4] : Fin 3 → ℕ)) :
    dlnLoss (![3, 3, 4] : Fin 3 → ℕ) 0 A = frobSq (prod (![3, 3, 4] : Fin 3 → ℕ) A) := by
  unfold dlnLoss frobSq
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]

/-- **General `L = 2` layer-product entry form** `(prod M A) i j = ∑ₖ A₀ᵢₖ·A₁ₖⱼ` (re-derived locally;
the same `prodAux` dependent-`Fin`-cast closer as `Case222Algebra.prod_two_layer`). -/
theorem prod_two_layer334 (M : Fin 3 → ℕ) (A : Params M) (i : Fin (M 0)) (j : Fin (M 2)) :
    prod M A i j = ∑ k : Fin (M 1), A 0 i k * A 1 k j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) k using 2

/-- The layer product `prod M334 A` as the raw matrix product `rmatMul (A 0) (A 1)` (entrywise, via
`prod_two_layer334`; `A 0` is `3×3`, `A 1` is `3×4`). -/
theorem prod_M334_eq_rmatMul (A : Params (![3, 3, 4] : Fin 3 → ℕ)) :
    (fun i j => prod (![3, 3, 4] : Fin 3 → ℕ) A i j)
      = rmatMul (fun i k => A 0 i k) (fun k j => A 1 k j) := by
  funext i j
  rw [prod_two_layer334 (![3, 3, 4] : Fin 3 → ℕ) A i j]
  rfl

/-- The `Fin 1` tail family after peeling layer `0` (the layer-`1` fiber). -/
abbrev TailFam334 : Fin 1 → Type :=
  fun s : Fin 1 => Fin ((![3, 3, 4] : Fin 3 → ℕ) ((0 : Fin 2).succAbove s).castSucc) →
    Fin ((![3, 3, 4] : Fin 3 → ℕ) ((0 : Fin 2).succAbove s).succ) → ℝ

/-- **The `Params M334` split into the two layer matrix boxes, in `(A0, A1)` order.** Peel layer `0`
(A0) then collapse the singleton `Fin 1` tail (A1) via `piUnique`. An MP reshape, with components
`(eParams334 A).1 = A 0`, `.2 = A 1` (both definitional). -/
noncomputable def eParams334 :
    Params (![3, 3, 4] : Fin 3 → ℕ) ≃ᵐ (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 4 → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun s : Fin 2 => Fin ((![3, 3, 4] : Fin 3 → ℕ) s.castSucc) →
        Fin ((![3, 3, 4] : Fin 3 → ℕ) s.succ) → ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piUnique TailFam334))

theorem measurePreserving_eParams334 :
    MeasurePreserving eParams334 (volume : Measure (Params (![3, 3, 4] : Fin 3 → ℕ))) volume := by
  unfold eParams334
  refine (volume_preserving_piFinSuccAbove _ 0).trans ?_
  have hp := (MeasurePreserving.id (volume : Measure (Fin 3 → Fin 3 → ℝ))).prod
    (volume_preserving_piUnique TailFam334)
  rw [show (volume : Measure ((Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 4 → ℝ)))
    = volume.prod volume from rfl]
  exact hp

/-- The `Params M334` box: all matrix entries in `[−1,1]` (the image of the closed flat cube box). -/
def paramsBox334 : Set (Params (![3, 3, 4] : Fin 3 → ℕ)) := {A | ∀ s i j, A s i j ∈ Set.Icc (-1 : ℝ) 1}

/-- `eParams334 ⁻¹' (matBox 3 3 1 ×ˢ matBox 3 4 1) = paramsBox334` (the two layer boxes pull back to the
all-entries-bounded `Params` box; `fin_cases` on the layer index). -/
theorem eParams334_preimage_box :
    eParams334 ⁻¹' (matBox 3 3 1 ×ˢ matBox 3 4 1) = paramsBox334 := by
  ext A
  simp only [Set.mem_preimage, Set.mem_prod, matBox, paramsBox334, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, h1⟩ s i j
    fin_cases s
    · exact h0 i j
    · exact h1 i j
  · intro h
    exact ⟨fun i j => h 0 i j, fun i j => h 1 i j⟩

/-- `paramsEquivFlat M334 ⁻¹' (cubeBox 21 1) = paramsBox334` (the closed flat cube box pulls back to the
all-entries-bounded `Params` box; the flat decode ranges over all entries). -/
theorem paramsEquivFlat_preimage_box334 :
    paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ) ⁻¹' (cubeBox (flatDim (![3, 3, 4] : Fin 3 → ℕ)) 1)
      = paramsBox334 := by
  ext A
  simp only [Set.mem_preimage, cubeBox, paramsBox334, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_setOf_eq]
  constructor
  · intro h s i j
    have := h (Fintype.equivFin (FlatIdx (![3, 3, 4] : Fin 3 → ℕ)) ⟨⟨s, i⟩, j⟩)
    rwa [paramsEquivFlat_decode (![3, 3, 4] : Fin 3 → ℕ) A ⟨⟨s, i⟩, j⟩] at this
  · intro h k
    obtain ⟨idx, rfl⟩ := (Fintype.equivFin (FlatIdx (![3, 3, 4] : Fin 3 → ℕ))).surjective k
    rw [paramsEquivFlat_decode (![3, 3, 4] : Fin 3 → ℕ) A idx]
    exact h idx.1.1 idx.1.2 idx.2

theorem measurableSet_paramsBox334 : MeasurableSet paramsBox334 := by
  rw [← paramsEquivFlat_preimage_box334]
  exact ((by rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) :
    MeasurableSet (cubeBox (flatDim (![3, 3, 4] : Fin 3 → ℕ)) 1)).preimage
    (paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ)).measurable

/-- The integrand identity: `frobSq (prod M334 A) = frobSq (rmatMul A0 A1)` read off the `eParams334`
components (`A0, A1` are `(eParams334 A).1, .2`). Via `prod_M334_eq_rmatMul`. -/
theorem frobSq_prod_eq_eParams334 (A : Params (![3, 3, 4] : Fin 3 → ℕ)) :
    frobSq (prod (![3, 3, 4] : Fin 3 → ℕ) A)
      = frobSq (rmatMul (eParams334 A).1 (eParams334 A).2) := by
  change frobSq (prod (![3, 3, 4] : Fin 3 → ℕ) A) = frobSq (rmatMul (A 0) (A 1))
  have h := prod_M334_eq_rmatMul A
  unfold frobSq
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [show prod (![3, 3, 4] : Fin 3 → ℕ) A i j
      = rmatMul (fun i k => A 0 i k) (fun k j => A 1 k j) i j from congrFun (congrFun h i) j]

/-- `routeMCore M334` is nonnegative (the loss is a squared Frobenius norm). -/
theorem routeMCore_M334_nonneg (x : Fin (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) → ℝ) :
    0 ≤ routeMCore (![3, 3, 4] : Fin 3 → ℕ) x := by
  rw [routeMCore, dlnLoss_M334_eq_frobSq]; exact frobSq_nonneg _

/-- **The two-matrix-box reduction (the clean MP plumbing, S2-FREE).** For `0 < c'`,
`∫⁻_{routeMBaseNbhd M334} |routeMCore M334|^{−c'} ≤ ∫⁻_{A0 box}∫_{A1 box} frobSq(A0·A1)^{−c'}`.
Mirrors `RouteM4422Hfin` steps 1–3 (dominate the open box by the closed cube, transport through
`paramsEquivFlat` MP to the `Params` box, reshape through `eParams334` MP to the two matrix boxes,
Tonelli). The blow-up bridge (the corank-2 resolution) is the SEPARATE step bounding the RHS. -/
theorem routeMCore_M334_le_matBox (c' : ℝ) (hc0 : 0 < c') :
    ∫⁻ x in routeMBaseNbhd (![3, 3, 4] : Fin 3 → ℕ),
        ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-c'))
      ≤ ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
          ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c')) := by
  have hopen_sub : flatOpenBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ))
      ⊆ cubeBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) 1 := by
    intro x hx i _
    have := hx i (Set.mem_univ i); rw [Set.mem_Ioo] at this
    rw [Set.mem_Icc]; exact ⟨le_of_lt this.1, le_of_lt this.2⟩
  -- Step 1: |routeMCore| = routeMCore, dominate the open box by the closed cube box.
  have hbound : ∫⁻ x in routeMBaseNbhd (![3, 3, 4] : Fin 3 → ℕ),
        ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-c'))
      ≤ ∫⁻ x in cubeBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) 1,
          ENNReal.ofReal (routeMCore (![3, 3, 4] : Fin 3 → ℕ) x ^ (-c')) := by
    rw [routeMBaseNbhd]
    refine le_trans (lintegral_mono_set hopen_sub) (le_of_eq ?_)
    refine setLIntegral_congr_fun (by
      rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) (fun x _ => ?_)
    rw [abs_of_nonneg (routeMCore_M334_nonneg x)]
  refine le_trans hbound (le_of_eq ?_)
  -- Step 2: transport the closed cube box via paramsEquivFlat (MP) to paramsBox334.
  have hcore : ∀ A : Params (![3, 3, 4] : Fin 3 → ℕ),
      routeMCore (![3, 3, 4] : Fin 3 → ℕ) (paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ) A)
        = frobSq (prod (![3, 3, 4] : Fin 3 → ℕ) A) := by
    intro A
    rw [congrFun (routeMCore_comp_paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ)) A, dlnLoss_M334_eq_frobSq]
  have hmpF := measurePreserving_paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ)
  have hstep2 : ∫⁻ x in cubeBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) 1,
        ENNReal.ofReal (routeMCore (![3, 3, 4] : Fin 3 → ℕ) x ^ (-c'))
      = ∫⁻ A in paramsBox334,
          ENNReal.ofReal (frobSq (prod (![3, 3, 4] : Fin 3 → ℕ) A) ^ (-c')) := by
    have hpre := hmpF.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.measurableEmbedding (paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ)))
      (fun x => ENNReal.ofReal (routeMCore (![3, 3, 4] : Fin 3 → ℕ) x ^ (-c')))
      (cubeBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) 1)
    calc ∫⁻ x in cubeBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) 1,
            ENNReal.ofReal (routeMCore (![3, 3, 4] : Fin 3 → ℕ) x ^ (-c'))
        = ∫⁻ A in (paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ)) ⁻¹'
              cubeBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) 1,
            ENNReal.ofReal (routeMCore (![3, 3, 4] : Fin 3 → ℕ)
              (paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ) A) ^ (-c')) := hpre.symm
      _ = ∫⁻ A in paramsBox334,
            ENNReal.ofReal (frobSq (prod (![3, 3, 4] : Fin 3 → ℕ) A) ^ (-c')) := by
          rw [show (paramsEquivFlat (![3, 3, 4] : Fin 3 → ℕ)) ⁻¹'
              cubeBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) 1 = paramsBox334
            from paramsEquivFlat_preimage_box334]
          refine setLIntegral_congr_fun measurableSet_paramsBox334 (fun A _ => ?_)
          rw [hcore A]
  rw [hstep2]
  -- Step 3: transport paramsBox334 via eParams334 (MP) to the two layer matrix boxes.
  have hmpP := measurePreserving_eParams334
  have hstep3 : ∫⁻ A in paramsBox334,
        ENNReal.ofReal (frobSq (prod (![3, 3, 4] : Fin 3 → ℕ) A) ^ (-c'))
      = ∫⁻ p in (matBox 3 3 1 ×ˢ matBox 3 4 1),
          ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c')) := by
    have hpre := hmpP.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.measurableEmbedding eParams334)
      (fun p : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 4 → ℝ) =>
        ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c')))
      (matBox 3 3 1 ×ˢ matBox 3 4 1)
    calc ∫⁻ A in paramsBox334,
            ENNReal.ofReal (frobSq (prod (![3, 3, 4] : Fin 3 → ℕ) A) ^ (-c'))
        = ∫⁻ A in eParams334 ⁻¹' (matBox 3 3 1 ×ˢ matBox 3 4 1),
            ENNReal.ofReal ((frobSq (rmatMul (eParams334 A).1 (eParams334 A).2)) ^ (-c')) := by
          rw [eParams334_preimage_box]
          refine setLIntegral_congr_fun measurableSet_paramsBox334 (fun A _ => ?_)
          rw [frobSq_prod_eq_eParams334 A]
      _ = ∫⁻ p in (matBox 3 3 1 ×ˢ matBox 3 4 1),
            ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c')) := hpre
  rw [hstep3]
  -- Step 4: Tonelli into the iterated integral ∫_{A0}∫_{A1}.
  have hmeas : Measurable (fun p : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 4 → ℝ) =>
      ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq rmatMul; fun_prop
  rw [Measure.volume_eq_prod (Fin 3 → Fin 3 → ℝ) (Fin 3 → Fin 4 → ℝ),
    setLIntegral_prod _ hmeas.aemeasurable]

/-! ## The Schur-shear algebraic atoms (BANKED sorry-free — the verified heart of the blow-up bridge)

The decorrelated-Codex `xhigh` route's algebraic core, verified exact by sympy (frame-transport cert):
on an `A0` max-modulus-entry chart with pivot `(0,0)`, `A0 = a·R` with `R = [[1,β],[γ,Δ+γβ]]` (`β` 1×2,
`γ` 2×1, `Δ` 2×2, all ratios `|·| ≤ 1`). With `A1 = [y; S]` and the Schur shear `T = y + β·S` (det-1),

    R·A1 = L_γ · [T; Δ·S],   L_γ = [[1,0,0],[γ₀,1,0],[γ₁,0,1]]   (exact, sympy-verified).

`L_γ` is invertible with `det 1`, and on the bounded chart `|γ₀|,|γ₁| ≤ 1` it satisfies the uniform
Frobenius comparability `frobSq(L_γ·M) ≥ (1/5)·frobSq(M)` (smallest singular value `σ_min(L_γ)² ≥ 2−√3 >
1/5`; the column SOS certificate `25·(per-col) = (5γ₀v₀+4v₁)²+(5γ₁v₀+4v₂)²+ (16−5γ₀²−5γ₁²)v₀²` clears at
`γ² ≤ 1`). This is the comparability the per-chart c-o-v rides on. -/

/-- **The `L_γ`-shear column lower bound** (the `nlinarith` atom, verified SOS). For `|g0|,|g1| ≤ 1` and
any `v0 v1 v2`, the squared norm of `L_γ·(v0,v1,v2) = (v0, g0·v0+v1, g1·v0+v2)` dominates `(1/5)·‖v‖²`:

    v0² + (g0·v0 + v1)² + (g1·v0 + v2)² ≥ (1/5)·(v0² + v1² + v2²).

The per-column form of `frobSq(L_γ·M) ≥ (1/5)·frobSq(M)`. -/
theorem lgammaShear_col_ge (g0 g1 v0 v1 v2 : ℝ) (hg0 : g0 ^ 2 ≤ 1) (hg1 : g1 ^ 2 ≤ 1) :
    (1 / 5 : ℝ) * (v0 ^ 2 + v1 ^ 2 + v2 ^ 2)
      ≤ v0 ^ 2 + (g0 * v0 + v1) ^ 2 + (g1 * v0 + v2) ^ 2 := by
  nlinarith [sq_nonneg (5 * g0 * v0 + 4 * v1), sq_nonneg (5 * g1 * v0 + 4 * v2),
    mul_nonneg (sub_nonneg.2 hg0) (sq_nonneg v0), mul_nonneg (sub_nonneg.2 hg1) (sq_nonneg v0),
    sq_nonneg v0]

/-- The `L_γ`-shear matrix `[[1,0,0],[γ₀,1,0],[γ₁,0,1]]` acting on a `3×4` block `M`: row `0` passes
through, row `1 = γ₀·(row 0) + (row 1 of M)`, row `2 = γ₁·(row 0) + (row 2 of M)`. The bounded det-1
left factor that the Schur shear leaves. -/
noncomputable def lgammaShear (g0 g1 : ℝ) (M : Fin 3 → Fin 4 → ℝ) : Fin 3 → Fin 4 → ℝ :=
  fun i j => if i = 0 then M 0 j else if i = 1 then g0 * M 0 j + M 1 j else g1 * M 0 j + M 2 j

/-- **The `L_γ`-shear Frobenius comparability** (BANKED, the verified heart). For `|γ₀|, |γ₁| ≤ 1`,
`frobSq(L_γ·M) ≥ (1/5)·frobSq(M)` — summing the per-column SOS bound `lgammaShear_col_ge` over the `4`
columns. The uniform comparability the per-chart c-o-v consumes (`C = 1/5 < σ_min(L_γ)² = 2−√3`). -/
theorem frobSq_lgammaShear_ge (g0 g1 : ℝ) (hg0 : g0 ^ 2 ≤ 1) (hg1 : g1 ^ 2 ≤ 1)
    (M : Fin 3 → Fin 4 → ℝ) :
    (1 / 5 : ℝ) * frobSq M ≤ frobSq (lgammaShear g0 g1 M) := by
  -- frobSq sums over rows then columns; regroup as a column-sum of the per-column 3-vector norms
  have hrow : ∀ N : Fin 3 → Fin 4 → ℝ, frobSq N = ∑ j : Fin 4, (N 0 j ^ 2 + N 1 j ^ 2 + N 2 j ^ 2) := by
    intro N; unfold frobSq; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_); rw [Fin.sum_univ_three]
  rw [hrow M, hrow (lgammaShear g0 g1 M), Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have h0 : lgammaShear g0 g1 M 0 j = M 0 j := by simp [lgammaShear]
  have h1 : lgammaShear g0 g1 M 1 j = g0 * M 0 j + M 1 j := by simp [lgammaShear]
  have h2 : lgammaShear g0 g1 M 2 j = g1 * M 0 j + M 2 j := by simp [lgammaShear]
  rw [h0, h1, h2]
  exact lgammaShear_col_ge g0 g1 (M 0 j) (M 1 j) (M 2 j) hg0 hg1

/-- The angular matrix `R = [[1,β],[γ,Δ+γβ]]` (`β = (b0,b1)`, `γ = (g0,g1)`, `Δ = (d00,d01,d10,d11)`):
the `pivot-(0,0) = 1` blow-up direction of `A0 = a·R`. Top-left `1`, top row `(1,b0,b1)`, left column
`(1,g0,g1)`, lower-right `Δ + γβ`. -/
noncomputable def angularR (b0 b1 g0 g1 d00 d01 d10 d11 : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i k =>
    !![1, b0, b1;
       g0, d00 + g0 * b0, d01 + g0 * b1;
       g1, d10 + g1 * b0, d11 + g1 * b1] i k

/-- The Schur normal form `[T; Δ·S]` (`3×4`): top row `T = y + β·S` (the spectator row, `y = A1` row 0,
`S = A1` rows 1,2), bottom block `Δ·S` (`2×4`). The `‖T‖² ⊕ frobSq(Δ·S)` shape `resolved334_lt_top`
consumes. -/
noncomputable def schurNF (b0 b1 d00 d01 d10 d11 : ℝ) (A1 : Fin 3 → Fin 4 → ℝ) : Fin 3 → Fin 4 → ℝ :=
  fun i j =>
    if i = 0 then A1 0 j + (b0 * A1 1 j + b1 * A1 2 j)
    else if i = 1 then d00 * A1 1 j + d01 * A1 2 j
    else d10 * A1 1 j + d11 * A1 2 j

/-- **The Schur-shear identity** `R·A1 = L_γ · [T; Δ·S]` (entrywise, sympy-verified exact). The angular
matrix times `A1` equals the bounded `L_γ`-shear of the Schur normal form: row `0 = T = y + β·S`, rows
`1,2 = γ·T + Δ·S`. Pure `ring` per entry (the cross terms `γβ·S` and `β·S` regroup). -/
theorem rmatMul_angularR_eq (b0 b1 g0 g1 d00 d01 d10 d11 : ℝ) (A1 : Fin 3 → Fin 4 → ℝ) :
    rmatMul (angularR b0 b1 g0 g1 d00 d01 d10 d11) A1
      = lgammaShear g0 g1 (schurNF b0 b1 d00 d01 d10 d11 A1) := by
  funext i j
  have hrow : ∀ i : Fin 3, rmatMul (angularR b0 b1 g0 g1 d00 d01 d10 d11) A1 i j
      = lgammaShear g0 g1 (schurNF b0 b1 d00 d01 d10 d11 A1) i j := by
    intro i
    unfold rmatMul angularR lgammaShear schurNF
    rw [Fin.sum_univ_three]
    fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
        Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val', Fin.isValue,
        Fin.mk_zero, Fin.mk_one] <;>
      norm_num [Fin.ext_iff] <;> ring
  exact hrow i

/-- `frobSq (schurNF …) = ∑_j T_j² + frobSq(Δ·S)` — the normal form splits into the spectator row `T`
(`∑_j T_j²`, the `‖T‖²` Morse block) plus the corank-2 core `frobSq(Δ·S)` (rows `1,2`). The split the
disjoint-sum `resolved334_lt_top` integrand reads. -/
theorem frobSq_schurNF_eq (b0 b1 d00 d01 d10 d11 : ℝ) (A1 : Fin 3 → Fin 4 → ℝ) :
    frobSq (schurNF b0 b1 d00 d01 d10 d11 A1)
      = (∑ j, (A1 0 j + (b0 * A1 1 j + b1 * A1 2 j)) ^ 2)
        + frobSq (rmatMul (!![d00, d01; d10, d11] : Matrix (Fin 2) (Fin 2) ℝ)
            (fun k j => A1 (k.succ) j)) := by
  unfold frobSq schurNF rmatMul
  rw [Finset.sum_comm]
  rw [show (∑ j : Fin 4, ∑ i : Fin 3,
        (if i = 0 then A1 0 j + (b0 * A1 1 j + b1 * A1 2 j)
         else if i = 1 then d00 * A1 1 j + d01 * A1 2 j else d10 * A1 1 j + d11 * A1 2 j) ^ 2)
      = ∑ j : Fin 4, ((A1 0 j + (b0 * A1 1 j + b1 * A1 2 j)) ^ 2
          + ((d00 * A1 1 j + d01 * A1 2 j) ^ 2 + (d10 * A1 1 j + d11 * A1 2 j) ^ 2)) from
    Finset.sum_congr rfl (fun j _ => by rw [Fin.sum_univ_three]; simp; ring)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ]

/-- **The per-chart algebraic comparability (BANKED — the combined heart).** On an `A0` max-entry chart
`A0 = a·R` (`R = angularR`, ratios `|γ| ≤ 1`), the product Frobenius square dominates the disjoint-sum
normal form:

    frobSq(R·A1) ≥ (1/5)·(∑_j T_j² + frobSq(Δ·S)),   T = y + β·S.

Compose the shear identity (`rmatMul_angularR_eq`), the `L_γ` comparability (`frobSq_lgammaShear_ge`),
and the normal-form split (`frobSq_schurNF_eq`). The bound the per-chart c-o-v feeds into
`resolved334_lt_top` (after the radial `a²` peel and the box rescale). -/
theorem frobSq_angularR_ge (b0 b1 g0 g1 d00 d01 d10 d11 : ℝ)
    (hg0 : g0 ^ 2 ≤ 1) (hg1 : g1 ^ 2 ≤ 1) (A1 : Fin 3 → Fin 4 → ℝ) :
    (1 / 5 : ℝ) * ((∑ j, (A1 0 j + (b0 * A1 1 j + b1 * A1 2 j)) ^ 2)
        + frobSq (rmatMul (!![d00, d01; d10, d11] : Matrix (Fin 2) (Fin 2) ℝ)
            (fun k j => A1 (k.succ) j)))
      ≤ frobSq (rmatMul (angularR b0 b1 g0 g1 d00 d01 d10 d11) A1) := by
  rw [rmatMul_angularR_eq, ← frobSq_schurNF_eq]
  exact frobSq_lgammaShear_ge g0 g1 hg0 hg1 _

/-- **The `(3,3,4)` radial `a`-axis divisor finiteness** (BANKED, the threshold `9/2` atom). For
`c' < 9/2`, `∫⁻_{[−1,1]} |a|^{8−2c'} < ⊤` — the `r²−1 = 8`-dimensional radial Jacobian divisor of the
`A0 = a·R` blow-up integrates over the pivot axis exactly when `8 − 2c' > −1 ⟺ c' < 9/2`. Since the
threshold is `4 < 9/2`, the `a`-axis is NEVER the binding factor (the corank-2 core's `λ_{2,4} = 2 ⊕ 2`
binds first). The radial factor the per-chart c-o-v Tonelli-separates. -/
theorem radialAxis334_lt_top (c' : ℝ) (hc' : c' < 9 / 2) :
    ∫⁻ a in Set.Icc (-1 : ℝ) 1, ENNReal.ofReal (|a| ^ (8 - 2 * c')) < ⊤ :=
  abs_rpow_lintegral_Icc_lt_top 1 one_pos (8 - 2 * c') (by linarith)

/-- **The exponent-bump pointwise bound.** For `0 < c'` and `c' ≤ c''` (with `0 < c''`), the inverse
power `F^{−c'}` is dominated by `1 + F^{−c''}` for every `F ≥ 0`. (At `F ≥ 1` the `−c'` power is `≤ 1`;
at `0 < F < 1` the larger exponent dominates, `F^{−c'} ≤ F^{−c''}`; at `F = 0` both `rpow`s are `0`.)
The reduction device that lifts the `c' ≤ 2` case of the blow-up bridge onto the `2 < c''` cover. -/
theorem rpow_neg_le_one_add_rpow_neg (F : ℝ) (hF : 0 ≤ F) (c' c'' : ℝ) (hc0 : 0 < c')
    (hle : c' ≤ c'') :
    F ^ (-c') ≤ 1 + F ^ (-c'') := by
  rcases eq_or_lt_of_le hF with hF0 | hF0
  · -- F = 0: 0^{−c'} = 0 ≤ 1 + 0^{−c''}
    rw [← hF0, Real.zero_rpow (by linarith : -c' ≠ 0)]
    have : (0 : ℝ) ≤ (0 : ℝ) ^ (-c'') := Real.rpow_nonneg le_rfl _
    linarith
  · rcases le_or_gt 1 F with hF1 | hF1
    · -- F ≥ 1: F^{−c'} ≤ 1 (base ≥ 1, exponent ≤ 0)
      have h1 : F ^ (-c') ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hF1 (by linarith)
      have h2 : (0 : ℝ) ≤ F ^ (-c'') := Real.rpow_nonneg hF _
      linarith
    · -- 0 < F < 1: F^{−c'} ≤ F^{−c''} (base ≤ 1, smaller-magnitude negative exponent)
      have h1 : F ^ (-c') ≤ F ^ (-c'') :=
        Real.rpow_le_rpow_of_exponent_ge hF0 (le_of_lt hF1) (by linarith)
      linarith

/-! ## The blow-up bridge (the ONE remaining gap — the `A0` radial-chart cover)

`∫_{A0 box}∫_{A1 box} frobSq(A0·A1)^{−c'} < ⊤` for `0 < c' < 4`. The corank-2 resolution: the pure
fibre route caps at `3r/2 ≤ 3/2 ≪ 4` (the rank-`r` fibre threshold), so a Jacobian-weighted blow-up
is genuinely forced (no MP global reparametrization lands the normal form — decorrelated-Codex
confirmed). The route (frame-transport cert §"A0 radial chart", decorrelated-Codex `xhigh`):

- Cover `{A0 ≠ 0}` by the `9` max-modulus-entry charts of `A0` (`{A0 ≠ 0}` complement null); on the
  chart with pivot `(i,j)`, write `A0 = a·R` (`a = A0ᵢⱼ`, `R` the bounded angular matrix, `Rᵢⱼ = 1`).
  Radial Jacobian `|a|^{9−1} = |a|^8`.
- After a (det-1) row/column permutation putting the pivot at `(0,0)` and the Schur shear `T = y + β·S`
  on `A1`'s top row (Jacobian `1`), `R·A1 = L_γ · [T; Δ·S]` with `L_γ = [[1,0],[γ,I]]` bounded on the
  chart. So `frobSq(A0·A1) = a²·frobSq(R·A1) ≥ C·a²·(‖T‖² + frobSq(Δ·S))` (uniform Frobenius
  comparability, `γ` bounded).
- The chart contribution `≤ (∫ |a|^{8−2c'} da) · (∫ (‖T‖² + frobSq(Δ·S))^{−c'} dT dS dΔ)` — the `a`-axis
  finite for `c' < 9/2` (so for `c' < 4`), the residual `= resolved334_lt_top` (a scaled-box rescale).
  Finite subadditivity over the `9` charts (NOT a disjoint partition — ties harmless).

GAP (`sorry`): this `A0` radial-chart cover. Highest-risk step (decorrelated-Codex): the radial-chart
c-o-v on the max-entry cells (cover-up-to-null, injectivity off `{a = 0}`, Jacobian `|a|^8`, the sheared
target boxes → enlarged boxes consumable by a scaled `resolved334_lt_top`). Everything DOWNSTREAM of the
RHS (`resolved334_lt_top` + the T-peel + the core resolution + the null set) is BANKED sorry-free; the
clean MP plumbing (`routeMCore_M334_le_matBox`) reducing the headline to THIS is banked sorry-free too. -/
/-- The flat-A0 cover integrand: `gFlat334 c' y = ∫_{A1∈box} frobSq(rmatMul ((matToFlatEquiv 3 3).symm y) A1)^{−c'}`,
the (A1-integrated) `A0`-integrand reindexed by the `Fin 9` flatten. The `g` of `recStep` on `Fin 9`. -/
noncomputable def gFlat334 (c' : ℝ) (y : Fin 9 → ℝ) : ℝ≥0∞ :=
  ∫⁻ A1 in matBox 3 4 1,
    ENNReal.ofReal ((frobSq (rmatMul ((matToFlatEquiv 3 3).symm y) A1)) ^ (-c'))

/-- The flattened A0-box `matToFlatEquiv 3 3 '' (matBox 3 3 1) = {y | ∀ i, |y i| ≤ 1}` as a flat set;
equivalently the preimage under `.symm`. The cover domain on the `Fin 9` carrier. -/
def flatBox334 : Set (Fin 9 → ℝ) := {y | ∀ i, y i ∈ Set.Icc (-1 : ℝ) 1}

theorem flatBox334_measurableSet : MeasurableSet flatBox334 := by
  rw [flatBox334, Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) measurableSet_Icc)

/-- **The flat-box correspondence (GAP — the `matToFlatEquiv` coordinate read).** The matrix box
`matBox 3 3 1` is the `matToFlatEquiv 3 3`-preimage of the flat box `flatBox334`. Both are `[−1,1]^9`,
differing only by the entry↔`Fin 9` reindex (`piCurry`/`arrowCongr'`); the box predicate `∀ entry, |·|≤1`
is preserved coordinatewise. SKELETON (`sorry`) — the `matToFlatEquiv` per-coordinate unfolding. -/
theorem matBox334_flatBox_preimage :
    matBox 3 3 1 = (matToFlatEquiv 3 3) ⁻¹' flatBox334 := by
  ext A0
  simp only [matBox, flatBox334, Set.mem_setOf_eq, Set.mem_preimage]
  -- `(matToFlatEquiv 3 3 A0) i = A0 (e.symm i).1 (e.symm i).2`; reindex the `∀ i` by the bijection `e`.
  set e : (Σ _ : Fin 3, Fin 3) ≃ Fin 9 :=
    (Equiv.sigmaEquivProd (Fin 3) (Fin 3)).trans finProdFinEquiv with he
  have hcoord : ∀ i : Fin 9, (matToFlatEquiv 3 3 A0) i = A0 (e.symm i).1 (e.symm i).2 := fun i => rfl
  constructor
  · intro h i
    rw [hcoord i]; exact h (e.symm i).1 (e.symm i).2
  · intro h k j
    have := h (e ⟨k, j⟩)
    rw [hcoord (e ⟨k, j⟩), Equiv.symm_apply_apply] at this
    exact this

/-- The A0-outer integral reindexes to the flat `gFlat334` integral over `flatBox334`
(via `measurePreserving_matToFlatEquiv` + `matBox334_flatBox_preimage`). -/
theorem matBox334_outer_flat (c' : ℝ) :
    ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
        ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c'))
      = ∫⁻ y in flatBox334, gFlat334 c' y := by
  have hmp := measurePreserving_matToFlatEquiv 3 3
  have hcomp := hmp.setLIntegral_comp_preimage_emb (matToFlatEquiv 3 3).measurableEmbedding
    (gFlat334 c') flatBox334
  rw [matBox334_flatBox_preimage, ← hcomp]
  refine setLIntegral_congr_fun
    ((matToFlatEquiv 3 3).measurable flatBox334_measurableSet)
    (fun A0 _ => ?_)
  rw [gFlat334, MeasurableEquiv.symm_apply_apply]

/-- **The indicator decoupling (PROVED — the key chart simplification).** On the chart domain
`chartDomOn univ p` (the ratios `|y_k| ≤ 1`, `k ≠ p`), the blown-up point lands in the flat box
`flatBox334` IFF the radial coordinate `|y p| ≤ 1`: the off-pivot blown-up entries are `y p · y_k` with
`|y_k| ≤ 1`, so `|y p · y_k| ≤ |y p|`, and the pivot entry is `y p` itself. So the box indicator depends
ONLY on `|y p|` — decoupling the radial axis from the 8 ratios (the step that lets Tonelli separate them).
Decorrelated-Codex confirmed SOUND (thread 29 `codex/chart-answer.md` VET-1). -/
theorem flatBox334_blowup_mem_iff (p : Fin 9) (y : Fin 9 → ℝ)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin 9)) p) :
    pivotBlowupOn (Finset.univ : Finset (Fin 9)) p y ∈ flatBox334 ↔ |y p| ≤ 1 := by
  unfold flatBox334 chartDomOn at *
  simp only [Set.mem_setOf_eq] at *
  constructor
  · intro h
    have hpp := h p
    rw [pivotBlowupOn] at hpp
    simp only [Set.mem_Icc] at hpp
    rw [abs_le]; exact hpp
  · intro hp i
    rw [pivotBlowupOn]
    by_cases hi : i = p
    · subst hi; simp only [if_pos rfl, Set.mem_Icc]; rw [abs_le] at hp; exact hp
    · simp only [if_neg hi, Finset.mem_univ, if_true, Set.mem_Icc]
      have hyi : |y i| ≤ 1 := hy i (Finset.mem_univ i) hi
      have hb : |y p * y i| ≤ |y p| := by
        rw [abs_mul]; nlinarith [abs_nonneg (y p), abs_nonneg (y i)]
      have hbb : |y p * y i| ≤ 1 := le_trans hb hp
      rw [abs_le] at hbb; exact hbb

/-- The unflattened angular matrix on chart `p`: `Rmat334 p y` is the `3×3` matrix with `R_p = 1` and
`R_k = y_k` (`k ≠ p`), the bounded direction of the radial blow-up `A0 = (y p)·R`. -/
noncomputable def Rmat334 (p : Fin 9) (y : Fin 9 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  (matToFlatEquiv 3 3).symm (fun i => if i = p then 1 else y i)

/-- **The radial pull-out (PROVED — the homogeneity step).** `gFlat334 c'` of the pivot blow-up factors
the radial scale `a = y p` out of the loss with degree `2` (`radialDelta_loss_factor`): the blown-up flat
A0 unflattens to `(y p) • (Rmat334 p y)`, so
`gFlat334 c' (blowup) = ∫_{A1} ofReal(((y p)²·frobSq(Rmat334·A1))^{−c'})`. The form the radial-axis Tonelli
separation consumes (the `|y p|^{−2c'}` then pulls cleanly out, leaving the bounded `Rmat334`). -/
theorem gFlat334_blowup_radial (c' : ℝ) (p : Fin 9) (y : Fin 9 → ℝ) :
    gFlat334 c' (pivotBlowupOn (Finset.univ : Finset (Fin 9)) p y)
      = ∫⁻ A1 in matBox 3 4 1,
          ENNReal.ofReal (((y p) ^ 2 * frobSq (rmatMul (Rmat334 p y) A1)) ^ (-c')) := by
  unfold gFlat334 Rmat334
  refine lintegral_congr (fun A1 => ?_)
  congr 1
  have hbl : (matToFlatEquiv 3 3).symm (pivotBlowupOn (Finset.univ : Finset (Fin 9)) p y)
      = fun r c => (y p) * ((matToFlatEquiv 3 3).symm (fun i => if i = p then 1 else y i)) r c := by
    funext r c
    show (matToFlatEquiv 3 3).symm (pivotBlowupOn (Finset.univ : Finset (Fin 9)) p y) r c = _
    rw [show pivotBlowupOn (Finset.univ : Finset (Fin 9)) p y
        = (fun i => (y p) * (if i = p then 1 else y i)) from by
      funext i; unfold pivotBlowupOn; by_cases hi : i = p <;> simp [hi]]
    rfl
  rw [hbl, radialDelta_loss_factor (y p)
    ((matToFlatEquiv 3 3).symm (fun i => if i = p then 1 else y i)) A1]

/-- **The per-chart finiteness (GAP — the genuine radial transport).** For each A0-entry pivot
`p : Fin 9`, the radial-blow-up chart integral — the pivot-blow-up `pivotBlowupOn univ p` of the flat A0
(Jacobian `|y p|^8`), against the full A1 box — is finite for `2 < c' < 4`. The content: on chart `p`,
`A0 = a·R` (`a = y p`, `R` the bounded angular matrix, `R_p = 1`); `frobSq(A0·A1) = a²·frobSq(R·A1)`
(`radialDelta_loss_factor`); the per-pivot normalisation to `(0,0)` (row/col permute A0, the induced
A1-row permute is measure-preserving on the symmetric box) + `frobSq_angularR_ge` lower-bounds
`frobSq(R·A1) ≥ (1/5)(‖T‖² + frobSq(Δ·S))`; Tonelli-separate the radial `|a|^{8−2c'}` axis
(`radialAxis334_lt_top`, finite since `c' < 4 < 9/2`); the residual `(‖T‖²+frobSq(Δ·S))^{−c'}` over the
box-enlarged `(Δ∈[−2,2], S∈[−1,1], T∈[−3,3])` domain feeds `resolved334_box_lt_top 3`. SKELETON (`sorry`)
— the radial change-of-variables + per-pivot permutation + box-enlarged rescale (the long pole). -/
theorem matBox334_chart_lt_top (c' : ℝ) (hc2 : 2 < c') (hc4 : c' < 4) (p : Fin 9) :
    ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin 9)) p \ pivotZeroOn p,
        ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin 9)) p y).det|
          * flatBox334.indicator (gFlat334 c') (pivotBlowupOn (Finset.univ : Finset (Fin 9)) p y)
      < ⊤ := by
  -- the Jacobian determinant is `|y p|^8` (`pivotBlowupOnDeriv_det`, `univ.card = 9`).
  have hdet : ∀ y : Fin 9 → ℝ,
      |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin 9)) p y).det| = |y p| ^ 8 := by
    intro y
    rw [pivotBlowupOnDeriv_det (Finset.univ : Finset (Fin 9)) p (Finset.mem_univ p) y]
    simp [abs_pow]
  simp only [hdet]
  -- REMAINING GAP (the genuine measure-theoretic long pole, sharply scoped to this chart integral).
  -- The structural facts are established (det `|y p|^8` above; `pivotBlowupOn univ p y` unflattens to
  -- the radial scaling `(y p) • R` with `R_p = 1`, `R_k = y_k`, by `rfl`; `frobSq((y p)•R · A1) =
  -- (y p)²·frobSq(R·A1)` by `radialDelta_loss_factor`). The remaining content:
  -- (KEY decoupling) on `chartDomOn univ p` the ratios `|y_k| ≤ 1` (k≠p), so the blown-up off-pivot
  --   entries `|y p · y_k| ≤ |y p|`; hence `flatBox334 (blowup) ⟺ |y p| ≤ 1` — the indicator decouples
  --   to the pure radial constraint, separating the `y p` axis from the ratios with NO coupling.
  -- (i) reindex `Fin 9 ≃ ℝ × (Fin 8 → ℝ)` (pivot axis × ratios), Tonelli-separate the radial factor
  --   `|y p|^{8−2c'}` (finite for `c' < 9/2`, `radialAxis334_lt_top`) from the ratio/A1 residual;
  -- (ii) the per-pivot row/col permutation to `(0,0)` (the induced A1-row permute is MP on the
  --   symmetric A1-box) + `frobSq_angularR_ge` lower-bounds `frobSq(R·A1) ≥ (1/5)(‖T‖²+frobSq(Δ·S))`,
  --   box-enlarged (`Δ∈[−2,2]`, `T∈[−3,3]`, the de-shift `d = raw − γβ`) to feed `resolved334_box_lt_top 3`.
  sorry

/-- **The blow-up bridge, the `2 < c'` core.** `∫_{A0 box}∫_{A1 box} frobSq(A0·A1)^{−c'} < ⊤` for
`2 < c' < 4`. The full `0 < c' < 4` statement reduces to this via the exponent-bump
(`matBox334_blowup_lt_top`). The 9-chart A0-entry radial cover assembly: flatten A0 (`matToFlatEquiv 3 3`,
MP), cover the inner `A0`-integral by the 9 max-modulus-entry charts (`recStep` on `univ : Finset (Fin 9)`,
folding the box indicator), each chart finite (`matBox334_chart_lt_top`), summed by `ENNReal.sum_lt_top`.
The cover-to-sum is proven here; the per-chart finiteness is the named transport gap. -/
theorem matBox334_blowup_lt_top_gt2 (c' : ℝ) (hc2 : 2 < c') (hc4 : c' < 4) :
    ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
      ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c')) < ⊤ := by
  -- Reindex A0 to the flat `Fin 9` carrier (MP), then `recStep` (univ argmax-cover) splits the
  -- A0-integral into the 9 max-modulus-entry chart sum; each chart is finite, summed by `sum_lt_top`.
  rw [matBox334_outer_flat c']
  rw [recStep (Finset.univ : Finset (Fin 9)) 0 (Finset.mem_univ 0)
      flatBox334 flatBox334_measurableSet (gFlat334 c')]
  exact ENNReal.sum_lt_top.2 (fun p _ => matBox334_chart_lt_top c' hc2 hc4 p)

theorem matBox334_blowup_lt_top (c' : ℝ) (hc0 : 0 < c') (hc4 : c' < 4) :
    ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
      ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c')) < ⊤ := by
  rcases le_or_gt c' 2 with hc2 | hc2
  · -- 0 < c' ≤ 2: bump the exponent to c'' = 3 ∈ (2,4) by the pointwise `F^{−c'} ≤ 1 + F^{−3}` bound.
    -- ∫∫ F^{−c'} ≤ ∫∫ 1 + ∫∫ F^{−3} = vol·vol + (the 2<c'' cover) < ⊤.
    have hbump : ∀ (A0 : Fin 3 → Fin 3 → ℝ) (A1 : Fin 3 → Fin 4 → ℝ),
        ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c'))
        ≤ 1 + ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ))) := by
      intro A0 A1
      have h := rpow_neg_le_one_add_rpow_neg (frobSq (rmatMul A0 A1)) (frobSq_nonneg _) c' 3 hc0
        (by linarith)
      calc ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c'))
          ≤ ENNReal.ofReal (1 + (frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ))) := ENNReal.ofReal_le_ofReal h
        _ = 1 + ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ))) := by
            rw [ENNReal.ofReal_add (by norm_num) (Real.rpow_nonneg (frobSq_nonneg _) _),
              ENNReal.ofReal_one]
    -- the c'' = 3 cover
    have hcover3 := matBox334_blowup_lt_top_gt2 3 (by norm_num) (by norm_num)
    -- the constant-1 integral over the two boxes
    have hvolfin : ∀ p n : ℕ, volume (matBox p n 1) < ⊤ := by
      intro p n
      have hcpt : IsCompact (matBox p n (1 : ℝ)) := by
        have heq : matBox p n (1 : ℝ)
            = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) := by
          ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
        rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
      exact hcpt.measure_lt_top
    have hvol : ∫⁻ _A0 in matBox 3 3 1, ∫⁻ _A1 in matBox 3 4 1, (1 : ℝ≥0∞) < ⊤ := by
      rw [setLIntegral_const, setLIntegral_const]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.one_lt_top (hvolfin 3 4)) (hvolfin 3 3)
    -- the c'' = 3 inner-integral measurability (for `lintegral_add`)
    have hmeas3 : ∀ A0 : Fin 3 → Fin 3 → ℝ, Measurable (fun A1 : Fin 3 → Fin 4 → ℝ =>
        ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ)))) := by
      intro A0
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.comp (g := fun t : ℝ => t ^ (-(3 : ℝ))) (by fun_prop)
      unfold frobSq rmatMul; fun_prop
    -- combine
    calc ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
            ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c'))
        ≤ ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
            (1 + ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ)))) :=
          lintegral_mono fun A0 => lintegral_mono fun A1 => hbump A0 A1
      _ = (∫⁻ _A0 in matBox 3 3 1, ∫⁻ _A1 in matBox 3 4 1, (1 : ℝ≥0∞))
            + ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
                ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ))) := by
          rw [← lintegral_add_left' (by
            exact (Measurable.lintegral_prod_right (measurable_const)).aemeasurable) _]
          refine setLIntegral_congr_fun (matBox_measurableSet 3 3 1) (fun A0 _ => ?_)
          rw [← lintegral_add_left' (measurable_const).aemeasurable]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hvol, hcover3⟩
  · exact matBox334_blowup_lt_top_gt2 c' hc2 hc4

/-- **The `(3,3,4)` hfin upper bound (the N4 depth-2 instance, GAP = the blow-up bridge ONLY).** For
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
  rcases eq_or_lt_of_le (c'.2 : (0 : ℝ) ≤ (c' : ℝ)) with hc0 | hc0
  · -- c' = 0: integrand is (·)^0 = 1, integral = volume(box) < ⊤.
    have hzero : (c' : ℝ) = 0 := hc0.symm
    have hone : ∀ x, ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ))) = 1 := by
      intro x; rw [hzero]; simp [Real.rpow_zero]
    simp only [hone]
    rw [setLIntegral_const]
    refine ENNReal.mul_lt_top ENNReal.one_lt_top ?_
    rw [routeMBaseNbhd]
    have hopen_sub : flatOpenBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ))
        ⊆ cubeBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) 1 := by
      intro x hx i _
      have := hx i (Set.mem_univ i); rw [Set.mem_Ioo] at this
      rw [Set.mem_Icc]; exact ⟨le_of_lt this.1, le_of_lt this.2⟩
    refine lt_of_le_of_lt (measure_mono hopen_sub) ?_
    exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top
  · -- 0 < c' < 4: reduce to the two-matrix-box integral, then the blow-up bridge.
    exact lt_of_le_of_lt (routeMCore_M334_le_matBox (c' : ℝ) hc0)
      (matBox334_blowup_lt_top (c' : ℝ) hc0 hc4)

end DLNFibre.DLN.RLCT
