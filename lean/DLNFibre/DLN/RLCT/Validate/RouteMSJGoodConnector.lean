import DLNFibre.DLN.RLCT.Validate.RouteMSJBaseHyp
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagCore
import DLNFibre.DLN.RLCT.Validate.RouteMSJFreedPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSJShellCharge
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagShell

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJGoodConnector` — hole (d), the good-case cover connector

**Thread `genm-sj5-good` (aoyagi-full Stage 2).** The content of `RouteMSJDecoratedStep`'s hole (d)
`deeperFlagGood_finite`, built as standalone lemmas in a NEW module (the controller wires the hole to
`deeperFlagGood_finite_impl` at rendezvous — this module does NOT import `RouteMSJDecoratedStep`, so it
sits BELOW it; no import cycle).

## The reduction (good chain `M`, arity ≥ 3, admissible `D`)

For a GOOD chain (`deepTailMin M ≤ M 1`, delivered here as the per-cut pivot source
`hgoodpiv : ∀ u, minAdm (redChain u M) ≤ u * tailMinWidth M`) and an `adm`-admissible `D`, show `D` is
finite below `carrierThreshold M`. The chain (mirroring `#4`'s width-2 base
`decoratedBase_routeA_of_leafForm_prod`, but with a VARYING deep tail):

1. **Dispatch** `FaithfulSJAt D`: `d = 0` (observable, `decLoss = frobSq (prod M (e z))`) vs `d ≥ 1`
   (the route-A leaf form `decLoss = commonDivisor(u)² · frobSq (Γ · prod (dropHead M) r)`).
2. **`a = M 0`** (the front-block dimension of the `d ≥ 1` γ' clause equals `M 0`) — DERIVED, no `adm`
   change, via `a_eq_M0_of_domEq`: `genuineCarrier`'s MP `e : D.Z ≃ᵐ Params M` and γ''s MP
   `eΓ : D.Z ≃ᵐ (Fin a → Fin M₁) × Params (dropHead M)` are BOTH measure-preserving on `D.dom`, so
   `volume (matBox M₀ M₁ 1) = volume (matBox a M₁ 1)` (cancelling the shared deep-tail box), and
   `matBox_vol1` (`= 2^{p·q}`, strictly monotone in `p·q`) forces `M₀·M₁ = a·M₁ ⟹ a = M₀`.
3. **Tonelli-separate** (as `#4`): `D.integral c' = (∫ monomial) · routeMLayerBoxIntegral M c' 1`; the
   monomial factor is finite below `monomialThreshold` (the β clause).
4. **Cover** (`routeMBox_le_shellSum`, the genuinely-new content): the box integral is bounded by the
   finite sum, over shells `j` and pivot columns `κ`, of the deeper-cut spine integrands
   `shellSpineIntegrand M (t★+j) κ ε r j c'` (`t★ = bindingCut M`, `r = min (M₀−t★) (M₁−t★)`). This is
   the decorated/deeper-cut analogue of `sjBoundaryPeel`: shell-stratify the outer tail
   (`offSector_cover_le`) + per-shell re-peel of the front factor at the deeper cut `t★+j`
   (`gammaPeelIntegral_schurShearFree_eq` restricted to the shell, pivot-cover at depth `t★+j`).
5. Each `shellSpineIntegrand M (t★+j) κ ε r j c' < ⊤` via the sibling holes (a)
   `deeperFlagStrictShell_finite` (`j < r`) / (b) `deeperFlagSaturatedShell_finite` (`j = r`),
   consumed here as hypotheses (WITH the `hcT : c' < carrierThreshold M` clause the controller is
   adding); `ENNReal.sum_lt_top` closes.

## Status

`a_eq_M0_of_domEq` is FILLED (the load-bearing soundness lemma — treated as canonical, axiom-clean).
`routeMBox_le_shellSum` (the cover) and `deeperFlagGood_finite_impl` (the assembly) are stated with
`sorry`, pending the controller's design sanity-check on the cover before deep-fill.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## Box-volume helpers (for the `a = M 0` derivation) -/

/-- **`volume (matBox p q 1) = 2^{p·q}`** — the entries range over `Icc (-1) 1` (side `2`), so the
volume is `(ofReal 2)^{p·q}`, strictly monotone in `p·q`. Nested `volume_pi_pi` + `Real.volume_Icc`. -/
private theorem matBox_vol1 (p q : ℕ) :
    volume (matBox p q 1) = ENNReal.ofReal 2 ^ (p * q) := by
  have hset : matBox p q 1
      = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin q => Set.Icc (-1 : ℝ) 1)) := by
    ext X
    simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [hset, MeasureTheory.volume_pi_pi]
  have hinner : ∀ _i : Fin p,
      volume (Set.univ.pi (fun _ : Fin q => Set.Icc (-1 : ℝ) 1)) = ENNReal.ofReal 2 ^ q := by
    intro _
    rw [MeasureTheory.volume_pi_pi]
    simp only [Real.volume_Icc]
    rw [show (1 : ℝ) - -1 = 2 by ring, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_congr rfl (fun i _ => hinner i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm]

/-- **`volume (paramsBoxM M' 1) = volume (cubeBox (flatDim M') 1)`** — the measure-preserving flatten
`paramsEquivFlat` sends the (dependent) params box to the flat single-level cube box (whose volume is a
plain single-level `volume_pi_pi`). Sidesteps the dependent-pi `volume_pi_pi` on `Params`. -/
private theorem paramsBoxM_vol_eq_cube {L' : ℕ} (M' : Fin (L' + 1) → ℕ) :
    volume (paramsBoxM M' 1) = volume (cubeBox (flatDim M') 1) := by
  have hcubeMeas : MeasurableSet (cubeBox (flatDim M') 1) := by
    rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  rw [← paramsEquivFlat_preimage_paramsBoxM M' 1]
  exact (measurePreserving_paramsEquivFlat M').measure_preimage hcubeMeas.nullMeasurableSet

/-- **`volume (paramsBoxM M' 1) ≠ ⊤`** — a bounded box, finite volume (via the flat cube). -/
private theorem paramsBoxM_vol_ne_top {L' : ℕ} (M' : Fin (L' + 1) → ℕ) :
    volume (paramsBoxM M' 1) ≠ ⊤ := by
  rw [paramsBoxM_vol_eq_cube, cubeBox, volume_pi_pi]
  refine ENNReal.prod_ne_top (fun i _ => ?_)
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

/-- **`volume (paramsBoxM M' 1) ≠ 0`** — positive volume (each `Icc (-1) 1` has length 2). -/
private theorem paramsBoxM_vol_ne_zero {L' : ℕ} (M' : Fin (L' + 1) → ℕ) :
    volume (paramsBoxM M' 1) ≠ 0 := by
  rw [paramsBoxM_vol_eq_cube, cubeBox, volume_pi_pi, Finset.prod_ne_zero_iff]
  intro i _; rw [Real.volume_Icc]; simp

/-! ## The `a = M 0` derivation (soundness linchpin — DERIVE route, no `adm` change) -/

/-- **The front-block dimension `a` equals `M 0`** (soundness linchpin). Given both measure-preserving
domain parametrizations — `genuineCarrier`'s `e : D.Z ≃ᵐ Params M` (with `dom = e⁻¹(paramsBoxM M 1)`) and
γ''s `eΓ : D.Z ≃ᵐ (Fin a → Fin M₁) × Params (dropHead M)` (with `dom = eΓ⁻¹(matBox a M₁ 1 ×ˢ box)`) — the
domain volume computed two ways forces `volume (matBox M₀ M₁ 1) = volume (matBox a M₁ 1)`, hence (via
`matBox_vol1 = 2^{·}`, strictly monotone) `M₀·M₁ = a·M₁`, hence `a = M₀` (`M₁ ≥ 1`). No cardinality/ι≃ν
tie is used; no `adm` clause is added. -/
theorem a_eq_M0_of_domEq {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (hM1 : 1 ≤ M 1)
    {Z : Type} [MeasureSpace Z] (a : ℕ) (dom : Set Z)
    (e : Z ≃ᵐ Params M) (he : MeasurePreserving e)
    (hdome : dom = ⇑e ⁻¹' (paramsBoxM M 1))
    (eΓ : Z ≃ᵐ (Fin a → Fin (M 1) → ℝ) × Params (dropHead M)) (heΓ : MeasurePreserving eΓ)
    (hdomΓ : dom = ⇑eΓ ⁻¹' (matBox a (M 1) 1 ×ˢ paramsBoxM (dropHead M) 1)) :
    a = M 0 := by
  have hVne0 : volume (paramsBoxM (dropHead M) 1) ≠ 0 := paramsBoxM_vol_ne_zero _
  have hVtop : volume (paramsBoxM (dropHead M) 1) ≠ ⊤ := paramsBoxM_vol_ne_top _
  -- volume dom via `e` + the banked front-split `eFront` (tail box = `paramsBoxM (dropHead M) 1`).
  have htd : tailChain M = dropHead M := rfl
  have h1 : volume dom
      = volume (matBox (M 0) (M 1) 1) * volume (paramsBoxM (dropHead M) 1) := by
    rw [hdome, he.measure_preimage_equiv, ← eFront_preimage_box M,
      (measurePreserving_eFront M).measure_preimage_equiv, Measure.volume_eq_prod,
      Measure.prod_prod, htd]
  -- volume dom via `eΓ`.
  have h2 : volume dom
      = volume (matBox a (M 1) 1) * volume (paramsBoxM (dropHead M) 1) := by
    rw [hdomΓ, heΓ.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]
  have hmain : volume (matBox (M 0) (M 1) 1) * volume (paramsBoxM (dropHead M) 1)
      = volume (matBox a (M 1) 1) * volume (paramsBoxM (dropHead M) 1) := h1.symm.trans h2
  have hmateq : volume (matBox (M 0) (M 1) 1) = volume (matBox a (M 1) 1) :=
    (ENNReal.mul_left_inj hVne0 hVtop).mp hmain
  rw [matBox_vol1, matBox_vol1, ENNReal.ofReal_ofNat] at hmateq
  -- `(2:ℝ≥0∞)^{M₀·M₁} = 2^{a·M₁}` → `M₀·M₁ = a·M₁` (via `ℕ` cast + `Nat.pow_right_injective`).
  have hnatcast : ((2 : ℕ) ^ (M 0 * M 1) : ℝ≥0∞) = ((2 : ℕ) ^ (a * M 1) : ℝ≥0∞) := by
    push_cast
    exact hmateq
  have hnat : (2 : ℕ) ^ (M 0 * M 1) = (2 : ℕ) ^ (a * M 1) := by exact_mod_cast hnatcast
  have hmul : M 0 * M 1 = a * M 1 := Nat.pow_right_injective (le_refl 2) hnat
  exact (Nat.eq_of_mul_eq_mul_right (by omega : 0 < M 1) hmul).symm

/-! ## SNAG-D — the general-depth determinantal null (`rank ≥ t` a.e. for `t ≤ min m n`) -/

/-- **`t ≤ rank A₀` a.e. for `t ≤ m` and `t ≤ n`** (the general-depth analogue of the `{rank = 0}`-null
in `frontBox_pivotCover_le`). The deficient set `{A₀ | rank A₀ < t}` is contained in the zero set of ONE
fixed `t×t` minor (`Core.submatrix_det_eq_zero_of_rank_le`); that minor is `eval A₀ P` for a nonzero
polynomial `P` (nonzero via the identity witness on the `castLE` minor), whose zero set is Lebesgue-null
(`ae_matrix_eval_ne_zero`). Used to upgrade the pivot-chart cover of the front factor from `{t ≤ rank}` to
the full box: `∫_{matBox} = ∫_{matBox ∩ {t ≤ rank}}`. -/
theorem rank_ge_ae {m n t : ℕ} (htm : t ≤ m) (htn : t ≤ n) :
    ∀ᵐ A : Fin m → Fin n → ℝ, t ≤ (Matrix.of A).rank := by
  classical
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · subst ht0; filter_upwards with A; exact Nat.zero_le _
  obtain ⟨c, rfl⟩ : ∃ c, t = c + 1 := ⟨t - 1, by omega⟩
  set ρ₀ : Fin (c + 1) ↪ Fin m := Fin.castLEEmb htm with hρ₀
  set κ₀ : Fin (c + 1) ↪ Fin n := Fin.castLEEmb htn with hκ₀
  set Agen : Matrix (Fin m) (Fin n) (MvPolynomial (Fin m × Fin n) ℝ) :=
    Matrix.of (fun i j => MvPolynomial.X (i, j)) with hAgen
  set P : MvPolynomial (Fin m × Fin n) ℝ := (Agen.submatrix ρ₀ κ₀).det with hP
  -- encoding: `eval (A ·.1 ·.2) P = det ((of A).submatrix ρ₀ κ₀)`.
  have hencode : ∀ A : Fin m → Fin n → ℝ,
      MvPolynomial.eval (fun ij : Fin m × Fin n => A ij.1 ij.2) P
        = ((Matrix.of A).submatrix ρ₀ κ₀).det := by
    intro A
    have hAmap : Agen.map (MvPolynomial.eval (fun ij : Fin m × Fin n => A ij.1 ij.2))
        = Matrix.of A := by
      ext i j
      simp only [Matrix.map_apply, hAgen, Matrix.of_apply, MvPolynomial.eval_X]
    rw [hP, RingHom.map_det]
    exact congrArg Matrix.det (congrArg (fun M => Matrix.submatrix M ρ₀ κ₀) hAmap)
  -- `P ≠ 0`: the identity witness `W i j = [i = j]` makes the `castLE` minor the identity (det 1).
  have hPne : P ≠ 0 := by
    intro hzero
    set W : Fin m → Fin n → ℝ := fun i j => if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0 with hW
    have hWsub : (Matrix.of W).submatrix ρ₀ κ₀ = (1 : Matrix (Fin (c + 1)) (Fin (c + 1)) ℝ) := by
      ext k l
      simp only [Matrix.submatrix_apply, Matrix.of_apply, hW, hρ₀, hκ₀, Fin.castLEEmb_apply,
        Fin.val_castLE, Matrix.one_apply]
      by_cases hkl : k = l
      · subst hkl; simp
      · rw [if_neg (by exact fun h => hkl (Fin.ext h)), if_neg hkl]
    have hev := hencode W
    rw [hzero, map_zero, hWsub, Matrix.det_one] at hev
    exact one_ne_zero hev.symm
  -- a.e. the minor is nonzero, hence `rank ≥ c+1`.
  filter_upwards [ae_matrix_eval_ne_zero P hPne] with A hA
  rw [hencode] at hA
  by_contra hlt
  rw [not_le] at hlt
  exact hA (Core.submatrix_det_eq_zero_of_rank_le (A := Matrix.of A) (r := c) (by omega) ρ₀ κ₀)

/-! ## The genuinely-new cover (deeper-cut analogue of `sjBoundaryPeel`) — hole (d) piece -/

/-- **The good-case box→shell-sum cover (GENUINELY-NEW — sorried, pending design sanity-check).** The
layer-product box integral is bounded by the finite sum, over the singular shells `j : Fin (r+1)`
(`r = min (M₀−t★) (M₁−t★)`, `t★ = bindingCut M`) and the pivot-column embeddings `κ`, of the deeper-cut
spine integrands at cut `t★+j` restricted to shell `j`. This is the shell-stratify (outer tail,
`offSector_cover_le` / `singularShell_iUnion`) + per-shell re-peel of the front factor at the deeper cut
`t★+j` (`gammaPeelIntegral_schurShearFree_eq` on the shell + pivot-cover at depth `t★+j`, whose
`{rank < t★+j}` null-set is SNAG-D). It is UNDECORATED (a statement about `routeMLayerBoxIntegral`) — the
decoration enters only in the `D.integral → monomial · routeMLayerBoxIntegral` separation. -/
theorem routeMBox_le_shellSum (M : Fin (L + 1 + 1 + 1) → ℕ) (c' : ℝ) {ε : ℝ} (hε : 0 < ε) :
    routeMLayerBoxIntegral M c' 1
      ≤ ∑ j : Fin (min (M 0 - bindingCut M) (M 1 - bindingCut M) + 1),
          ∑ _ρ : Fin (bindingCut M + (j : ℕ)) ↪ Fin (M 0),
            ∑ κ : Fin (bindingCut M + (j : ℕ)) ↪ Fin (M 1),
              shellSpineIntegrand M (bindingCut M + (j : ℕ)) κ ε
                (min (M 0 - bindingCut M) (M 1 - bindingCut M)) j c' := by
  sorry

/-! ## The assembled hole (d) — `deeperFlagGood_finite_impl` (assembly sorried, pending checkpoint) -/

/-- **Hole (d) content — the good-case cover connector (assembly, sorried pending checkpoint).** For a
GOOD chain (delivered as the per-cut pivot source `hgoodpiv`) and an `adm`-admissible `D`, `D` is finite
below `carrierThreshold M`. Consumes the sibling holes (a) `deeperFlagStrictShell_finite` (`hstrict`,
`j < r`) and (b) `deeperFlagSaturatedShell_finite` (`hsat`, `j = r`) as hypotheses — both WITH the
`hcT : c' < carrierThreshold M` clause the controller threads from the `DecoratedStepHyp` dispatch. The
controller wires the RouteMSJDecoratedStep hole to this (deriving `hgoodpiv` from
`hgood : deepTailMin M ≤ M 1` via `minAdm_redChain_le_deepTailMin` + `tailMinWidth = deepTailMin` on the
good side, and passing the real (a)/(b)). Assembly = dispatch `FaithfulSJAt` → `a = M 0`
(`a_eq_M0_of_domEq`) → Tonelli-separate (as `#4`) → `routeMBox_le_shellSum` → (a)/(b) per shell →
`ENNReal.sum_lt_top`. -/
theorem deeperFlagGood_finite_impl (M : Fin (L + 1 + 1 + 1) → ℕ) (D : SJDecoration M)
    (hD : adm (L + 1 + 1) M D)
    (hgoodpiv : ∀ u, minAdm (redChain u M) ≤ u * tailMinWidth M)
    (hIH : ∀ (M' : Fin (L + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (L + 1) M' D' → DecoratedBoxThresholdFinite D')
    -- (a) sibling hole `deeperFlagStrictShell_finite`, WITH the `hcT : c' < carrierThreshold M` clause.
    (hstrict : ∀ (t j : ℕ) (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ}, 0 < ε → ∀ (c' : ℝ),
        t ≤ min (M 0) (M 1) → (hj : j ≤ min (M 0 - t) (M 1 - t)) → 1 ≤ t → (∀ i, 1 ≤ M i) →
        minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M →
        (M 0 - (t + j)) + (M 1 - (t + j)) ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j →
        min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2 →
        (((M 0 - (t + j)) * (M 1 - (t + j)) : ℕ) : ℝ) / 2 < c' →
        j < min (M 0 - t) (M 1 - t) → c' < carrierThreshold M →
        shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t))
          ⟨j, Nat.lt_succ_of_le hj⟩ c' < ⊤)
    -- (b) sibling hole `deeperFlagSaturatedShell_finite`, WITH `hcT`.
    (hsat : ∀ (t j : ℕ) (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ}, 0 < ε → ∀ (c' : ℝ),
        t ≤ min (M 0) (M 1) → (hj : j ≤ min (M 0 - t) (M 1 - t)) → 1 ≤ t → (∀ i, 1 ≤ M i) →
        minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M →
        (M 0 - (t + j)) + (M 1 - (t + j)) ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j →
        min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2 →
        (((M 0 - (t + j)) * (M 1 - (t + j)) : ℕ) : ℝ) / 2 < c' →
        j = min (M 0 - t) (M 1 - t) → c' < carrierThreshold M →
        shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t))
          ⟨j, Nat.lt_succ_of_le hj⟩ c' < ⊤) :
    DecoratedBoxThresholdFinite D := by
  sorry

end DLNFibre.DLN.RLCT
