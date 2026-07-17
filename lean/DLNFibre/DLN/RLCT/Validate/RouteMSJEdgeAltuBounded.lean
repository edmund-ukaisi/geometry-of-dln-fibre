import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeAssembly
import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeSelector
import DLNFibre.DLN.RLCT.Validate.RouteMSJProjRadial
import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapseWide
import DLNFibre.DLN.RLCT.Validate.RouteMSJInnerDescent
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankSurvival

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeAltuBounded` — the b=1, a<u, bounded-w arm of the front-collapse dispatch

**Thread `d1altu` (Lane-1 `d≤1` dispatch, the b=1 corank-one edge, a<u bounded arm).** Fills the
`b = 1` (`M₁ − t = 1`), `a < u` (`M₀ − t < t`), bounded-density (`M₂ ≤ M₁ − t`) arm of the front-collapse
dispatch that discharges `innerCorankDescent_lt_top`'s `d ≤ 1` native `sorry`
(`RouteMSJDecoratedPeelStep:121`). Matches the socket's freed-`Γ` triple conclusion exactly (minus the
unused `ρ`).

Target integrand (the RHS of `gammaPeelIntegral_schurShearFree_eq`, the freed-`Γ` triple):

    ∫_{A' ∈ box(tailChain M)} ∫_{x ∈ outerDom t (M₀−t) (M₁−t) 1}
      ∫_{Γ ∈ shearbox} (freedSchurLoss x Γ ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id))^{−c'} < ⊤

Status: SPECIFY skeleton (signature validated against the socket; body `sorry`). The PROVE step is
gated on a scoping decision — see the `d1altu` report: the brief's radial recipe (steps 2–5, via
`edge_leaf_gamma_bound`/`scaledRadialEuclid`) gives a VACUOUS bound for `c' ≤ a/2` (the a-radial `B`
diverges when `a ≥ 2c'`), so the full `c' < ½·minAdm M` window needs a two-branch dispatch (bounded
branch for `c' ≤ a/2`). Numerically-verified charge facts: `minAdm M'' = minAdm(redChain t M)` (M'' the
keep-M₁ chain), coverage `min(a, minAdm M) ≤ minAdm M''`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators Matrix

/-! ## The charge sub-lemma (pure `minAdm` nat algebra, decorrelated)

The front-collapse invocation feeds the keep-`M₁` chain `M'' = (t, M₁, M₂, …)` to
`frontCollapse_wide_bounded_lt_top`, which needs the threshold `exponent < ½·minAdm M''`. The available
bound is `exponent < ½·minAdm (redChain t M)` (from `c' < ½·minAdm M` + the harvest lemma
`minAdm_le_peelCharge_add_redChain`). Transferring it needs `minAdm (redChain t M) ≤ minAdm M''`, which
this block supplies. It rests on a general "first-coordinate Lipschitz" bound on `minAdm`. -/

/-- **First-coordinate Lipschitz bound for `minAdm`.** Raising the leading dimension of a chain from `y`
to `x` (`y ≤ x`) increases `minAdm` by at most `(x − y)·(second dimension)`:
`minAdm (cons x rest) ≤ (x − y)·rest 0 + minAdm (cons y rest)`. Leaf (`Fin 2`): equality
`x·rest₀ = (x−y)·rest₀ + y·rest₀`. Recursion: take a minimiser `r*` of `minAdm (cons y rest)`'s layer-peel
(`LayerSplit_value_eq_minAdm` + `Finset.exists_mem_eq_inf'`); the harvest lemma at `r*` bounds
`minAdm (cons x rest)`, and `redChain r* (cons x rest) = redChain r* (cons y rest)` (the reduced chain
drops the leading two entries, so is `x`/`y`-independent), so the two differ by
`(x−r*)(rest₀−r*) − (y−r*)(rest₀−r*) = (x−y)(rest₀−r*) ≤ (x−y)·rest₀`. -/
theorem minAdm_cons_le_first_lipschitz {K : ℕ} (rest : Fin (K + 1) → ℕ) (x y : ℕ) (hyx : y ≤ x) :
    minAdm (Fin.cons x rest) ≤ (x - y) * rest 0 + minAdm (Fin.cons y rest) := by
  rcases K with _ | K'
  · -- leaf: `Fin 2` chains, `minAdm = product`.
    have hcons1 : ∀ z : ℕ, (Fin.cons z rest : Fin 2 → ℕ) 1 = rest 0 := by
      intro z; rw [← Fin.succ_zero_eq_one, Fin.cons_succ]
    have hx : minAdm (Fin.cons x rest) = x * rest 0 := by
      rw [← minAdmRec_eq_minAdm, minAdmRec_leaf, Fin.cons_zero, hcons1]
    have hy : minAdm (Fin.cons y rest) = y * rest 0 := by
      rw [← minAdmRec_eq_minAdm, minAdmRec_leaf, Fin.cons_zero, hcons1]
    rw [hx, hy, ← add_mul, Nat.sub_add_cancel hyx]
  · -- recursion: `cons x rest : Fin (K'+1+1+1)`.
    have hc0 : ∀ z : ℕ, (Fin.cons z rest : Fin (K' + 1 + 1 + 1) → ℕ) 0 = z := by
      intro z; rw [Fin.cons_zero]
    have hc1 : ∀ z : ℕ, (Fin.cons z rest : Fin (K' + 1 + 1 + 1) → ℕ) 1 = rest 0 := by
      intro z; rw [Fin.cons_one]
    obtain ⟨r, hr_mem, hr_eq⟩ := Finset.exists_mem_eq_inf'
      (show (Finset.range (min ((Fin.cons y rest : Fin (K' + 1 + 1 + 1) → ℕ) 0)
          ((Fin.cons y rest : Fin (K' + 1 + 1 + 1) → ℕ) 1) + 1)).Nonempty by simp)
      (fun s => ((Fin.cons y rest : Fin (K' + 1 + 1 + 1) → ℕ) 0 - s)
          * ((Fin.cons y rest : Fin (K' + 1 + 1 + 1) → ℕ) 1 - s)
        + minAdm (redChain s (Fin.cons y rest)))
    rw [Finset.mem_range, Nat.lt_succ_iff, le_min_iff] at hr_mem
    have hry : r ≤ y := (hc0 y) ▸ hr_mem.1
    have hr0 : r ≤ rest 0 := (hc1 y) ▸ hr_mem.2
    have hrx : r ≤ min x (rest 0) := le_min (le_trans hry hyx) hr0
    -- the layer-peel value of `minAdm (cons y rest)` at the minimiser `r` (heads kept symbolic).
    have hyval0 : minAdm (Fin.cons y rest)
        = ((Fin.cons y rest : Fin (K' + 1 + 1 + 1) → ℕ) 0 - r)
            * ((Fin.cons y rest : Fin (K' + 1 + 1 + 1) → ℕ) 1 - r)
          + minAdm (redChain r (Fin.cons y rest)) :=
      (LayerSplit_value_eq_minAdm (Fin.cons y rest)).symm.trans hr_eq
    have hyval : minAdm (Fin.cons y rest)
        = (y - r) * (rest 0 - r) + minAdm (redChain r (Fin.cons y rest)) := by
      rw [hyval0, hc0, hc1]
    -- the harvest bound on `minAdm (cons x rest)` at cut `r`.
    have hxle : minAdm (Fin.cons x rest)
        ≤ (x - r) * (rest 0 - r) + minAdm (redChain r (Fin.cons x rest)) := by
      have h := minAdm_le_peelCharge_add_redChain (Fin.cons x rest) r (by rw [hc0, hc1]; exact hrx)
      rwa [peelCharge, hc0, hc1] at h
    -- the reduced chain is `x`/`y`-independent.
    have hred : redChain r (Fin.cons x rest) = redChain r (Fin.cons y rest) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [redChain]
      · simp only [redChain, Fin.cons_succ]
    -- combine.
    calc minAdm (Fin.cons x rest)
        ≤ (x - r) * (rest 0 - r) + minAdm (redChain r (Fin.cons x rest)) := hxle
      _ = (x - r) * (rest 0 - r) + minAdm (redChain r (Fin.cons y rest)) := by rw [hred]
      _ = (x - y) * (rest 0 - r) + minAdm (Fin.cons y rest) := by
            rw [hyval]
            have hxr : x - r = (x - y) + (y - r) := by omega
            rw [hxr, add_mul]; ring
      _ ≤ (x - y) * rest 0 + minAdm (Fin.cons y rest) := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _

/-- **The keep-`M₁` chain dominates the reduced chain (the `≥` charge direction).** For the front-collapse
chain `M'' = (t, M₁, M₂, …) = Fin.cons t (tail M)`, if the second layer is bounded (`M₂ ≤ M₁ − t`) and
`t ≤ M₁`, then `minAdm (redChain t M) ≤ minAdm M''`. Combined with the harvest lemma
`minAdm M ≤ (M₀−t)(M₁−t) + minAdm (redChain t M)`, this transfers a threshold below `½·minAdm (redChain t M)`
up to `½·minAdm M''`, the hypothesis `frontCollapse_wide_bounded_lt_top` needs at chain `M''`. Layer-peel
`M''` (`LayerSplit_value_eq_minAdm`); each cut `t' ≤ t` gives, via the first-coordinate Lipschitz bound
(`minAdm_cons_le_first_lipschitz`, `x=t, y=t'`) plus `M₂ ≤ M₁ − t ≤ M₁ − t'`,
`minAdm (redChain t M) ≤ (t−t')·M₂ + minAdm (redChain t' M) ≤ (t−t')(M₁−t') + minAdm (redChain t' M'')`. -/
theorem minAdm_redChain_le_consFront {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (hb : M 2 ≤ M 1 - t) :
    minAdm (redChain t M) ≤ minAdm (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ)) := by
  set rest : Fin (L + 1 + 1) → ℕ := fun i => M i.succ with hrest
  have e0 : (Fin.cons t rest : Fin (L + 1 + 1 + 1) → ℕ) 0 = t := by rw [Fin.cons_zero]
  have e1 : ∀ z : ℕ, (Fin.cons z rest : Fin (L + 1 + 1 + 1) → ℕ) 1 = M 1 := by
    intro z; rw [Fin.cons_one, hrest]; simp only [Fin.succ_zero_eq_one]
  -- the reduced chain of `M''` at cut `t'` is the reduced chain of `M`.
  have hredM : ∀ t' : ℕ, redChain t' (Fin.cons t rest) = redChain t' M := by
    intro t'
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [redChain]
    · simp only [redChain, Fin.cons_succ, hrest]
  rw [← LayerSplit_value_eq_minAdm (Fin.cons t rest)]
  refine Finset.le_inf' _ _ (fun t' ht' => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff, le_min_iff] at ht'
  have ht't : t' ≤ t := (e0) ▸ ht'.1
  -- the first-coordinate Lipschitz bound at `x=t, y=t'` on the reduced-chain tail.
  have hlip := minAdm_cons_le_first_lipschitz (fun i : Fin (L + 1) => M i.succ.succ) t t' ht't
  -- `redChain t M = cons t (tail²)`, `redChain t' M = cons t' (tail²)`, and `tail² 0 = M 2`.
  have hrc_t : redChain t M = Fin.cons t (fun i : Fin (L + 1) => M i.succ.succ) := rfl
  have hrc_t' : redChain t' M = Fin.cons t' (fun i : Fin (L + 1) => M i.succ.succ) := rfl
  have hM2 : (fun i : Fin (L + 1) => M i.succ.succ) 0 = M 2 := rfl
  rw [hM2] at hlip
  -- assemble.
  calc minAdm (redChain t M)
      = minAdm (Fin.cons t (fun i : Fin (L + 1) => M i.succ.succ)) := by rw [hrc_t]
    _ ≤ (t - t') * M 2 + minAdm (Fin.cons t' (fun i : Fin (L + 1) => M i.succ.succ)) := hlip
    _ = (t - t') * M 2 + minAdm (redChain t' M) := by rw [← hrc_t']
    _ ≤ (t - t') * (M 1 - t') + minAdm (redChain t' M) := by
          refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _
          exact le_trans hb (Nat.sub_le_sub_left ht't _)
    _ = ((Fin.cons t rest : Fin (L + 1 + 1 + 1) → ℕ) 0 - t')
          * ((Fin.cons t rest : Fin (L + 1 + 1 + 1) → ℕ) 1 - t')
        + minAdm (redChain t' (Fin.cons t rest)) := by rw [e0, e1, hredM]

/-! ## Step 2 — the shifted pivot change-of-variables (`y ↦ H = P·y + shift`)

The pivot side of the disposal integrates the `H`-radial THROUGH the reduced-chain leading layer `y`
(`H = P·y + η·B₁₂`, `y` free, the `η·B₁₂` a fixed shift), NEVER against `B₁₂` — the latter manufactures a
spurious `η^{−u}`. The `y ↦ H` map is left-multiplication by `P` plus a shift, so `|det P|` cancels clean.
This is the shifted variant of `lintegral_comp_rmatMulLeft`; verdict-independent, reusable. -/

/-- **Shifted left-multiplication CoV (raw pi).** For invertible `G` and a fixed shift `c`, precomposing a
measurable `ℝ≥0∞`-integrand with `A ↦ G·A + c` scales the full-space integral by `|det G|^{−p}`. The
left-mult Jacobian (`lintegral_comp_rmatMulLeft`) with the shift absorbed by translation invariance
(`lintegral_add_right_eq_self`). The pivot `y ↦ H = P·y + η·B₁₂` CoV (integrate through `y`, `η·B₁₂` fixed):
`|det P|` cancels, no spurious `η`-power. -/
theorem lintegral_comp_rmatMulLeft_shift {N p : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.det ≠ 0)
    (c : Fin N → Fin p → ℝ) (φ : (Fin N → Fin p → ℝ) → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ A : Fin N → Fin p → ℝ, φ ((fun i j => ∑ k, G i k * A k j) + c))
      = ENNReal.ofReal (|G.det| ^ p)⁻¹ * ∫⁻ B, φ B := by
  have hψ : Measurable (fun B : Fin N → Fin p → ℝ => φ (B + c)) :=
    hφ.comp (measurable_id.add_const c)
  have h1 := lintegral_comp_rmatMulLeft G hG (fun B => φ (B + c)) hψ
  have h2 : (∫⁻ B : Fin N → Fin p → ℝ, φ (B + c)) = ∫⁻ B, φ B :=
    lintegral_add_right_eq_self φ c
  calc (∫⁻ A : Fin N → Fin p → ℝ, φ ((fun i j => ∑ k, G i k * A k j) + c))
      = ∫⁻ A : Fin N → Fin p → ℝ, (fun B => φ (B + c)) (fun i j => ∑ k, G i k * A k j) := rfl
    _ = ENNReal.ofReal (|G.det| ^ p)⁻¹ * ∫⁻ B, φ (B + c) := h1
    _ = ENNReal.ofReal (|G.det| ^ p)⁻¹ * ∫⁻ B, φ B := by rw [h2]

/-! ## The pivot-energy reindex (the frontCollapse connection, algebraic crux)

`W = frobSq(P·Q̃ₚ)` with `Q̃ₚ = Q_inl + P⁻¹·B₁₂·Q_inr` is inverse-free (`pivotEnergy_inverse_free`):
`P·Q̃ₚ = P·Q_inl + B₁₂·Q_inr`. With `Q = QT.submatrix (blockSplitEquiv κ) id`, the left/right column
blocks read the κ-image / complement rows of `QT`, so `P·Q_inl + B₁₂·Q_inr` is a single raw product
`rmatMul X̂ QT` with `X̂` the κ-reindexed front `[P | B₁₂]` — the frontCollapse front matrix. -/

/-- **The pivot-energy reindex.** For `Q = QT.submatrix (blockSplitEquiv κ) id`, the inverse-free pivot
factor `P·Q_inl + B₁₂·Q_inr` equals the raw product `rmatMul X̂ QT`, where `X̂ I n =
Sum.elim (P I) (B₁₂ I) ((blockSplitEquiv κ).symm n)` places `[P | B₁₂]`'s columns at the κ-image / complement
rows of `QT`. Reindex the `QT`-row sum by `blockSplitEquiv κ` (`Equiv.sum_comp`) + split the sum type
(`Fintype.sum_sum_type`); `blockSplitEquiv_inl` identifies the left block with `κ`. -/
theorem pivotEnergy_reindex_rmatMul {t m q : ℕ} (P : Fin t → Fin t → ℝ)
    (B12 : Fin t → Fin (m - t) → ℝ) (QT : Matrix (Fin m) (Fin q) ℝ) (κ : Fin t ↪ Fin m) :
    Matrix.of P * ((QT.submatrix (blockSplitEquiv κ) id).submatrix Sum.inl id)
        + Matrix.of B12 * ((QT.submatrix (blockSplitEquiv κ) id).submatrix Sum.inr id)
      = Matrix.of (rmatMul
          (fun (I : Fin t) (n : Fin m) => Sum.elim (P I) (B12 I) ((blockSplitEquiv κ).symm n)) QT) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.submatrix_apply,
    rmatMul, id_eq]
  -- RHS: reindex the `Fin m` sum by `blockSplitEquiv κ`, then split the sum type.
  rw [← Equiv.sum_comp (blockSplitEquiv κ)
      (fun n => Sum.elim (P i) (B12 i) ((blockSplitEquiv κ).symm n) * QT n j),
    Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply]
  simp only [Sum.elim_inl, Sum.elim_inr, blockSplitEquiv_inl]

/-! ## The standard-equiv front reindex (direct `wingFrontBox` membership)

To feed `frontCollapse_wide_bounded_lt_top` (front over `Fin M₁` columns, `wingFrontBox = leading-t-block
invertible`), reindex the raw `PB = [P | B₁₂]`'s sum-type columns to `Fin M₁` by the STANDARD
`finSumFinEquiv` (`Sum.inl ↦ first-t`) — NOT `blockSplitEquiv κ` (which κ-permutes and would put `P` at
the κ-image columns, breaking direct membership). With the standard equiv the leading `t`-block is `P`, so
membership is `IsUnit P` (the `outerPB` chart), and the κ moves entirely into the tail. -/

/-- **The standard sum→`Fin` column equiv** `Fin t ⊕ Fin (M₁−t) ≃ Fin M₁` (needs `t ≤ M₁`), sending
`Sum.inl` onto the FIRST `t` indices (`finSumFinEquiv` + the `t + (M₁−t) = M₁` cast). -/
noncomputable def frontStdEquiv {t M₁ : ℕ} (htM1 : t ≤ M₁) : Fin t ⊕ Fin (M₁ - t) ≃ Fin M₁ :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' htM1))

/-- `frontStdEquiv` sends `Sum.inl i` to `i` embedded in the first `t` indices. -/
theorem frontStdEquiv_symm_castLE {t M₁ : ℕ} (htM1 : t ≤ M₁) (j : Fin t) :
    (frontStdEquiv htM1).symm (Fin.castLE htM1 j) = Sum.inl j := by
  rw [frontStdEquiv, Equiv.symm_trans_apply]
  have : (finCongr (Nat.add_sub_cancel' htM1)).symm (Fin.castLE htM1 j)
      = Fin.castAdd (M₁ - t) j := by
    apply Fin.ext; simp
  rw [this, finSumFinEquiv_symm_apply_castAdd]

/-- **Front reindex ⟹ leading column reads `P`.** For the `frontStdEquiv`-reindexed raw front, the
leading `t`-columns read `P`: `Sum.elim (P i) (B₁₂ i) ((frontStdEquiv htM1).symm (castLE j)) = P i j`,
since `(frontStdEquiv).symm (castLE j) = Sum.inl j`. This makes the leading `t×t` block of the reindexed
front equal to `P`, so its `IsUnit` ⟺ `IsUnit P` (the `outerPB` chart). -/
theorem frontStd_leadingBlock {t M₁ : ℕ} (htM1 : t ≤ M₁) (P : Fin t → Fin t → ℝ)
    (B12 : Fin t → Fin (M₁ - t) → ℝ) (i j : Fin t) :
    Sum.elim (P i) (B12 i) ((frontStdEquiv htM1).symm (Fin.castLE htM1 j)) = P i j := by
  rw [frontStdEquiv_symm_castLE htM1 j, Sum.elim_inl]

/-- **The standard front measurable equiv** `((P, B₁₂)) ≃ᵐ (Fin t → Fin M₁ → ℝ)` — combine the pivot
pair into a sum-front (`splitCols⁻¹`) then reindex columns to `Fin M₁` by `frontStdEquiv` (`Sum.inl`
onto the first `t`). Measure-preserving; `frontStdEquivM pb i m = Sum.elim (pb.1 i) (pb.2 i)
((frontStdEquiv htM1).symm m)`. -/
noncomputable def frontStdEquivM {t M₁ : ℕ} (htM1 : t ≤ M₁) :
    ((Fin t → Fin t → ℝ) × (Fin t → Fin (M₁ - t) → ℝ)) ≃ᵐ (Fin t → Fin M₁ → ℝ) :=
  (splitCols t t (M₁ - t)).symm.trans
    (MeasurableEquiv.arrowCongr' (Equiv.refl (Fin t))
      (MeasurableEquiv.arrowCongr' (frontStdEquiv htM1) (MeasurableEquiv.refl ℝ)))

/-- `frontStdEquivM pb i m = Sum.elim (pb.1 i) (pb.2 i) ((frontStdEquiv htM1).symm m)`. -/
theorem frontStdEquivM_apply {t M₁ : ℕ} (htM1 : t ≤ M₁)
    (pb : (Fin t → Fin t → ℝ) × (Fin t → Fin (M₁ - t) → ℝ)) (i : Fin t) (m : Fin M₁) :
    frontStdEquivM htM1 pb i m = Sum.elim (pb.1 i) (pb.2 i) ((frontStdEquiv htM1).symm m) := rfl

/-- `frontStdEquivM` is measure-preserving. -/
theorem measurePreserving_frontStdEquivM {t M₁ : ℕ} (htM1 : t ≤ M₁) :
    MeasurePreserving (frontStdEquivM htM1)
      (volume : Measure ((Fin t → Fin t → ℝ) × (Fin t → Fin (M₁ - t) → ℝ)))
      (volume : Measure (Fin t → Fin M₁ → ℝ)) := by
  refine MeasurePreserving.trans (measurePreserving_splitCols t t (M₁ - t)).symm ?_
  exact volume_preserving_arrowCongr' (Equiv.refl (Fin t))
    (MeasurableEquiv.arrowCongr' (frontStdEquiv htM1) (MeasurableEquiv.refl ℝ))
    (volume_preserving_arrowCongr' (frontStdEquiv htM1) (MeasurableEquiv.refl ℝ)
      (MeasurePreserving.id volume))

/-- **The shear-image box has the same volume as the centered box** (translation-invariance): the shear
`Γ ↦ Γ + s` is measure-preserving, and the shearbox is its preimage of `genBox`. -/
theorem volume_shearbox_eq {a b : ℕ} (s : Fin a → Fin b → ℝ) (T : ℝ) :
    volume {Γ : Fin a → Fin b → ℝ | Γ + s ∈ genBox (Fin a) (Fin b) T}
      = volume (genBox (Fin a) (Fin b) T) := by
  have hpre : {Γ : Fin a → Fin b → ℝ | Γ + s ∈ genBox (Fin a) (Fin b) T}
      = (fun Γ => Γ + s) ⁻¹' genBox (Fin a) (Fin b) T := rfl
  rw [hpre, (measurePreserving_add_right (volume : Measure (Fin a → Fin b → ℝ)) s).measure_preimage
    (measurableSet_genBox T).nullMeasurableSet]

/-! ## The keep-`M₁` chain and its front-collapse finiteness (α-LOW target)

The α-LOW clean branch feeds the keep-`M₁` chain `M'' = (t, M₁, M₂, …) = Fin.cons t (tailChain M)` to
`frontCollapse_wide_bounded_lt_top`. Its tail chain is `tailChain M` (the A'-domain of the target). -/

/-- `tailChain (Fin.cons t (tailChain M)) = tailChain M` — the keep-`M₁` chain's tail is `tailChain M`. -/
theorem tailChain_consFront {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) :
    tailChain (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ)) = (fun i : Fin (L + 1 + 1) => M i.succ) := by
  funext i
  rw [tailChain, Fin.cons_succ]

-- Heartbeats raised: the `tailChain (Fin.cons t …) ≡ M ·.succ` chain defeqs and the `Fin.cons`
-- width reductions (`M'' 1 ≡ M 1`, etc.) force expensive `whnf` during elaboration.
set_option maxHeartbeats 1600000 in
/-- **The keep-`M₁` chain front-collapse finiteness (α-LOW target integral).** For the keep-`M₁` chain
`M'' = Fin.cons t (tailChain M)`, below `½·minAdm (redChain t M)` (which transfers to `½·minAdm M''` via
`minAdm_redChain_le_consFront`), in the wide (`t ≤ M₁`) bounded (`M₂ ≤ M₁−t`) regime, the front-factor box
integral over `wingFrontBox M'' × paramsBoxM(tailChain M)` is finite. -/
theorem edge_frontCollapse_consFront_lt_top {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht2 : t ≤ min (M 0) (M 1)) (hbnd : (M 2 : ℝ) < (M 1 : ℝ) - t + 1) (hb : M 2 ≤ M 1 - t)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hlow : (c' : ℝ) < (minAdm (redChain t M) : ℝ) / 2) :
    (∫⁻ F in wingFrontBox (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ)),
        ∫⁻ A' in paramsBoxM (fun i : Fin (L + 1 + 1) => M i.succ) 1,
          ENNReal.ofReal ((frobSq (rmatMul F
            (prod (fun i : Fin (L + 1 + 1) => M i.succ) A'))) ^ (-(c' : ℝ)))) < ⊤ := by
  -- the chain values for `M'' = Fin.cons t (fun i => M i.succ)`
  have h0 : (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 0 = t := by
    rw [Fin.cons_zero]
  have h1 : (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 1 = M 1 := by
    rw [Fin.cons_one]; simp only [Fin.succ_zero_eq_one]
  have h2 : (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 2 = M 2 := by
    rw [show (2 : Fin (L + 1 + 1 + 1)) = (1 : Fin (L + 1 + 1)).succ from rfl, Fin.cons_succ,
      Fin.succ_one_eq_two]
  have hwide : (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 0
      ≤ (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 1 := by
    rw [h0, h1]; exact le_trans ht2 (min_le_right _ _)
  have hbnd'' : ((Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 2 : ℝ)
      < ((Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 1 : ℝ)
        - ((Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 0 : ℝ) + 1 := by
    rw [h0, h1, h2]; exact hbnd
  -- threshold transfer: c' < ½·minAdm (redChain t M) ≤ ½·minAdm M''
  have hle : minAdm (redChain t M)
      ≤ minAdm (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ)) :=
    minAdm_redChain_le_consFront M t hb
  have hc'' : (c' : ℝ)
      < (minAdm (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ)) : ℝ) / 2 := by
    have : (minAdm (redChain t M) : ℝ)
        ≤ (minAdm (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ)) : ℝ) := by exact_mod_cast hle
    linarith
  have hFC := frontCollapse_wide_bounded_lt_top
    (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ)) hwide hbnd'' hIH c' hc''
  exact tailChain_consFront M t ▸ hFC

/-- **The syntactic (`Fin t → Fin M₁`) clean front box** — the `wingFrontBox` of the keep-`M₁` chain
`M'' = Fin.cons t (tailChain M)` restated over the syntactic widths `t`, `M₁` (min-free): all entries in
`[−1,1]` and the leading `t×t` block (first `t` columns via `Fin.castLE htM1`) invertible. Its `IsUnit`
condition is exactly the form `frontStd_leadingBlock` produces, so downstream `frontStdEquivM` membership
is cast-free (avoids the `Fin (min (M''0)(M''1))` opaque-width friction of `leadingBlock`). -/
def cleanFrontBox {t M₁ : ℕ} (htM1 : t ≤ M₁) : Set (Fin t → Fin M₁ → ℝ) :=
  {F | (∀ i j, F i j ∈ Set.Icc (-1 : ℝ) 1)
    ∧ IsUnit (Matrix.of (fun i j : Fin t => F i (Fin.castLE htM1 j)))}

-- Heartbeats raised: the `Fin.cons` width defeqs (`M'' 0 ≡ t`, `M'' 1 ≡ M 1`) force `whnf` here.
set_option maxHeartbeats 1600000 in
/-- **`wingFrontBox (Fin.cons t (tailChain M)) = cleanFrontBox`** — the ONE controlled width-cast
conversion (min-cast localized here). The box conditions match; the `IsUnit(leadingBlock M'')` block equals
the `cleanFrontBox` leading block up to the `min (M''0)(M''1) = t` `finCongr` reindex
(`Matrix.isUnit_submatrix_equiv`). Semantics-preserving: same `t×t` leading block, just min-free. -/
theorem wingFrontBox_consFront_eq_cleanBox {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (htM1 : t ≤ M 1) :
    wingFrontBox (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ)) = cleanFrontBox htM1 := by
  have hM0 : (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 0 = t :=
    Fin.cons_zero _ _
  have hM1' : (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 1 = M 1 := by
    rw [Fin.cons_one]; simp only [Fin.succ_zero_eq_one]
  have hmin : min ((Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 0)
      ((Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ) : Fin (L + 1 + 1 + 1) → ℕ) 1) = t := by
    rw [hM0, hM1', min_eq_left htM1]
  ext F
  simp only [wingFrontBox, cleanFrontBox, Set.mem_setOf_eq]
  refine and_congr Iff.rfl ?_
  have hEq : Matrix.of (fun i j : Fin t => F i (Fin.castLE htM1 j))
      = (leadingBlock (Fin.cons t (fun i : Fin (L + 1 + 1) => M i.succ)) F).submatrix
          (finCongr hmin.symm) (finCongr hmin.symm) := by
    ext I J
    simp only [Matrix.of_apply, Matrix.submatrix_apply, leadingBlock]
    refine congr_arg₂ F ?_ ?_ <;>
      (apply Fin.ext; simp only [Fin.val_castLE, finCongr_apply, Fin.val_cast])
  exact hEq.symm ▸ (Matrix.isUnit_submatrix_equiv (finCongr hmin.symm) (finCongr hmin.symm)).symm

/-- **The α-LOW target over the syntactic clean front box.** Restates
`edge_frontCollapse_consFront_lt_top` over `cleanFrontBox` (min-free `Fin t → Fin M₁` front), via the ONE
controlled conversion `wingFrontBox_consFront_eq_cleanBox`. -/
theorem edge_frontCollapse_cleanBox_lt_top {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht2 : t ≤ min (M 0) (M 1)) (hbnd : (M 2 : ℝ) < (M 1 : ℝ) - t + 1) (hb : M 2 ≤ M 1 - t)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hlow : (c' : ℝ) < (minAdm (redChain t M) : ℝ) / 2) :
    (∫⁻ F in cleanFrontBox (show t ≤ M 1 from le_trans ht2 (min_le_right _ _)),
        ∫⁻ A' in paramsBoxM (fun i : Fin (L + 1 + 1) => M i.succ) 1,
          ENNReal.ofReal ((frobSq (rmatMul F
            (prod (fun i : Fin (L + 1 + 1) => M i.succ) A'))) ^ (-(c' : ℝ)))) < ⊤ := by
  rw [← wingFrontBox_consFront_eq_cleanBox M t (le_trans ht2 (min_le_right _ _))]
  exact edge_frontCollapse_consFront_lt_top M t ht2 hbnd hb hIH c' hlow

/-! ## The pivot-energy zero locus is null (the a.e.-`W > 0` restriction)

For a fixed nonzero tail product `QT`, the front-Gram zero locus `{F | frobSq (rmatMul F QT) = 0}` is
Lebesgue-null: `frobSq = 0` forces the `(0, j₀)`-entry (a nonzero polynomial in `F`, `QT`'s column `j₀`
nonzero) to vanish, and a nonzero polynomial's zero set is null (`ae_matrix_eval_ne_zero`). -/

/-- **Column-reindex of the raw product.** `rmatMul (fun I m => F I (e m)) QT = rmatMul F (QT.submatrix
e.symm id)` — a column permutation of the front `F` is a row permutation of the tail `QT`. -/
theorem rmatMul_colReindex {t n q : ℕ} (e : Fin n ≃ Fin n) (F : Fin t → Fin n → ℝ)
    (QT : Matrix (Fin n) (Fin q) ℝ) :
    rmatMul (fun I m => F I (e m)) QT = rmatMul F (QT.submatrix e.symm id) := by
  funext I j
  simp only [rmatMul, Matrix.submatrix_apply, id_eq]
  rw [← Equiv.sum_comp e (fun m => F I m * QT (e.symm m) j)]
  exact Finset.sum_congr rfl (fun m _ => by rw [Equiv.symm_apply_apply])

/-- **The front-Gram zero locus is null** (fixed nonzero tail `QT`, `t ≥ 1`). `frobSq (rmatMul F QT) = 0`
forces `(rmatMul F QT) 0 j₀ = 0`, a nonzero polynomial in `F` (`QT`'s column `j₀ ≠ 0`); its zero set is
Lebesgue-null by `ae_matrix_eval_ne_zero`. -/
theorem ae_frobSq_rmatMul_ne_zero {t n q : ℕ} (ht : 1 ≤ t) (QT : Matrix (Fin n) (Fin q) ℝ)
    (hQT : QT ≠ 0) :
    ∀ᵐ F : Fin t → Fin n → ℝ, frobSq (rmatMul F QT) ≠ 0 := by
  classical
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  -- pick a nonzero column `j₀` of `QT`.
  obtain ⟨k₀, j₀, hkj⟩ : ∃ k j, QT k j ≠ 0 := by
    by_contra h
    apply hQT
    ext k j
    by_contra hkj
    exact h ⟨k, j, hkj⟩
  -- the `(0, j₀)`-entry polynomial `P = ∑ k, X(0,k)·C(QT k j₀)`.
  set P : MvPolynomial (Fin (t' + 1) × Fin n) ℝ :=
    ∑ k, MvPolynomial.X ((0 : Fin (t' + 1)), k) * MvPolynomial.C (QT k j₀) with hP
  have hencode : ∀ F : Fin (t' + 1) → Fin n → ℝ,
      MvPolynomial.eval (fun ij : Fin (t' + 1) × Fin n => F ij.1 ij.2) P
        = rmatMul F QT (0 : Fin (t' + 1)) j₀ := by
    intro F
    rw [hP, map_sum]
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, rmatMul]
  have hPne : P ≠ 0 := by
    intro h0
    have hev := hencode (fun _ k => if k = k₀ then (1 : ℝ) else 0)
    rw [h0, map_zero] at hev
    have hval : rmatMul (fun _ k => if k = k₀ then (1 : ℝ) else 0) QT (0 : Fin (t' + 1)) j₀
        = QT k₀ j₀ := by
      simp only [rmatMul]
      rw [Finset.sum_eq_single k₀ (fun k _ hk => by rw [if_neg hk, zero_mul])
        (fun h => absurd (Finset.mem_univ k₀) h), if_pos rfl, one_mul]
    rw [hval] at hev
    exact hkj hev.symm
  filter_upwards [ae_matrix_eval_ne_zero P hPne] with F hF
  rw [hencode] at hF
  intro hz
  apply hF
  -- frobSq = 0 ⟹ the (0,j₀) entry is 0.
  rw [frobSq, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))] at hz
  have h2 := hz (0 : Fin (t' + 1)) (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (rmatMul F QT 0 j))] at h2
  exact pow_eq_zero_iff (two_ne_zero) |>.mp (h2 j₀ (Finset.mem_univ _))

/-- **The b=1, a<u, bounded-w arm of the front-collapse dispatch.** For a `≥ 3`-width chain `M` with a
legal pivot cut `1 ≤ t ≤ min(M₀,M₁)` on the corank-one edge (`M₁ − t = 1`), in the `a < u` regime
(`M₀ − t < t`) and bounded-density regime (`M₂ < M₁ − t + 1`, i.e. `M₂ ≤ M₁ − t`), GIVEN the plain
one-shorter strong IH `hIH` and below the geometric threshold (`c' < ½·minAdm M`), the freed-`Γ` triple
integral is finite. This is one arm of the `d ≤ 1` native dispatch of `innerCorankDescent_lt_top`; its
conclusion matches that socket exactly (`ρ` dropped — the freed-`Γ` integrand uses only `κ`). -/
theorem frontCollapse_edge_b1_altu_bounded {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1))
    (κ : Fin t ↪ Fin (M 1)) (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hb1 : M 1 - t = 1)
    (haltu : M 0 - t < t)
    (hbnd : (M 2 : ℝ) < (M 1 : ℝ) - t + 1)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') :
    (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
            ENNReal.ofReal ((freedSchurLoss x Γ
              ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-(c' : ℝ)))) < ⊤ := by
  -- ISOLATED HOLE — the b=1 corank-one FreeBilinear disposal (regime #1: native, no cite, no decoration).
  -- Converged route (lane1shell/d1design, Codex-proven): KEEP the (H,γ) coupling — the drop-transverse
  -- a-fortiori (freedSchurLoss_shear_corank_one_le → single-fragile power) is UNSOUND (discards the
  -- γ-regularization; M=(3,3,1) diverges for 1<c'<3/2), so `∫ (single-fragile power) < ⊤` is FALSE and must
  -- NOT be the isolated sorry. The corank term `Γ·Q_b` is rank-1 (`γ⊗z`, frobSq_rmatMul_corank_one) with γ
  -- free; the sound assembly (M₂≤b, i.e. this `hbnd` regime) is: (1) corank-γ via banked
  -- freeBilinear_box_lt_top (RouteMSJFreeBilinear) + the C-shift absorption; (2) pivot-H via the B₁₂↦H CoV
  -- (|det P| cancels); (3) reduced W via frontCollapse_wide_bounded_lt_top at X=[P|B₁₂], exponent c'−a/2 —
  -- whose threshold c'−a/2 < ½·minAdm M'' the LANDED charge lemmas above supply
  -- (minAdm_redChain_le_consFront + minAdm_le_peelCharge_add_redChain, b=1 ⟹ peelCharge = a).
  -- DEFINITIVE dispatch (d1design d1altu-dispatch-and-D2gate.md). `hbnd` ⟹ M₂ ≤ b = M₁−t, so this arm is
  -- entirely in the M₂≤b regime (no LOG / M₂≥b+2 branches arise). Dispatch on c' vs ½·minAdm(redChain t M):
  --   • α-LOW (c' < ½·minAdm(redChain t M)) — CLEAN, drop the WHOLE corank (charge 0):
  --       freedSchurLoss ≥ W = frobSq(P·Q̃ₚ) (freedSchurLoss_inner_bounded_le, needs 0<W) ⟹ ∫_Γ ≤ W^{−c'}·vol;
  --       W is C,Γ-free; W inverse-free (pivotEnergy_inverse_free) = frobSq(rmatMul X̂ (prod (tailChain M) A')),
  --       X̂ = the κ-reindexed [P|B₁₂] → frontCollapse_wide_bounded_lt_top(X̂∈wingFrontBox M'') at exp c',
  --       threshold c'<½·minAdm(redChain t M) ≤ ½·minAdm M'' via minAdm_redChain_le_consFront.
  --       {W=0} null via ae_matrix_eval_ne_zero (RouteMSJCorankSurvival; W a nonzero matrix-polynomial) —
  --       restrict to co-null {W>0}. ALL pieces banked + verified present.
  --   • α-HIGH (c' ≥ ½·minAdm(redChain t M)) — the a/2 corank charge is needed = the heart's rank-1 (b=1)
  --       joint (Δ,C,Z) FreeBilinear leaf → hIH at c'−a/2, HELD (gated on the heart, jointpnp).
  -- ── α-LOW build state (tide `d1altu-full`) ─────────────────────────────────────────────────────
  -- BANKED green helpers in this file (all axiom-clean, reusable):
  --   • `edge_frontCollapse_consFront_lt_top` — the α-LOW TARGET: charge transfer (via
  --     `minAdm_redChain_le_consFront`) + `frontCollapse_wide_bounded_lt_top` for the keep-M₁ chain
  --     `M'' = Fin.cons t (tailChain M)`, giving `∫_{F∈wingFrontBox M''} ∫_{A'} frobSq(F·prod A')^{−c'} < ⊤`.
  --   • `ae_frobSq_rmatMul_ne_zero` — the {W=0}-null: for `QT ≠ 0`, `{F | frobSq(rmatMul F QT)=0}` is
  --     Lebesgue-null (via `ae_matrix_eval_ne_zero` on the (0,j₀)-entry polynomial).
  --   • `rmatMul_colReindex` — front column-perm = tail row-perm (the algebra of the reindex/h-invariance).
  --   • `frontStdEquivM` (+ `measurePreserving_frontStdEquivM`, `frontStdEquivM_apply`) — the standard
  --     front measure-equiv `(P,B₁₂) ≃ᵐ (Fin t → Fin M₁ → ℝ)`, pb ↦ [P|B₁₂] in STANDARD order.
  --   • `volume_shearbox_eq` — `vol(shearbox x) = vol(genBox)` (C-free, translation-invariant).
  -- REMAINING α-LOW plumbing (route fully resolved on paper; the residual is Lean cast-plumbing):
  --   STEP 1 (drop-corank): outerDom_lintegral_prod (split x=(pb,C)) + freedSchurLoss_inner_bounded_le
  --     (needs 0<W, a.e. by the {W=0}-null via `frontStdEquivM` MP + `ae_frobSq_rmatMul_ne_zero`, with a
  --     by_cases on Q=0 for the degenerate all-zero tail) + `volume_shearbox_eq` ⟹
  --     (TGT) ≤ (vol Cbox · vol genBox) · ∫_{A'} ∫_{pb∈outerPB} ofReal(W^{−c'}), W via
  --     `pivotEnergy_inverse_free` + `pivotEnergy_reindex_rmatMul`.
  --   STEP 2 (reindex to FC): `frontStdEquivM` CoV (outerPB ↔ wingFrontBox M'') + Tonelli + the h-column-
  --     perm-invariance (frontFactor_split + `rmatMul_colReindex` + a matBox row-reindex CoV) ⟹
  --     ∫_{A'}∫_{pb} ofReal(W^{−c'}) = `edge_frontCollapse_consFront_lt_top`'s integral < ⊤.
  --   WALL (reported, not faked): STEP 2's `frontStdEquivM ⁻¹' (wingFrontBox (Fin.cons t (tailChain M)))
  --     = outerPB` — the IsUnit(leadingBlock M'')↔IsUnit P direction — walls on the OPAQUE-WIDTH defeq
  --     `Fin ((Fin.cons t ·) 1) ≡ Fin (M 1)` (and `Fin (min (M''0)(M''1))`): the value-level index
  --     equalities (`hY`/`hX`) prove, but `rw`/`simp` cannot bridge the two syntactically-distinct-but-defeq
  --     width types for the cast-indexed `(frontStdEquiv).symm (castLE …)` in `leadingBlock`. This is the
  --     documented `Fin.cons`/`min` opaque-width friction (lean/CLAUDE.md). Needs either a value-transported
  --     `leadingBlock`-membership bridge or restating `edge_frontCollapse_consFront_lt_top` over a
  --     syntactic `Fin t → Fin (M 1)` front box.
  --   • α-HIGH (c' ≥ ½·minAdm(redChain t M)) — the a/2 corank charge = the heart's rank-1 (b=1) joint
  --     (Δ,C,Z) FreeBilinear leaf → hIH at c'−a/2, HELD (gated on the heart, jointpnp). NOT attempted.
  sorry

end DLNFibre.DLN.RLCT

