import DLNFibre.DLN.RLCT.Validate.RouteMSmearedBoxGen
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedFrontFactor
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedSquareL2

/-!
# `RouteMSmearedSquareGen` — the general-`L` Field-A entry bound `hSpre` (R2)

The general-`L` analog of the L=2 `condBox_subset_preimage` (`RouteMSmearedSquareL2`). Bounds every
decoded flat coord of `psiMapG (RmapG u)` by `ε` on the conditioned box `boxGen`, so the image lands in
`cubeBox ε` — discharging the Field-A containment `hSpre` that
`smearedChartDataGen_of_dets`/`smearedChartDataGen` take as an input.

The decode (`genDecode_params`) says `(paramsEquivFlat M).symm (psiMapG (RmapG u)) = chartGenParams …`,
so each flat coord is a `chartGenParams` entry. The three entry families:

* **front layers** `t ≠ deepLayer`: `frontTupleG u t i j = u (coordOfG (frontSlotG t i j))`, a direct
  box coord (`≤ δ`);
* **deep-bottom rows** `S_bot b j = u (coordOfG (botSlotG b j))`, a direct box coord (`≤ η`);
* **deep-top rows** `(z·H̄_unit − Λ₀·S_bot) a j`: the radial `z·H̄` (`≤ δ·1`) minus the shear
  `Λ₀·S_bot`. The shear is where the crux `Λ₀`-entry bound bites.

## The `Λ₀`-entry bound (the crux, decorrelated-Codex route 4)

`Λ₀ = (P₁ᵀP₁)⁻¹ P₁ᵀ P₂` with `P₁` **tall** (`M0 × r`, `M0 ≥ r`) — the L=2 square trick
`Λ₀ = P₁⁻¹P₂` is unavailable, and the tall Gram `P₁ᵀP₁` sums over the `M0−r` UNCONTROLLED front-product
rows, so a direct Varah bound on `P₁ᵀP₁` fails. Instead route through the width-`r` waist: `frontProd =
U·V` (`V : r × M⟨L−1⟩`, exactly `r` rows — the "first `r` rows only" limitation of `WideCarrierBound`
disappears). Then `Λ₀ = Vρ⁻¹·Vσ` (`gram_routing_eq_factor` + `front_factorsThrough_general`), and
`Vρ` is strictly row-dominant (a `WideCarrierBound` on the SUFFIX product `V`), so
`|Λ₀ a b| ≤ nb_V / γ_V = O(η)` (`StrictRowDominant.inv_mul_entry_bound`).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

open DLNFibre.Core.Matrix

variable {L : ℕ} {M : Fin (L + 1) → ℕ} {r s : ℕ}

/-- **The flat decode** `paramsEquivFlat H A (Fintype.equivFin (FlatIdx H) idx) = A idx.1.1 idx.1.2 idx.2`
(local copy of `DeepestFrameRaw.paramsEquivFlat_apply_equivFin`, to avoid the heavy import). -/
theorem paramsEquivFlat_apply_equivFin' (H : Fin (L + 1) → ℕ) (A : Params H) (idx : FlatIdx H) :
    paramsEquivFlat H A (Fintype.equivFin (FlatIdx H) idx) = A idx.1.1 idx.1.2 idx.2 := by
  unfold paramsEquivFlat
  erw [MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply]
  simp only [MeasurableEquiv.coe_piCurry_symm]
  erw [Equiv.arrowCongr_apply]
  simp only [Function.comp_apply]
  erw [Equiv.symm_apply_apply]
  rfl

/-! ## The suffix-product carrier bound (the shifted `wideCarrierBound_prodAux`)

`prodAux_split_exists` factors `prodAux M A k = prodAux M A p * Y`; here we build the SAME `Y` with a
`WideCarrierBound` on it. `Y` is the segment product `A^p·…·A^{k−1}`, a right-fold from the identity at
`k = p` (`wideCarrierBound_one`) advancing one `CarrierLayer` at a time (`wideCarrier_mul`). Mirrors
`wideCarrierBound_prodAux` with the endpoint shifted to start at `p`. -/

/-- **The suffix-product carrier bound (existence).** For `p ≤ k` with layers `p..k−1` each a
`CarrierLayer` and widths `≥ r` throughout `p..k`, there is a `Y` with `prodAux M A k = prodAux M A p * Y`
and a `WideCarrierBound Y r dlb nb pub` with the fused invariant (`nb ≤ η·Acc`,
`(δ/2)^{k−p} − η·Acc ≤ dlb`). The base `k = p` is `Y = 1`; each step right-multiplies a `CarrierLayer`. -/
theorem wideCarrierBound_suffix (A : Params M) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ)
    (p : ℕ) (hp : p < L + 1)
    (hwidth : ∀ t : ℕ, ∀ ht : t < L + 1, r ≤ M ⟨t, ht⟩)
    (hlayers : ∀ t : Fin L, p ≤ (t : ℕ) → (t : ℕ) < L - 1 → CarrierLayer (A t) r δ η) :
    ∀ (k : ℕ) (hpk : p ≤ k) (hkub : k ≤ L - 1) (hk : k < L + 1),
      ∃ (Y : Matrix (Fin (M ⟨p, hp⟩)) (Fin (M ⟨k, hk⟩)) ℝ) (dlb nb pub Acc : ℝ),
        prodAux M A k hk = prodAux M A p hp * Y
          ∧ WideCarrierBound Y r dlb nb pub
          ∧ 0 ≤ nb ∧ 0 ≤ pub ∧ 0 ≤ Acc
          ∧ nb ≤ η * Acc ∧ (δ / 2) ^ (k - p) - η * Acc ≤ dlb := by
  intro k hpk
  induction k, hpk using Nat.le_induction with
  | base =>
      intro _ hk
      -- base `k = p`: `Y = 1`, `prodAux p = prodAux p * 1`; `WideCarrierBound 1 r 1 0 1`
      refine ⟨1, 1, 0, 1, 0, (Matrix.mul_one _).symm, wideCarrierBound_one, le_refl _,
        by norm_num, le_refl _, by simp, ?_⟩
      simp
  | succ k hpk ih =>
      intro hkub hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hkub' : k ≤ L - 1 := by omega
      -- the folded layer `A^k` is a free front layer (`p ≤ k < L−1`)
      have hkLm1 : k < L - 1 := by omega
      obtain ⟨Y, dlb, nb, pub, Acc, hY, hWCB, hnb0, hpub0, hAcc0, hnbA, hdlbA⟩ :=
        ih hkub' hk'
      -- peel the last layer of the PARENT at index `k`
      have e1 : M (⟨k, hk'⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).castSucc) := by
        apply congrArg; apply Fin.ext; simp [Fin.castSucc]
      have e2 : M (⟨k + 1, hk⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).succ) := by
        apply congrArg; apply Fin.ext; simp [Fin.succ]
      rw [prodAux_succ M A k hk e1 e2, hY]
      set Alay := Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k, hkL⟩) with hAlay
      -- the reindexed layer is a CarrierLayer
      have hCL : CarrierLayer Alay r δ η :=
        carrierLayer_reindex (A ⟨k, hkL⟩) (hlayers ⟨k, hkL⟩ hpk hkLm1) e1.symm e2.symm
      -- the interface width `M ⟨k,_⟩ ≥ r`
      have hrw : r ≤ M (⟨k, hk'⟩ : Fin (L + 1)) := hwidth k hk'
      -- one composition step: `Y' = Y * Alay`
      have hstep := wideCarrier_mul hWCB hCL hpub0 hnb0 hη hηδ hrw
      refine ⟨Y * Alay, dlb * (δ / 2) - (M (⟨k, hk'⟩ : Fin (L + 1)) - 1 : ℕ) * pub * η,
        nb * δ + M (⟨k, hk'⟩ : Fin (L + 1)) * pub * η, M (⟨k, hk'⟩ : Fin (L + 1)) * pub * δ,
        δ * Acc + M (⟨k, hk'⟩ : Fin (L + 1)) * pub, ?_, hstep, ?_, ?_, ?_, ?_, ?_⟩
      · -- `prodAux p * (Y * Alay)`: reassociate
        rw [← Matrix.mul_assoc]
      · have : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        positivity
      · have : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        positivity
      · have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        have : (0:ℝ) ≤ δ * Acc := mul_nonneg (le_of_lt hδ) hAcc0
        positivity
      · -- `nb' ≤ η · Acc'`
        have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        have h1 : nb * δ ≤ η * (δ * Acc) := by
          nlinarith [hnbA, hδ.le, mul_le_mul_of_nonneg_right hnbA hδ.le]
        nlinarith [h1, mul_nonneg (mul_nonneg hM hpub0) hη]
      · -- `(δ/2)^{(k+1)−p} − η·Acc' ≤ dlb'`
        have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        have hwcast : ((M (⟨k, hk'⟩ : Fin (L + 1)) - 1 : ℕ) : ℝ)
            ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := by exact_mod_cast Nat.sub_le _ 1
        have hlow : ((δ / 2) ^ (k - p) - η * Acc) * (δ / 2) ≤ dlb * (δ / 2) :=
          mul_le_mul_of_nonneg_right hdlbA (by positivity)
        have hcross : ((M (⟨k, hk'⟩ : Fin (L + 1)) - 1 : ℕ) : ℝ) * pub * η
            ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) * pub * η :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwcast hpub0) hη
        have hexp : (δ / 2) ^ (k + 1 - p) = (δ / 2) ^ (k - p) * (δ / 2) := by
          rw [show k + 1 - p = (k - p) + 1 by omega, pow_succ]
        nlinarith [hlow, hcross, hexp, mul_nonneg (mul_nonneg hM hpub0) hη, hAcc0, hη, hδ.le]

/-! ## The flat-coord readoff `psiMapG (RmapG u) i = shearMBody … i` -/

/-- **`coordOfG (slotEquivG i) = i`** (the `slotEquivG`/`coordOfG` inverse round-trip). -/
theorem coordOfG_slotEquivG (M : Fin (L + 1) → ℕ) (i : Fin (routeMAmbient M)) :
    coordOfG M (slotEquivG M i) = i := by
  rw [coordOfG]; exact (slotEquivG M).symm_apply_apply i

/-- **The flat-coord readoff.** `psiMapG (RmapG u) i = shearMBody … (RmapG u) i` — the flat map is
`paramsEquivFlat ∘ packM ∘ shearMBody`, and `packM`/`paramsEquivFlat` cancel back to the shear value at
the coord `coordOfG (slotEquivG i) = i`. -/
theorem psiMapG_RmapG_flat (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) (i : Fin (routeMAmbient M)) :
    psiMapG M hL hrs (RmapG M hL hrs hr hc u) i
      = shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs) (RmapG M hL hrs hr hc u) i := by
  simp only [psiMapG]
  conv_lhs => rw [← Equiv.apply_symm_apply (Fintype.equivFin (FlatIdx M)) i]
  rw [paramsEquivFlat_apply_equivFin']
  rw [packM_shearG_entry M hL hrs (RmapG M hL hrs hr hc u) ((Fintype.equivFin (FlatIdx M)).symm i)]
  -- `coordOfG (slotEquivG i) = i`
  rw [show ((Fintype.equivFin (FlatIdx M)).symm i) = slotEquivG M i from rfl, coordOfG_slotEquivG]

/-! ## The `boxGen` readoff helpers (every non-pivot coord `∈ [−δ,δ]` when `η ≤ δ`) -/

/-- **A `boxGen` coord is `≤ δ` in absolute value** (`η ≤ δ`; both `Icc` branches lie in `[−δ,δ]`). -/
theorem boxGen_abs_le (hL : 0 < L) {q : FlatIdx M} {δ η : ℝ} (hδ : 0 < δ) (hη : η ≤ δ) {x : ℝ}
    (hx : x ∈ slotBoxGen M hL r δ η q) : |x| ≤ δ := by
  rw [slotBoxGen] at hx
  split at hx <;> · rw [Set.mem_Icc] at hx; rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

/-- **A non-carrier `boxGen` coord is `≤ η` in absolute value.** If the diagonal branch is not taken
(`q` not a front carrier-diagonal slot), the coord lies in `[−η,η]`. -/
theorem boxGen_abs_le_eta (hL : 0 < L) {q : FlatIdx M} {δ η : ℝ} {x : ℝ}
    (hnd : ¬ (q.1.1.val < L - 1 ∧ (q.1.2.val : ℕ) < r ∧ (q.2.val : ℕ) < r ∧ q.1.2.val = q.2.val))
    (hx : x ∈ slotBoxGen M hL r δ η q) : |x| ≤ η := by
  rw [slotBoxGen, if_neg hnd, Set.mem_Icc] at hx
  rw [abs_le]; exact hx

/-! ## The `Λ₀`-entry bound (route 4: `Λ₀ = Vρ⁻¹·Vσ`, `Vρ` dominant on the waist factor)

`frontProd = U·V` at the width-`r` waist `q` (`M⟨q⟩ = r`), with `V` the suffix product `A^q·…·A^{L−2}`
(exactly `r` rows after the cast). `WideCarrierBound V r` is an all-row statement, so:
* `Vρ := V[:, deepWidthEquiv∘inl]` (`r×r`) has carrier diagonal `≥ dlb`, off-diagonal `≤ nb`;
* `Vσ := V[:, deepWidthEquiv∘inr]` (`r×s`) has every entry `≤ nb` (residual cols are never carrier
  diagonals).
Then `Vρ` is `γ`-dominant (`γ = dlb − (r−1)·nb`), `Λ₀ = Vρ⁻¹·Vσ`, so `|Λ₀ a b| ≤ (1/γ)·nb`. -/

/-- **The waist carrier data.** From the suffix carrier bound at the width-`r` waist `q`, extract the
factorization `frontProd = U·V` (`V : r × M⟨L−1⟩` via the `Fin.cast M⟨q⟩=r`) together with a
`CarrierBound` on `Vρ := V[:, ρ]` and a uniform bound on `Vσ := V[:, σ]`, all with the fused
`nb ≤ η·Acc`, `(δ/2)^{L−1−q} − η·Acc ≤ dlb` invariant. -/
theorem waist_carrier_data (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ)
    (q : ℕ) (hq : q < L + 1) (hqL : q ≤ L - 1) (hMq : M ⟨q, hq⟩ = r)
    (hwidth : ∀ t : ℕ, ∀ ht : t < L + 1, r ≤ M ⟨t, ht⟩)
    (hlayers : ∀ t : Fin L, q ≤ (t : ℕ) → (t : ℕ) < L - 1 →
      CarrierLayer (frontTupleG M u t) r δ η) :
    ∃ (U : Matrix (Fin (M 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (M ⟨L - 1, by omega⟩)) ℝ)
      (dlb nb Acc : ℝ),
      frontProd M (frontTupleG M u) hL = U * V
        ∧ CarrierBound (V.submatrix (id : Fin r → Fin r)
            (fun k : Fin r => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k))) dlb nb
        ∧ (∀ i : Fin r, ∀ b : Fin s,
            |(V.submatrix (id : Fin r → Fin r)
              (fun j : Fin s => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr j))) i b| ≤ nb)
        ∧ 0 ≤ nb ∧ 0 ≤ Acc ∧ nb ≤ η * Acc
        ∧ (δ / 2) ^ (L - 1 - q) - η * Acc ≤ dlb := by
  -- suffix carrier bound `prodAux (L−1) = prodAux q * Y`, `WideCarrierBound Y r dlb nb pub`
  obtain ⟨Y, dlb, nb, pub, Acc, hY, hWCB, hnb0, _, hAcc0, hnbA, hdlbA⟩ :=
    wideCarrierBound_suffix (frontTupleG M u) hδ hη hηδ q hq hwidth hlayers (L - 1)
      hqL (le_refl _) (by omega)
  -- the recast `U := prodAux q · cast`, `V := cast · Y` (mirrors `frontProd_factorsThrough_waist`)
  refine ⟨(prodAux M (frontTupleG M u) q hq).submatrix (id : _ → _) (Fin.cast hMq.symm),
    Y.submatrix (Fin.cast hMq.symm) (id : _ → _), dlb, nb, Acc, ?_, ?_, ?_, hnb0, hAcc0, hnbA, ?_⟩
  · -- `frontProd = U · V`
    rw [frontProd, hY]
    funext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Fintype.sum_equiv (finCongr hMq)
      (fun a => (prodAux M (frontTupleG M u) q hq) i a * Y a j)
      (fun k => (prodAux M (frontTupleG M u) q hq).submatrix (id : _ → _) (Fin.cast hMq.symm) i k
        * Y.submatrix (Fin.cast hMq.symm) (id : _ → _) k j) (fun a => ?_)
    simp only [Matrix.submatrix_apply, id_eq, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  · -- `CarrierBound Vρ dlb nb`
    obtain ⟨hdiag, hnb, _⟩ := hWCB
    refine ⟨fun i => ?_, fun i k hik => ?_⟩
    · -- diagonal: `Vρ i i = Y (cast i) (deepWidthEquiv (inl i))`, both `.val = i < r`
      rw [Matrix.submatrix_apply, id_eq, Matrix.submatrix_apply, id_eq]
      refine hdiag (Fin.cast hMq.symm i) (by simp [Fin.cast])
        (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl i)) ?_
      simp only [Fin.coe_cast, deepWidthEquiv, Equiv.trans_apply, finCongr_apply, Fin.coe_cast,
        finSumFinEquiv_apply_left, Fin.coe_castAdd]
    · -- off-diagonal: `Vρ i k = Y (cast i) (deepWidthEquiv (inl k))`, `.val i ≠ .val k`
      rw [Matrix.submatrix_apply, id_eq, Matrix.submatrix_apply, id_eq]
      refine hnb (Fin.cast hMq.symm i) (by simp [Fin.cast])
        (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k)) ?_
      simp only [Fin.coe_cast, deepWidthEquiv, Equiv.trans_apply, finCongr_apply, Fin.coe_cast,
        finSumFinEquiv_apply_left, Fin.coe_castAdd]
      exact fun h => hik (Fin.ext h)
  · -- `Vσ` uniform bound: col `deepWidthEquiv (inr b)` has `.val = r + b ≥ r ≠ .val i (< r)`
    intro i b
    rw [Matrix.submatrix_apply, id_eq]
    obtain ⟨_, hnb, _⟩ := hWCB
    refine hnb (Fin.cast hMq.symm i) (by simp [Fin.cast])
      (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr b)) ?_
    simp only [Fin.coe_cast, deepWidthEquiv, Equiv.trans_apply, finCongr_apply, Fin.coe_cast,
      finSumFinEquiv_apply_right, Fin.coe_natAdd]
    omega
  · -- the invariant exponent `(δ/2)^{(L−1)−q}`
    exact hdlbA

/-- **The `Λ₀`-entry bound.** On the front-carrier box (`frontTupleG` layers are `CarrierLayer`s, small
`η`), with the Gram det `≠ 0`, every entry `|Lam0uG u a b| ≤ (1/γ)·nb` with `γ = dlb − (r−1)·nb`. Route
4: `Λ₀ = Vρ⁻¹·Vσ` (`front_factorsThrough_general` + `gram_routing_eq_factor`), `Vρ` is `γ`-dominant, so
the Varah `inv_mul_entry_bound` bites with the residual column bound `nb`. The existential returns
`γ, nb, Acc` so the box supplier can pick `η` to make `γ > 0`. -/
theorem Lam0uG_entry_bound (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ) (hr : 0 < r)
    (q : ℕ) (hq : q < L + 1) (hqL : q ≤ L - 1) (hMq : M ⟨q, hq⟩ = r)
    (hwidth : ∀ t : ℕ, ∀ ht : t < L + 1, r ≤ M ⟨t, ht⟩)
    (hlayers : ∀ t : Fin L, q ≤ (t : ℕ) → (t : ℕ) < L - 1 →
      CarrierLayer (frontTupleG M u t) r δ η)
    (hgram : ((P1uG M hL hrs u).transpose * P1uG M hL hrs u).det ≠ 0) :
    ∃ (γ nb Acc : ℝ), 0 ≤ nb ∧ 0 ≤ Acc ∧ nb ≤ η * Acc
      ∧ (((r : ℝ) - 1) * nb < (δ / 2) ^ (L - 1 - q) - η * Acc → 0 < γ)
      ∧ (0 < γ → ∀ a : Fin r, ∀ b : Fin s, |Lam0uG M hL hrs u a b| ≤ (1 / γ) * nb) := by
  obtain ⟨U, V, dlb, nb, Acc, hUV, hVρbound, hVσbound, hnb0, hAcc0, hnbA, hdlbA⟩ :=
    waist_carrier_data M hL hrs u hδ hη hηδ q hq hqL hMq hwidth hlayers
  set Vρ : Matrix (Fin r) (Fin r) ℝ := V.submatrix (id : Fin r → Fin r)
    (fun k : Fin r => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k)) with hVρdef
  set Vσ : Matrix (Fin r) (Fin s) ℝ := V.submatrix (id : Fin r → Fin r)
    (fun j : Fin s => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr j)) with hVσdef
  refine ⟨dlb - ((r : ℝ) - 1) * nb, nb, Acc, hnb0, hAcc0, hnbA, ?_, ?_⟩
  · -- `γ > 0` from `(r−1)·nb < (δ/2)^ℓ − η·Acc ≤ dlb`
    intro hsmall
    have : ((r : ℝ) - 1) * nb < dlb := lt_of_lt_of_le hsmall hdlbA
    linarith
  · -- the bound `|Λ₀ a b| ≤ (1/γ)·nb`
    intro hγpos a b
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    -- `Vρ` is `γ`-dominant, `γ = dlb − (↑r−1)·nb`
    have hdomlt : ((r : ℝ) - 1) * nb < dlb := by linarith [hγpos]
    have hSRD : StrictRowDominant Vρ (dlb - ((r : ℝ) - 1) * nb) :=
      hVρbound.strictRowDominant hdomlt
    -- `Λ₀ = Vρ⁻¹·Vσ` via `gram_routing_eq_factor` (Gram ≠ 0) + the factoring `P₂ = P₁·(Vρ⁻¹·Vσ)`
    have hVρdet : Vρ.det ≠ 0 := hSRD.det_ne_zero
    have hLamEq : Lam0uG M hL hrs u = Vρ⁻¹ * Vσ := by
      -- `P₁ = U·Vρ` (banked) and `P₂ = U·Vσ` (analogous column-select), so `P₂ = P₁·(Vρ⁻¹·Vσ)`
      have hP1 : P1uG M hL hrs u = U * Vρ := P1uG_eq_mul_Vrho hL hrs u U V hUV
      have hP2 : P2uG M hL hrs u = U * Vσ := by
        funext i j
        rw [P2uG, hUV, Matrix.mul_apply, Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun a _ => by rw [hVσdef, Matrix.submatrix_apply]; rfl)
      have hunitVρ : IsUnit Vρ.det := isUnit_iff_ne_zero.mpr hVρdet
      have hfac : P2uG M hL hrs u = P1uG M hL hrs u * (Vρ⁻¹ * Vσ) := by
        rw [hP2, hP1]
        calc U * Vσ = U * (1 : Matrix (Fin r) (Fin r) ℝ) * Vσ := by rw [Matrix.mul_one]
          _ = U * (Vρ * Vρ⁻¹) * Vσ := by rw [Matrix.mul_nonsing_inv _ hunitVρ]
          _ = U * Vρ * (Vρ⁻¹ * Vσ) := by simp only [Matrix.mul_assoc]
      rw [Lam0uG, hfac, gram_routing_eq_factor _ _ hgram]
    rw [hLamEq]
    -- Varah: `|Vρ⁻¹·Vσ a b| ≤ (1/γ)·nb`, γ = dlb − (r−1)·nb, column bound `nb`
    have hcol : ∀ i, |Vσ i b| ≤ nb := fun i => hVσbound i b
    exact hSRD.inv_mul_entry_bound Vσ b (Mj := nb) hcol a

/-! ## The deepest-slot box readoffs (`z`, `H̄_unit`, `S_bot` on `boxGen`)

A deepest-layer slot (`topSlotG`/`botSlotG`, layer `L−1`) is never a `slotBoxGen` carrier-diagonal
slot (that needs layer `< L−1`), so its coord lies in `[−η,η]`. The pivot `z` is `∈ Ioo 0 δ`. -/

/-- A deepest-top slot is not a `slotBoxGen` carrier-diagonal slot (it is at layer `L−1`). -/
theorem topSlotG_not_carrierDiag (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (a : Fin r) (j : Fin (M ((deepLayer hL).succ))) :
    ¬ ((topSlotG M hL hrs a j).1.1.val < L - 1 ∧
        ((topSlotG M hL hrs a j).1.2.val : ℕ) < r ∧ ((topSlotG M hL hrs a j).2.val : ℕ) < r
        ∧ (topSlotG M hL hrs a j).1.2.val = (topSlotG M hL hrs a j).2.val) := by
  rintro ⟨hlt, _, _, _⟩
  simp only [topSlotG, deepLayer] at hlt; omega

/-- A deepest-bottom slot is not a `slotBoxGen` carrier-diagonal slot (it is at layer `L−1`). -/
theorem botSlotG_not_carrierDiag (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (b : Fin s) (j : Fin (M ((deepLayer hL).succ))) :
    ¬ ((botSlotG M hL hrs b j).1.1.val < L - 1 ∧
        ((botSlotG M hL hrs b j).1.2.val : ℕ) < r ∧ ((botSlotG M hL hrs b j).2.val : ℕ) < r
        ∧ (botSlotG M hL hrs b j).1.2.val = (botSlotG M hL hrs b j).2.val) := by
  rintro ⟨hlt, _, _, _⟩
  simp only [botSlotG, deepLayer] at hlt; omega

/-- **`|z| ≤ δ`** on the box: the pivot value `z = u pivotCoordG ∈ Ioo 0 δ`. -/
theorem zuG_abs_le_of_box (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    {δ : ℝ} {u : Fin (routeMAmbient M) → ℝ}
    (hpivot : u (pivotCoordG M hL hrs hr hc) ∈ Set.Ioo (0 : ℝ) δ) :
    |zuG M hL hrs hr hc u| ≤ δ := by
  rw [zuG, abs_le]; rw [Set.mem_Ioo] at hpivot; constructor <;> linarith [hpivot.1, hpivot.2]

/-- **`|H̄_unit a j| ≤ 1`** on the box (`η ≤ 1`): the pivot entry is `1`, the others `∈ [−η,η]`. -/
theorem HbarUnitG_abs_le_of_box (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    {δ η : ℝ} (hη1 : η ≤ 1) {u : Fin (routeMAmbient M) → ℝ}
    (hrest : ∀ k, k ≠ pivotCoordG M hL hrs hr hc → u k ∈ boxGen M hL r δ η k)
    (a : Fin r) (j : Fin (M ((deepLayer hL).succ))) :
    |HbarUnitG M hL hrs hr hc u a j| ≤ 1 := by
  rw [HbarUnitG]
  by_cases hpiv : coordOfG M (topSlotG M hL hrs a j) = pivotCoordG M hL hrs hr hc
  · rw [if_pos hpiv]; norm_num
  · rw [if_neg hpiv]
    have hval := hrest (coordOfG M (topSlotG M hL hrs a j)) hpiv
    rw [boxGen_coordOfG] at hval
    exact le_trans (boxGen_abs_le_eta hL (topSlotG_not_carrierDiag M hL hrs a j) hval) hη1

/-- **`|S_bot b j| ≤ η`** on the box (a deepest-bottom slot is `∈ [−η,η]`). -/
theorem SbotuG_abs_le_of_box (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    {δ η : ℝ} {u : Fin (routeMAmbient M) → ℝ}
    (hrest : ∀ k, k ≠ pivotCoordG M hL hrs hr hc → u k ∈ boxGen M hL r δ η k)
    (hbotne : ∀ b : Fin s, ∀ j : Fin (M ((deepLayer hL).succ)),
      coordOfG M (botSlotG M hL hrs b j) ≠ pivotCoordG M hL hrs hr hc)
    (b : Fin s) (j : Fin (M ((deepLayer hL).succ))) :
    |SbotuG M hL hrs u b j| ≤ η := by
  have hval := hrest (coordOfG M (botSlotG M hL hrs b j)) (hbotne b j)
  rw [boxGen_coordOfG] at hval
  exact boxGen_abs_le_eta hL (botSlotG_not_carrierDiag M hL hrs b j) hval

/-! ## The flat-coord entry bound (each `|psiMapG (RmapG u) i| ≤ ε`) -/

/-- **The top-slot decode value.** At a top-slot coord, `psiMapG (RmapG u) = (z•H̄ − Λ₀·S_bot) a j`. -/
theorem psiMapG_RmapG_topSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) (a : Fin r) (j : Fin (M ((deepLayer hL).succ))) :
    psiMapG M hL hrs (RmapG M hL hrs hr hc u) (coordOfG M (topSlotG M hL hrs a j))
      = (zuG M hL hrs hr hc u • HbarUnitG M hL hrs hr hc u
          - Lam0uG M hL hrs u * SbotuG M hL hrs u) a j := by
  rw [psiMapG_RmapG_flat, shearG_topSlotG]

/-- **The deep-top entry bound.** `|(z•H̄ − Λ₀·S_bot) a j| ≤ δ + s·((1/γ)·nb)·η` on the box: the radial
`|z·H̄| ≤ δ·1`, the shear `|(Λ₀·S_bot) a j| ≤ ∑_b |Λ₀ a b|·|S_bot b j| ≤ s·((1/γ)·nb)·η`. -/
theorem deepTopG_entry_le_of_box (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    {δ η γ nb : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) (hη1 : η ≤ 1) (hηpos : 0 ≤ η) (hnb0 : 0 ≤ nb)
    {u : Fin (routeMAmbient M) → ℝ}
    (hpivot : u (pivotCoordG M hL hrs hr hc) ∈ Set.Ioo (0 : ℝ) δ)
    (hrest : ∀ k, k ≠ pivotCoordG M hL hrs hr hc → u k ∈ boxGen M hL r δ η k)
    (hbotne : ∀ b : Fin s, ∀ j : Fin (M ((deepLayer hL).succ)),
      coordOfG M (botSlotG M hL hrs b j) ≠ pivotCoordG M hL hrs hr hc)
    (hLam : ∀ a : Fin r, ∀ b : Fin s, |Lam0uG M hL hrs u a b| ≤ (1 / γ) * nb)
    (a : Fin r) (j : Fin (M ((deepLayer hL).succ))) :
    |(zuG M hL hrs hr hc u • HbarUnitG M hL hrs hr hc u
        - Lam0uG M hL hrs u * SbotuG M hL hrs u) a j|
      ≤ δ + (s : ℝ) * ((1 / γ) * nb) * η := by
  -- radial term `|z·H̄| ≤ δ·1 = δ`
  have hz := zuG_abs_le_of_box M hL hrs hr hc hpivot
  have hH := HbarUnitG_abs_le_of_box M hL hrs hr hc hη1 hrest a j
  have hrad : |zuG M hL hrs hr hc u * HbarUnitG M hL hrs hr hc u a j| ≤ δ := by
    rw [abs_mul]
    calc |zuG M hL hrs hr hc u| * |HbarUnitG M hL hrs hr hc u a j|
        ≤ δ * 1 := mul_le_mul hz hH (abs_nonneg _) hδ.le
      _ = δ := by ring
  -- shear term `|(Λ₀·S_bot) a j| ≤ s·((1/γ)·nb)·η`
  have hshear : |(Lam0uG M hL hrs u * SbotuG M hL hrs u) a j| ≤ (s : ℝ) * ((1 / γ) * nb) * η := by
    rw [Matrix.mul_apply]
    calc |∑ b, Lam0uG M hL hrs u a b * SbotuG M hL hrs u b j|
        ≤ ∑ b, |Lam0uG M hL hrs u a b * SbotuG M hL hrs u b j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b : Fin s, ((1 / γ) * nb) * η := by
          refine Finset.sum_le_sum (fun b _ => ?_)
          rw [abs_mul]
          refine mul_le_mul (hLam a b)
            (SbotuG_abs_le_of_box M hL hrs hr hc hrest hbotne b j) (abs_nonneg _) ?_
          positivity
      _ = (s : ℝ) * ((1 / γ) * nb) * η := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- combine via the triangle inequality
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc |zuG M hL hrs hr hc u * HbarUnitG M hL hrs hr hc u a j
          - (Lam0uG M hL hrs u * SbotuG M hL hrs u) a j|
      ≤ |zuG M hL hrs hr hc u * HbarUnitG M hL hrs hr hc u a j|
          + |(Lam0uG M hL hrs u * SbotuG M hL hrs u) a j| := abs_sub _ _
    _ ≤ δ + (s : ℝ) * ((1 / γ) * nb) * η := by linarith [hrad, hshear]

/-- **The flat-coord entry bound `|psiMapG (RmapG u) i| ≤ 2δ`.** Classify the coord `i`:
* `i ∈ topCoordsG` (a top slot `coordOfG (topSlotG a j)`): the deep-top entry, `≤ δ + s·((1/γ)nb)·η ≤ 2δ`
  under the field-A margin `s·((1/γ)nb)·η ≤ δ`;
* `i ∉ topCoordsG` (a front OR bottom slot, `psiMapG (RmapG u) i = u i`): a box coord, `≤ δ ≤ 2δ`. -/
theorem psiMapG_RmapG_flat_le (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    {δ η γ nb : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) (hη : η ≤ δ) (hη1 : η ≤ 1) (hηpos : 0 ≤ η)
    (hnb0 : 0 ≤ nb) (hfieldA : (s : ℝ) * ((1 / γ) * nb) * η ≤ δ)
    {u : Fin (routeMAmbient M) → ℝ}
    (hpivot : u (pivotCoordG M hL hrs hr hc) ∈ Set.Ioo (0 : ℝ) δ)
    (hrest : ∀ k, k ≠ pivotCoordG M hL hrs hr hc → u k ∈ boxGen M hL r δ η k)
    (hbotne : ∀ b : Fin s, ∀ j : Fin (M ((deepLayer hL).succ)),
      coordOfG M (botSlotG M hL hrs b j) ≠ pivotCoordG M hL hrs hr hc)
    (hLam : ∀ a : Fin r, ∀ b : Fin s, |Lam0uG M hL hrs u a b| ≤ (1 / γ) * nb)
    (i : Fin (routeMAmbient M)) :
    |psiMapG M hL hrs (RmapG M hL hrs hr hc u) i| ≤ 2 * δ := by
  by_cases hmem : i ∈ topCoordsG M hL hrs
  · -- TOP slot: the deep-top entry `≤ δ + s·((1/γ)nb)·η ≤ 2δ`
    obtain ⟨a, j, hij⟩ := (mem_topCoordsG_iff M hL hrs i).mp hmem
    rw [← hij, psiMapG_RmapG_topSlotG]
    have := deepTopG_entry_le_of_box M hL hrs hr hc hδ hγ hη1 hηpos hnb0 hpivot hrest hbotne hLam a j
    linarith [hfieldA]
  · -- SPECTATOR (front/bottom): `psiMapG (RmapG u) i = u i`, a box coord `≤ δ ≤ 2δ`
    have hval : psiMapG M hL hrs (RmapG M hL hrs hr hc u) i = u i := by
      rw [psiMapG_RmapG_flat, shearMBody_apply_of_not_mem _ _ _ hmem,
        RmapG_spectator M hL hrs hr hc u hmem]
    rw [hval]
    -- `i ≠ pivot` (pivot ∈ topCoordsG), so `u i ∈ boxGen i`, `≤ δ`
    have hine : i ≠ pivotCoordG M hL hrs hr hc :=
      fun h => hmem (h ▸ pivotCoordG_mem M hL hrs hr hc)
    have hbox := hrest i hine
    rw [boxGen] at hbox
    have := boxGen_abs_le hL hδ hη hbox
    linarith

/-! ## The Field-A containment `hSpre` (`condBox ⊆ (ψ∘R)⁻¹(cubeBox 2δ)`) -/

/-- **The general-`L` Field-A containment (`ε = 2δ`).** On the conditioned box `boxGen` (pivot in
`Ioo 0 δ`, front carrier-diagonals in `[δ/2,δ]`, everything else in `[−η,η]`), the decoded image lands
in `cubeBox 2δ`: every flat coord `|psiMapG (RmapG u) i| ≤ 2δ` (`psiMapG_RmapG_flat_le`). Takes the
`Λ₀`-entry bound `hLam` (from `Lam0uG_entry_bound` off small `η`) and the field-A margin
`s·((1/γ)nb)·η ≤ δ` as inputs — both discharged by the box supplier's `η`-choice. The general-`L`
analog of the L=2 `condBox_subset_preimage`. -/
theorem condBox_subset_preimage_gen (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    {δ η γ nb : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) (hη : η ≤ δ) (hη1 : η ≤ 1) (hηpos : 0 ≤ η)
    (hnb0 : 0 ≤ nb) (hfieldA : (s : ℝ) * ((1 / γ) * nb) * η ≤ δ)
    (hbotne : ∀ b : Fin s, ∀ j : Fin (M ((deepLayer hL).succ)),
      coordOfG M (botSlotG M hL hrs b j) ≠ pivotCoordG M hL hrs hr hc)
    (hLam : ∀ (u : Fin (routeMAmbient M) → ℝ),
      u ∈ condBox (pivotCoordG M hL hrs hr hc) (boxGen M hL r δ η) δ →
      ∀ a : Fin r, ∀ b : Fin s, |Lam0uG M hL hrs u a b| ≤ (1 / γ) * nb) :
    condBox (pivotCoordG M hL hrs hr hc) (boxGen M hL r δ η) δ
      ⊆ (fun u => psiMapG M hL hrs (RmapG M hL hrs hr hc u))
        ⁻¹' (cubeBox (routeMAmbient M) (2 * δ)) := by
  intro u hu
  rw [Set.mem_preimage, cubeBox, Set.mem_pi]
  intro i _
  rw [Set.mem_Icc, ← abs_le]
  exact psiMapG_RmapG_flat_le M hL hrs hr hc hδ hγ hη hη1 hηpos hnb0 hfieldA hu.1
    (fun k hk => hu.2 k hk) hbotne (hLam u hu) i

end DLNFibre.DLN.RLCT
