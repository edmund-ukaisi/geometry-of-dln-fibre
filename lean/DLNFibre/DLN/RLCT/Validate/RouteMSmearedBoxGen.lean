import DLNFibre.Core.Matrix.CarrierBlock
import DLNFibre.Core.Matrix.GramFullRank
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedDetData

/-!
# `RouteMSmearedBoxGen` — the front-product carrier block is strictly dominant on `boxGen`

Connects the abstract carrier-block engine (`Core.Matrix.CarrierBlock` / `GramFullRank`) to the
`frontProd`/`P1uG` machinery: the general-`L` box supplier for the smeared chart.

The chain product `frontProd M A hL = prodAux M A (L−1)` folds the front layers `A⁰·…·A^{L−2}`. When
every front layer is a `CarrierLayer` (carrier `r×r` diagonal `∈ [δ/2, δ]`, every other entry `≤ η`,
the `boxGen` conditioning), the abstract one-step composition `wideCarrier_mul` iterates over the
`prodAux` fold to give a `WideCarrierBound` on `frontProd`, hence a `CarrierBound` on its carrier
`r×r` block, hence a nonzero `r×r` minor of `P₁` — the Gram det (`hGram`/`hGram0`) via
`gram_det_ne_zero_of_submatrix_det_ne`, and `hWaist` as its corollary.

* `carrierLayer_reindex` — a `CarrierLayer` survives the `finCongr` recast (`.val`-preserving).
* `wideCarrierBound_prodAux` — the iteration: a per-layer `CarrierLayer` hypothesis on the front
  layers gives a `WideCarrierBound` on `prodAux M A k` (induction on `k`).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

open DLNFibre.Core.Matrix

variable {L : ℕ} {M : Fin (L + 1) → ℕ} {r : ℕ}

/-- **`CarrierLayer` survives a `finCongr` recast.** Reindexing a carrier layer by width equalities
(`finCongr e.symm` on rows/cols) preserves the carrier structure — `finCongr` is `.val`-preserving,
so the carrier-diagonal/off-diagonal classification is unchanged. -/
theorem carrierLayer_reindex {w w' v v' : ℕ} (A : Matrix (Fin w) (Fin w') ℝ) {δ η : ℝ}
    (hA : CarrierLayer A r δ η) (e1 : v = w) (e2 : v' = w') :
    CarrierLayer (Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) A) r δ η := by
  subst e1; subst e2
  simpa only [finCongr_refl, Matrix.reindex_refl_refl, Equiv.refl_symm] using hA

/-- The `WideCarrierBound` of the identity `m₀ × m₀` matrix (`prodAux … 0`), carrier corridor first
`r`: on the carrier rows (`i < r`) the diagonal `= 1`, off-diagonal `= 0`, global bound `1`. -/
theorem wideCarrierBound_one {m₀ : ℕ} :
    WideCarrierBound (1 : Matrix (Fin m₀) (Fin m₀) ℝ) r 1 0 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i _ j hij
    rw [show j = i from Fin.ext hij.symm, Matrix.one_apply_eq]; simp
  · intro i _ j hji
    rw [Matrix.one_apply_ne (fun h => hji (by rw [h]))]; simp
  · intro i _ j
    by_cases h : i = j
    · rw [h, Matrix.one_apply_eq]; simp
    · rw [Matrix.one_apply_ne h]; simp

/-- **The iterated composition invariant** (`Core` engine over the `prodAux` fold). For a `Params`
tuple whose layers `0..k−1` are each `CarrierLayer`s, the carrier `r × r` block of `prodAux M A k`
satisfies a `WideCarrierBound dlb nb pub` with the fused-constant invariant carried existentially:

* `nb ≤ η · Acc`,
* `dlb ≥ (δ/2)^k − η · Acc`,   `Acc ≥ 0`, `0 ≤ nb`, `0 ≤ pub`,

so the carrier block is strictly dominant once `η` is small (`(r−1)·nb < dlb`). The per-step algebra
is the banked `wideCarrier_mul`; the running `Acc` absorbs the growing `pub`. Requires every width
`r ≤ M ⟨t,_⟩` (the carrier corridor fits) — supplied by the waist decomposition downstream. -/
theorem wideCarrierBound_prodAux (A : Params M) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ)
    (hwidth : ∀ t : ℕ, ∀ ht : t < L + 1, r ≤ M ⟨t, ht⟩)
    (hlayers : ∀ t : Fin L, (t : ℕ) < L - 1 → CarrierLayer (A t) r δ η) :
    ∀ (k : ℕ) (hk : k < L), ∀ hk1 : k < L + 1,
      ∃ (dlb nb pub Acc : ℝ),
        WideCarrierBound (prodAux M A k hk1) r dlb nb pub
          ∧ 0 ≤ nb ∧ 0 ≤ pub ∧ 0 ≤ Acc
          ∧ nb ≤ η * Acc ∧ (δ / 2) ^ k - η * Acc ≤ dlb := by
  intro k
  induction k with
  | zero =>
      intro hkL hk
      -- base: `prodAux 0 = 1`, invariant with `dlb = 1, nb = 0, pub = 1, Acc = 0`
      refine ⟨1, 0, 1, 0, ?_, le_refl _, by norm_num, le_refl _, by simp, ?_⟩
      · show WideCarrierBound (prodAux M A 0 hk) r 1 0 1
        exact wideCarrierBound_one
      · simp
  | succ k ih =>
      intro hkLsucc hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      -- `k+1 < L` gives `k < L−1` (the folded layer `⟨k⟩` is a free front layer)
      have hkLm1 : k < L - 1 := by omega
      obtain ⟨dlb, nb, pub, Acc, hWCB, hnb0, hpub0, hAcc0, hnbA, hdlbA⟩ := ih hkL hk'
      -- peel the last layer
      have e1 : M (⟨k, hk'⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).castSucc) := by
        apply congrArg; apply Fin.ext; simp [Fin.castSucc]
      have e2 : M (⟨k + 1, hk⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).succ) := by
        apply congrArg; apply Fin.ext; simp [Fin.succ]
      rw [prodAux_succ M A k hk e1 e2]
      set Alay := Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k, hkL⟩) with hAlay
      -- the reindexed layer is a CarrierLayer
      have hCL : CarrierLayer Alay r δ η :=
        carrierLayer_reindex (A ⟨k, hkL⟩) (hlayers ⟨k, hkL⟩ hkLm1) e1.symm e2.symm
      -- the width `M ⟨k,_⟩ ≥ r` so the carrier corridor fits
      have hrw : r ≤ M (⟨k, hk'⟩ : Fin (L + 1)) := hwidth k hk'
      -- one composition step
      have hstep := wideCarrier_mul hWCB hCL hpub0 hnb0 hη hηδ hrw
      -- new constants
      refine ⟨dlb * (δ / 2) - (M (⟨k, hk'⟩ : Fin (L + 1)) - 1 : ℕ) * pub * η,
        nb * δ + M (⟨k, hk'⟩ : Fin (L + 1)) * pub * η, M (⟨k, hk'⟩ : Fin (L + 1)) * pub * δ,
        δ * Acc + M (⟨k, hk'⟩ : Fin (L + 1)) * pub, hstep, ?_, ?_, ?_, ?_, ?_⟩
      · -- `0 ≤ nb'`
        have : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        positivity
      · -- `0 ≤ pub'`
        have : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        positivity
      · -- `0 ≤ Acc'`
        have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        have : (0:ℝ) ≤ δ * Acc := mul_nonneg (le_of_lt hδ) hAcc0
        positivity
      · -- `nb' ≤ η · Acc'`:  `nb·δ + w·pub·η ≤ η·(δ·Acc + w·pub)`
        have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        have h1 : nb * δ ≤ η * (δ * Acc) := by
          nlinarith [hnbA, hδ.le, mul_le_mul_of_nonneg_right hnbA hδ.le]
        nlinarith [h1, mul_nonneg (mul_nonneg hM hpub0) hη]
      · -- `(δ/2)^{k+1} − η·Acc' ≤ dlb'`
        have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        -- `dlb' = dlb·(δ/2) − (w−1)·pub·η ≥ ((δ/2)^k − η·Acc)·(δ/2) − w·pub·η`
        have hwcast : ((M (⟨k, hk'⟩ : Fin (L + 1)) - 1 : ℕ) : ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := by
          exact_mod_cast Nat.sub_le _ 1
        have hlow : ((δ / 2) ^ k - η * Acc) * (δ / 2) ≤ dlb * (δ / 2) :=
          mul_le_mul_of_nonneg_right hdlbA (by positivity)
        have hcross : ((M (⟨k, hk'⟩ : Fin (L + 1)) - 1 : ℕ) : ℝ) * pub * η
            ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) * pub * η :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwcast hpub0) hη
        have hexp : (δ / 2) ^ (k + 1) = (δ / 2) ^ k * (δ / 2) := by rw [pow_succ]
        nlinarith [hlow, hcross, hexp, mul_nonneg (mul_nonneg hM hpub0) hη, hAcc0, hη, hδ.le]

/-- **The dominance closer.** From the iteration's fused invariant `nb ≤ η·Acc`,
`(δ/2)^{L−1} − η·Acc ≤ dlb` with `Acc ≥ 0`, `nb ≥ 0`, a small-`η` bound
`η·Acc·r < (δ/2)^{L−1}` gives strict carrier dominance `(r−1)·nb < dlb`. (The `r` absorbs both the
`(r−1)·nb ≤ r·η·Acc` off-sum and the `η·Acc` diagonal deficit.) -/
theorem dominance_of_small_eta {δ η dlb nb Acc : ℝ} (hr : 0 < r) (hη : 0 ≤ η) (hAcc0 : 0 ≤ Acc)
    (hnb0 : 0 ≤ nb) (hnbA : nb ≤ η * Acc) (hdlbA : (δ / 2) ^ (L - 1) - η * Acc ≤ dlb)
    (hsmall : (r : ℝ) * (η * Acc) < (δ / 2) ^ (L - 1)) :
    (r - 1 : ℝ) * nb < dlb := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  -- `(r−1)·nb ≤ (r−1)·η·Acc ≤ r·η·Acc`; `dlb ≥ (δ/2)^{L−1} − η·Acc > (r−1)·η·Acc`
  have h1 : (r - 1 : ℝ) * nb ≤ (r - 1 : ℝ) * (η * Acc) :=
    mul_le_mul_of_nonneg_left hnbA (by linarith)
  have hηAcc : 0 ≤ η * Acc := mul_nonneg hη hAcc0
  nlinarith [h1, hdlbA, hsmall, hηAcc, hr1]

/-- **The front-product carrier block is strictly dominant** (`det ≠ 0`), packaging the iteration.
Returns the existential running-constant `Acc ≥ 0` alongside a proof that, IF the small-`η` bound
`r·η·Acc < (δ/2)^{L−1}` holds, the carrier `r × r` block of `prodAux M A (L−1)` has nonzero
determinant. The box supplier reads off `Acc` and picks `η` accordingly. -/
theorem carrierBlock_prodAux_det_ne (A : Params M) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ)
    (hL : 0 < L) (hr : 0 < r) (hr0 : r ≤ M 0) (hrL : r ≤ M (⟨L - 1, by omega⟩ : Fin (L + 1)))
    (hwidth : ∀ t : ℕ, ∀ ht : t < L + 1, r ≤ M ⟨t, ht⟩)
    (hlayers : ∀ t : Fin L, (t : ℕ) < L - 1 → CarrierLayer (A t) r δ η) :
    ∃ Acc : ℝ, 0 ≤ Acc ∧ ((r : ℝ) * (η * Acc) < (δ / 2) ^ (L - 1) →
      (Matrix.of (fun i j : Fin r => prodAux M A (L - 1) (by omega)
        ⟨i, lt_of_lt_of_le i.isLt hr0⟩ ⟨j, lt_of_lt_of_le j.isLt hrL⟩)).det ≠ 0) := by
  obtain ⟨dlb, nb, pub, Acc, hWCB, hnb0, hpub0, hAcc0, hnbA, hdlbA⟩ :=
    wideCarrierBound_prodAux A hδ hη hηδ hwidth hlayers (L - 1) (by omega) (by omega)
  refine ⟨Acc, hAcc0, fun hsmall => ?_⟩
  have hdom := dominance_of_small_eta hr hη hAcc0 hnb0 hnbA hdlbA hsmall
  exact (hWCB.carrierBlock hr0 hrL).det_ne_zero hdom

/-! ## The Gram determinant `hGram`/`hGram0` from the carrier-block det -/

/-- **The `P1uG` carrier `r×r` minor is the `frontProd` carrier block.** `P1uG u i k =
frontProd (frontTupleG u) i (deepWidthEquiv(inl k))`, and `deepWidthEquiv(inl k)` has `.val = k`, so
selecting the first `r` rows and columns `deepWidthEquiv(inl)` gives exactly the first-`r×r` block of
`frontProd = prodAux (L−1)`. -/
theorem P1uG_submatrix_eq_carrierBlock (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ)
    (hr0 : r ≤ M 0) (hrL : r ≤ M (⟨L - 1, by omega⟩ : Fin (L + 1)))
    (i j : Fin r) :
    (P1uG M hL hrs u).submatrix (fun a : Fin r => (⟨a, lt_of_lt_of_le a.isLt hr0⟩ : Fin (M 0)))
        (id : Fin r → Fin r) i j
      = prodAux M (frontTupleG M u) (L - 1) (by omega)
          ⟨i, lt_of_lt_of_le i.isLt hr0⟩ ⟨j, lt_of_lt_of_le j.isLt hrL⟩ := by
  rw [Matrix.submatrix_apply, id_eq, P1uG, frontProd]
  -- the column `deepWidthEquiv(inl j)` equals `⟨j,_⟩` (val-preserving)
  have hcol : deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl j)
      = (⟨j, lt_of_lt_of_le j.isLt hrL⟩ : Fin (M (⟨L - 1, by omega⟩ : Fin (L + 1)))) := by
    apply Fin.ext
    simp [deepWidthEquiv, finSumFinEquiv_apply_left]
  rw [hcol]

/-- **`hGram` from the front-layer carrier structure.** When `frontTupleG u`'s layers are
`CarrierLayer`s and `η` is small, the Gram `det ((P1uG u)ᵀ P1uG u) ≠ 0` — `P₁`'s carrier `r×r` minor
(the `frontProd` carrier block) is nonzero (`carrierBlock_prodAux_det_ne`), so `P₁` has full column
rank (`gram_det_ne_zero_of_submatrix_det_ne`). -/
theorem gram_det_ne_of_carrierLayers (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ) (hr : 0 < r)
    (hr0 : r ≤ M 0) (hrL : r ≤ M (⟨L - 1, by omega⟩ : Fin (L + 1)))
    (hwidth : ∀ t : ℕ, ∀ ht : t < L + 1, r ≤ M ⟨t, ht⟩)
    (hlayers : ∀ t : Fin L, (t : ℕ) < L - 1 → CarrierLayer (frontTupleG M u t) r δ η) :
    ∃ Acc : ℝ, 0 ≤ Acc ∧ ((r : ℝ) * (η * Acc) < (δ / 2) ^ (L - 1) →
      ((P1uG M hL hrs u).transpose * P1uG M hL hrs u).det ≠ 0) := by
  obtain ⟨Acc, hAcc0, hclose⟩ :=
    carrierBlock_prodAux_det_ne (frontTupleG M u) hδ hη hηδ hL hr hr0 hrL hwidth hlayers
  refine ⟨Acc, hAcc0, fun hsmall => ?_⟩
  refine gram_det_ne_zero_of_submatrix_det_ne (P1uG M hL hrs u)
    (fun a : Fin r => (⟨a, lt_of_lt_of_le a.isLt hr0⟩ : Fin (M 0))) (id : Fin r → Fin r) ?_
  -- the submatrix det = the carrier-block det (entrywise equal matrices)
  have hEq : (P1uG M hL hrs u).submatrix
      (fun a : Fin r => (⟨a, lt_of_lt_of_le a.isLt hr0⟩ : Fin (M 0))) (id : Fin r → Fin r)
      = Matrix.of (fun i j : Fin r => prodAux M (frontTupleG M u) (L - 1) (by omega)
          ⟨i, lt_of_lt_of_le i.isLt hr0⟩ ⟨j, lt_of_lt_of_le j.isLt hrL⟩) := by
    funext i j
    exact P1uG_submatrix_eq_carrierBlock hL hrs u hr0 hrL i j
  rw [hEq]
  exact hclose hsmall

/-! ## `boxGen` — the slot-level conditioned box (front carrier diagonal near-`δ`, rest small) -/

/-- **The general-`L` slot-level box.** `[δ/2, δ]` on a FRONT carrier-diagonal slot (`frontSlotG t i j`
with `(i:ℕ) = (j:ℕ) < r` at a free front layer `t.val < L−1`), `[−η, η]` on every other slot. The
box231-generalization: it conditions the front carrier `r×r` diagonals near `δ` and everything else
(front off-carrier, deep-top, deep-bottom) small. The radial/pivot coords are `[−η, η]` here (their
radial handling is separate in the chart). -/
noncomputable def slotBoxGen (M : Fin (L + 1) → ℕ) (hL : 0 < L) (r : ℕ) (δ η : ℝ)
    (q : FlatIdx M) : Set ℝ :=
  if (q.1.1.val < L - 1 ∧ (q.1.2.val : ℕ) < r ∧ (q.2.val : ℕ) < r ∧ q.1.2.val = q.2.val)
  then Set.Icc (δ / 2) δ else Set.Icc (-η) η

/-- The ambient `boxGen`: `slotBoxGen` precomposed with `slotEquivG`. -/
noncomputable def boxGen (M : Fin (L + 1) → ℕ) (hL : 0 < L) (r : ℕ) (δ η : ℝ) :
    Fin (routeMAmbient M) → Set ℝ :=
  fun m => slotBoxGen M hL r δ η (slotEquivG M m)

/-- The slot-level readoff `boxGen (coordOfG q) = slotBoxGen q` (the `slotEquivG` round-trip). -/
theorem boxGen_coordOfG (M : Fin (L + 1) → ℕ) (hL : 0 < L) (r : ℕ) (δ η : ℝ) (q : FlatIdx M) :
    boxGen M hL r δ η (coordOfG M q) = slotBoxGen M hL r δ η q := by
  unfold boxGen coordOfG
  rw [Equiv.apply_symm_apply]

/-- Each `boxGen` width is measurable (both branches are `Icc`). -/
theorem measurableSet_boxGen (M : Fin (L + 1) → ℕ) (hL : 0 < L) (r : ℕ) (δ η : ℝ)
    (m : Fin (routeMAmbient M)) : MeasurableSet (boxGen M hL r δ η m) := by
  unfold boxGen slotBoxGen
  split <;> exact measurableSet_Icc

/-- **The front layers of `frontTupleG u` are `CarrierLayer`s on `boxGen`.** For a point `u` whose
front-slot coords lie in `boxGen` (`u (coordOfG (frontSlotG t i j)) ∈ boxGen …`), each free front
layer `t.val < L−1` of `frontTupleG M u` is a `CarrierLayer r δ η`: the carrier diagonal `i = j < r`
lands in `[δ/2, δ]` (the `slotBoxGen` diagonal branch), every other entry in `[−η, η]`. -/
theorem frontTupleG_carrierLayer_of_boxGen (M : Fin (L + 1) → ℕ) (hL : 0 < L) (r : ℕ) {δ η : ℝ}
    (u : Fin (routeMAmbient M) → ℝ)
    (hu : ∀ t : Fin L, ∀ i : Fin (M t.castSucc), ∀ j : Fin (M t.succ),
      u (coordOfG M (frontSlotG M t i j)) ∈ slotBoxGen M hL r δ η (frontSlotG M t i j))
    (t : Fin L) (ht : (t : ℕ) < L - 1) :
    CarrierLayer (frontTupleG M u t) r δ η := by
  constructor
  · -- carrier diagonal `(i:ℕ) = (j:ℕ) < r` lands in `[δ/2, δ]`
    intro i j hij hir
    have hmem := hu t i j
    -- `frontSlotG t i j = ⟨⟨t,i⟩,j⟩`; the diagonal branch condition holds
    have hbranch : ((frontSlotG M t i j).1.1.val < L - 1 ∧ ((frontSlotG M t i j).1.2.val : ℕ) < r
        ∧ ((frontSlotG M t i j).2.val : ℕ) < r ∧ (frontSlotG M t i j).1.2.val
          = (frontSlotG M t i j).2.val) := by
      refine ⟨ht, ?_, ?_, ?_⟩ <;> simp only [frontSlotG] <;> omega
    rw [slotBoxGen, if_pos hbranch] at hmem
    show u (coordOfG M (frontSlotG M t i j)) ∈ Set.Icc (δ / 2) δ
    exact hmem
  · -- every other entry `≤ η` (the `[−η, η]` branch)
    intro i j hnot
    have hmem := hu t i j
    have hbranch : ¬((frontSlotG M t i j).1.1.val < L - 1 ∧ ((frontSlotG M t i j).1.2.val : ℕ) < r
        ∧ ((frontSlotG M t i j).2.val : ℕ) < r ∧ (frontSlotG M t i j).1.2.val
          = (frontSlotG M t i j).2.val) := by
      simp only [frontSlotG]
      rintro ⟨_, hi, hj, hij⟩
      exact hnot ⟨hij, hi⟩
    rw [slotBoxGen, if_neg hbranch, Set.mem_Icc] at hmem
    rw [abs_le]
    show -η ≤ u (coordOfG M (frontSlotG M t i j)) ∧ u (coordOfG M (frontSlotG M t i j)) ≤ η
    exact hmem

/-! ## `hWaist` from the Gram determinant (the certificate corollary) -/

/-- **`P₁ = U · V_ρ` for the waist factorization.** For `frontProd u = U · V` (the width-`r` waist
split), `P1uG u = U · (V.submatrix id ρ)` with `ρ = deepWidthEquiv ∘ inl`: `P1uG` selects the `ρ`
columns of `frontProd = U·V`, i.e. `U` times `V`'s `ρ` columns. -/
theorem P1uG_eq_mul_Vrho (hL : 0 < L) (hrs : r + s = M ((deepLayer hL).castSucc))
    (u : Fin (routeMAmbient M) → ℝ)
    (U : Matrix (Fin (M 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (M ⟨L - 1, by omega⟩)) ℝ)
    (hUV : frontProd M (frontTupleG M u) hL = U * V) :
    P1uG M hL hrs u
      = U * V.submatrix (id : Fin r → Fin r)
          (fun k : Fin r => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k)) := by
  funext i k
  rw [P1uG, hUV, Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun a _ => by rw [Matrix.submatrix_apply, id_eq])

/-- **`hWaist` from the Gram det.** If `det ((P1uG u)ᵀ P1uG u) ≠ 0` (`P₁` rank `r`) then for any
width-`r` waist factorization `frontProd u = U · V`, the top-`r` block `V[:, ρ]` is invertible
(`det ≠ 0`) — `P₁ = U · V_ρ` has rank `r`, so `V_ρ` (`r×r`) is a unit (`right_factor_det_ne_of_rank_eq`). -/
theorem waist_det_ne_of_gram (hL : 0 < L) (hrs : r + s = M ((deepLayer hL).castSucc))
    (u : Fin (routeMAmbient M) → ℝ)
    (hgram : ((P1uG M hL hrs u).transpose * P1uG M hL hrs u).det ≠ 0)
    (U : Matrix (Fin (M 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (M ⟨L - 1, by omega⟩)) ℝ)
    (hUV : frontProd M (frontTupleG M u) hL = U * V) :
    (V.submatrix (id : Fin r → Fin r)
      (fun k : Fin r => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k))).det ≠ 0 := by
  -- `rank P₁ = r` from the Gram det (`rank(PᵀP)=rank P`, square full rank)
  have hrankP1 : (P1uG M hL hrs u).rank = r := by
    have hpp : ((P1uG M hL hrs u).transpose * P1uG M hL hrs u).rank = r := by
      by_contra h
      exact hgram (det_eq_zero_of_rank_lt _ (lt_of_le_of_ne
        (by simpa using ((P1uG M hL hrs u).transpose * P1uG M hL hrs u).rank_le_width) h))
    rwa [Matrix.rank_transpose_mul_self] at hpp
  exact right_factor_det_ne_of_rank_eq (P1uG M hL hrs u) U _
    (P1uG_eq_mul_Vrho hL hrs u U V hUV) hrankP1

end DLNFibre.DLN.RLCT
