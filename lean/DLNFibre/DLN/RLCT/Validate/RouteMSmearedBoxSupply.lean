import DLNFibre.DLN.RLCT.Validate.RouteMSmearedUniformLam
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedWaist

/-!
# `RouteMSmearedBoxSupply` — the general-`L` smeared box supplier (item 3, the instantiation)

Ties R1 (the box determinants) + R2 (the Field-A `hSpre_gen`) + the uniform-`u` `Λ₀`/Gram bounds
(`RouteMSmearedUniformLam`) + the width-`r` waist (`RouteMSmearedWaist`) into the per-ε
`SmearedChartData` the general-`L` chart consumes, then into the unconditional `hSmeared` ∀L.

The load-bearing choice is a single `η*` (a function of `δ`) that simultaneously satisfies:
* `boxGen`'s carrier constraint (`η* ≤ δ`, `0 < η*`, `η* ≤ 1`);
* the Gram / waist det small-`η` margin `r·(η*·Acc_G) < (δ/2)^{L−1}` (`Acc_G` `η`-free);
* the `Λ₀`-dominance margin `(r−1)·(η*·Acc_Λ) < (δ/2)^{L−1−q} − η*·Acc_Λ` (`γ* > 0`);
* the Field-A margin `s·((1/γ*)·(η*·Acc_Λ))·η* ≤ δ`.
All `Acc`s are `η`-free (the suffix recursion reads `M, δ` only), so each is "pick `η*` small".

* `condBox_boxGen_frontLayers` — points in the `boxGen` condBox have front `CarrierLayer`s.
* `insertNth_hN_mem_condBox` — a peeled point `hN ▸ insertNth p z y` is in the `boxGen` condBox.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

open DLNFibre.Core.Matrix

variable {L : ℕ} {M : Fin (L + 1) → ℕ} {r s : ℕ}

/-! ## Front `CarrierLayer`s from a `boxGen` condBox point -/

/-- **A deepest-bottom slot's coord is not the pivot** (bottom ∉ topCoords, pivot ∈ topCoords). -/
theorem coordOfG_botSlotG_ne_pivot (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (b : Fin s) (j : Fin (M ((deepLayer hL).succ))) :
    coordOfG M (botSlotG M hL hrs b j) ≠ pivotCoordG M hL hrs hr hc := by
  intro heq
  have hmem : coordOfG M (botSlotG M hL hrs b j) ∈ topCoordsG M hL hrs := by
    rw [heq]; exact pivotCoordG_mem M hL hrs hr hc
  exact coordOfG_botSlotG_not_mem M hL hrs b j hmem

/-- **The front-slot coord of a free layer `t.val < L−1` is not the pivot** (`t ≠ deepLayer`, so the
front slot is not a top slot, but the pivot IS a top slot). -/
theorem coordOfG_frontSlotG_ne_pivot (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (t : Fin L) (ht : (t : ℕ) < L - 1) (i : Fin (M t.castSucc)) (j : Fin (M t.succ)) :
    coordOfG M (frontSlotG M t i j) ≠ pivotCoordG M hL hrs hr hc := by
  have htd : t ≠ deepLayer hL := by
    intro h; rw [h] at ht; simp only [deepLayer] at ht; omega
  intro heq
  have hmem : coordOfG M (frontSlotG M t i j) ∈ topCoordsG M hL hrs := by
    rw [heq]; exact pivotCoordG_mem M hL hrs hr hc
  exact coordOfG_frontSlotG_not_mem M hL hrs t htd i j hmem

/-- **A `boxGen` condBox point has front `CarrierLayer`s.** For `u` with `∀ k ≠ pivotCoordG, u k ∈ boxGen
r δ η k`, every free front layer `t.val < L−1` of `frontTupleG M u` is a `CarrierLayer r δ η`: at that
layer each front slot's coord `≠ pivotCoordG` (`coordOfG_frontSlotG_ne_pivot`), so it lies in
`boxGen = slotBoxGen`, whose diagonal / off-diagonal branches give the carrier structure. -/
theorem condBox_boxGen_frontLayers (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    {δ η : ℝ} {u : Fin (routeMAmbient M) → ℝ}
    (hu : ∀ k, k ≠ pivotCoordG M hL hrs hr hc → u k ∈ boxGen M hL r δ η k)
    (t : Fin L) (ht : (t : ℕ) < L - 1) :
    CarrierLayer (frontTupleG M u t) r δ η := by
  -- the box membership at this layer's front slots
  have hslot : ∀ i : Fin (M t.castSucc), ∀ j : Fin (M t.succ),
      u (coordOfG M (frontSlotG M t i j)) ∈ slotBoxGen M hL r δ η (frontSlotG M t i j) := by
    intro i j
    have hval := hu _ (coordOfG_frontSlotG_ne_pivot M hL hrs hr hc t ht i j)
    rwa [boxGen_coordOfG] at hval
  constructor
  · -- carrier diagonal `(i:ℕ)=(j:ℕ)<r` ∈ [δ/2,δ]
    intro i j hij hir
    have hmem := hslot i j
    have hbranch : ((frontSlotG M t i j).1.1.val < L - 1 ∧ ((frontSlotG M t i j).1.2.val : ℕ) < r
        ∧ ((frontSlotG M t i j).2.val : ℕ) < r ∧ (frontSlotG M t i j).1.2.val
          = (frontSlotG M t i j).2.val) := by
      refine ⟨ht, ?_, ?_, ?_⟩ <;> simp only [frontSlotG] <;> omega
    rw [slotBoxGen, if_pos hbranch] at hmem
    exact hmem
  · -- every other entry ≤ η
    intro i j hnot
    have hmem := hslot i j
    have hbranch : ¬((frontSlotG M t i j).1.1.val < L - 1 ∧ ((frontSlotG M t i j).1.2.val : ℕ) < r
        ∧ ((frontSlotG M t i j).2.val : ℕ) < r ∧ (frontSlotG M t i j).1.2.val
          = (frontSlotG M t i j).2.val) := by
      simp only [frontSlotG]
      rintro ⟨_, hi, hj, hij⟩
      exact hnot ⟨hij, hi⟩
    rw [slotBoxGen, if_neg hbranch, Set.mem_Icc] at hmem
    rw [abs_le]
    exact hmem

/-! ## The peeled point lands in the `boxGen` condBox -/

/-- **A peeled point's non-pivot coords lie in `boxGen`.** For `y ∈ pi (fun k => boxGen (hN ▸ p.succAbove
k))` and `hp : hN ▸ p = pivotCoordG`, the point `u := hN ▸ insertNth p z y` satisfies `∀ k ≠ pivotCoordG,
u k ∈ boxGen k`. (Off the pivot axis, `u` reads a `y`-coord in exactly the matching `boxGen` interval.) -/
theorem insertNth_hN_frontBox {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1))
    (hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoordG M hL hrs hr hc)
    {δ η : ℝ} (z : ℝ) {y : Fin n → ℝ}
    (box₀ : Fin (n + 1) → Set ℝ)
    (hbox₀ : ∀ k : Fin (routeMAmbient M), boxGen M hL r δ η k = box₀ (hN ▸ k))
    (hy : y ∈ Set.univ.pi (fun k : Fin n => box₀ (p.succAbove k))) :
    ∀ k, k ≠ pivotCoordG M hL hrs hr hc →
      (hN ▸ (Fin.insertNth p z y) : Fin (routeMAmbient M) → ℝ) k ∈ boxGen M hL r δ η k := by
  simp only [Set.mem_pi, Set.mem_univ, true_implies] at hy
  intro k hk
  rw [hbox₀ k]
  -- reduce to `Fin (n+1)`: `(hN ▸ insertNth p z y) k = insertNth p z y (hN ▸ k)`,
  -- and `hN ▸ k ≠ p` (else `k = hN ▸ p = pivot`).
  have hval : (hN ▸ (Fin.insertNth p z y) : Fin (routeMAmbient M) → ℝ) k
      = (Fin.insertNth p z y : Fin (n + 1) → ℝ) (hN ▸ k) := by
    have kk : ∀ (N : ℕ) (h : N = n + 1) (g : Fin (n + 1) → ℝ) (w : Fin N),
        (h ▸ g : Fin N → ℝ) w = g (h ▸ w) := fun N h g w => by subst h; rfl
    exact kk (routeMAmbient M) hN (Fin.insertNth p z y) k
  rw [hval]
  have hkne : (hN ▸ k : Fin (n + 1)) ≠ p := by
    intro h
    apply hk
    rw [← hp, ← h]
    have kk : ∀ (N : ℕ) (hh : N = n + 1) (w : Fin N), (hh ▸ (hh ▸ w : Fin (n + 1)) : Fin N) = w :=
      fun N hh w => by subst hh; rfl
    exact (kk (routeMAmbient M) hN k).symm
  rcases Fin.eq_self_or_eq_succAbove p (hN ▸ k) with h | ⟨k', hk'⟩
  · exact absurd h hkne
  · rw [hk', @Fin.insertNth_apply_succAbove n (fun _ => ℝ) p z y k']
    exact hy k'

/-! ## The single `η*` choice (all margins at once) -/

/-- **A positive `η*` beating a finite list of positive-thresholded linear bounds.** Given `δ > 0` and
nonnegative coefficients `cG, cΛ, cγ, cF`, there is `0 < η* ≤ min(δ,1)` with `cG·η* < TG`,
`cΛ·η* < TL`, `cΛ·η* ≤ TL/2`, and `cF·η* ≤ δ`, for any positive thresholds `TG, TL`. (Each is
"pick `η*` small"; the min of finitely many positive quantities is positive.) -/
theorem exists_eta_margins {δ TG TL cG cΛ cF : ℝ} (hδ : 0 < δ) (hTG : 0 < TG) (hTL : 0 < TL)
    (hcG : 0 ≤ cG) (hcΛ : 0 ≤ cΛ) (hcF : 0 ≤ cF) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ η ≤ 1 ∧ cG * η < TG ∧ cΛ * η < TL ∧ cΛ * η ≤ TL / 2
      ∧ cF * η ≤ δ := by
  -- pick `η = min(δ, 1, TG/(2(cG+1)), TL/(4(cΛ+1)), δ/(cF+1))` — all positive.
  set a1 := TG / (2 * (cG + 1)) with ha1
  set a2 := TL / (4 * (cΛ + 1)) with ha2
  set a3 := δ / (cF + 1) with ha3
  have hcG1 : (0:ℝ) < cG + 1 := by linarith
  have hcΛ1 : (0:ℝ) < cΛ + 1 := by linarith
  have hcF1 : (0:ℝ) < cF + 1 := by linarith
  have ha1p : 0 < a1 := by rw [ha1]; positivity
  have ha2p : 0 < a2 := by rw [ha2]; positivity
  have ha3p : 0 < a3 := by rw [ha3]; positivity
  refine ⟨min (min δ 1) (min a1 (min a2 a3)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (lt_min hδ one_pos) (lt_min ha1p (lt_min ha2p ha3p))
  · exact le_trans (min_le_left _ _) (min_le_left _ _)
  · exact le_trans (min_le_left _ _) (min_le_right _ _)
  · -- `cG·η < TG`: `η ≤ a1 = TG/(2(cG+1))`, so `cG·η ≤ cG·a1 < (cG+1)·a1 ≤ ... < TG`
    have hη : min (min δ 1) (min a1 (min a2 a3)) ≤ a1 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hηpos : 0 < min (min δ 1) (min a1 (min a2 a3)) :=
      lt_min (lt_min hδ one_pos) (lt_min ha1p (lt_min ha2p ha3p))
    calc cG * min (min δ 1) (min a1 (min a2 a3)) ≤ cG * a1 :=
          mul_le_mul_of_nonneg_left hη hcG
      _ ≤ (cG + 1) * a1 := by nlinarith [ha1p]
      _ = TG / 2 := by rw [ha1]; field_simp
      _ < TG := by linarith
  · have hη : min (min δ 1) (min a1 (min a2 a3)) ≤ a2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    calc cΛ * min (min δ 1) (min a1 (min a2 a3)) ≤ cΛ * a2 :=
          mul_le_mul_of_nonneg_left hη hcΛ
      _ ≤ (cΛ + 1) * a2 := by nlinarith [ha2p]
      _ = TL / 4 := by rw [ha2]; field_simp
      _ < TL := by linarith
  · have hη : min (min δ 1) (min a1 (min a2 a3)) ≤ a2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    calc cΛ * min (min δ 1) (min a1 (min a2 a3)) ≤ cΛ * a2 :=
          mul_le_mul_of_nonneg_left hη hcΛ
      _ ≤ (cΛ + 1) * a2 := by nlinarith [ha2p]
      _ = TL / 4 := by rw [ha2]; field_simp
      _ ≤ TL / 2 := by linarith
  · have hη : min (min δ 1) (min a1 (min a2 a3)) ≤ a3 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    calc cF * min (min δ 1) (min a1 (min a2 a3)) ≤ cF * a3 :=
          mul_le_mul_of_nonneg_left hη hcF
      _ ≤ (cF + 1) * a3 := by nlinarith [ha3p]
      _ = δ := by rw [ha3]; field_simp

/-! ## The per-ε general-`L` smeared chart data (the box supplier) -/

set_option maxHeartbeats 1600000 in
/-- **The per-ε general-`L` smeared `SmearedChartData` from the box `boxGen`.** Given the structural
data (`hrs`/`hr`/`hc`/`hp`), the width-`r` waist `q` (`hMq`/`hwidth`, from `smeared_waist`), and the
width lower bounds `hr0`/`hrL`, builds the `SmearedChartData` at radial exponent `r·M(deepLayer).succ − 1`
for any `ε > 0`: sets `δ = ε/2`, picks a single `η*` (via `exists_eta_margins`) making the Gram/waist
det margin, the `Λ₀`-dominance margin, and the Field-A margin all hold on `boxGen r δ η*`, then feeds the
uniform det bounds (`gram_det_ne_uniformEta`) + the Field-A `hSpre_gen` (`Lam0uG_entry_bound_uniformEta`)
into `smearedChartDataGen_of_dets`. -/
theorem smearedChartData_boxGen {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1))
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, by omega⟩ : Fin L).succ))
    (hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoordG M hL hrs hr hc)
    (q : ℕ) (hq : q < L + 1) (hqL : q ≤ L - 1) (hMq : M ⟨q, hq⟩ = r)
    (hr0 : r ≤ M 0) (hrL : r ≤ M (⟨L - 1, by omega⟩ : Fin (L + 1)))
    (hwidth : ∀ t : ℕ, t < L → r ≤ Wext M t)
    (ε : ℝ) (hε : 0 < ε) :
    Nonempty (SmearedChartData M n hN (psiMapG M hL hrs) (RmapG M hL hrs hr hc)
      (DmapG M hL hrs hr hc) p (r * M ((deepLayer hL).succ) - 1) ε) := by
  classical
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  -- the two η-free accumulators
  obtain ⟨AccG, hAccG0, hGramEta⟩ := gram_det_ne_uniformEta M hL hrs hδ hr hr0 hrL hwidth
  obtain ⟨AccΛ, hAccΛ0, hLamEta⟩ := Lam0uG_entry_bound_uniformEta M hL hrs hδ hr q hq hqL hMq hwidth
  -- the single η* with all margins
  obtain ⟨η, hηpos, hηδ, hη1, hmG, hmL, hmLhalf, hmF⟩ :=
    exists_eta_margins (δ := δ) (TG := (δ / 2) ^ (L - 1)) (TL := (δ / 2) ^ (L - 1 - q))
      (cG := (r : ℝ) * AccG) (cΛ := (r : ℝ) * AccΛ)
      (cF := (s : ℝ) * (2 / (δ / 2) ^ (L - 1 - q)) * AccΛ)
      hδ (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  have hηpos' : 0 ≤ η := le_of_lt hηpos
  -- the box `box₀ = boxGen ∘ (hN ▸ ·)`; the double-cast collapse `boxGen k = box₀ (hN ▸ k)`
  set box₀ : Fin (n + 1) → Set ℝ := fun j => boxGen M hL r δ η (hN ▸ j) with hbox₀def
  have hbox₀eq : ∀ k : Fin (routeMAmbient M), boxGen M hL r δ η k = box₀ (hN ▸ k) :=
    fun k => (boxGen_double_cast M hL r δ η hN k).symm
  -- the γ from the Λ₀ lemma at η*, plus its positivity + Field-A margin
  obtain ⟨γ, nb, hnb0, hnbA, hγlb0, hγpos_of, hLamBound⟩ := hLamEta η hηpos' hηδ
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  -- `r·(η·AccΛ) < (δ/2)^{L−1−q}` (from `hmL : (r·AccΛ)·η < TL`) and `(r−1)·nb ≤ (r−1)·η·AccΛ`
  have hrηA : (r : ℝ) * (η * AccΛ) < (δ / 2) ^ (L - 1 - q) := by
    have := hmL; nlinarith [this]
  have hrηAhalf : (r : ℝ) * (η * AccΛ) ≤ (δ / 2) ^ (L - 1 - q) / 2 := by
    have := hmLhalf; nlinarith [this]
  have h1 : ((r : ℝ) - 1) * nb ≤ ((r : ℝ) - 1) * (η * AccΛ) :=
    mul_le_mul_of_nonneg_left hnbA (by linarith)
  have hγpos : 0 < γ := hγpos_of (by nlinarith [h1, hrηA, hnb0, hAccΛ0, hnbA, hr1])
  -- `γ ≥ (δ/2)^{L−1−q}/2`: from the lower bound `γ ≥ (δ/2)^ℓ − η·AccΛ − (r−1)·nb ≥ (δ/2)^ℓ − r·η·AccΛ`
  have hγlb : (δ / 2) ^ (L - 1 - q) / 2 ≤ γ := by
    have hstep : (δ / 2) ^ (L - 1 - q) - η * AccΛ - ((r : ℝ) - 1) * nb
        ≥ (δ / 2) ^ (L - 1 - q) - (r : ℝ) * (η * AccΛ) := by nlinarith [h1]
    have : (δ / 2) ^ (L - 1 - q) - (r : ℝ) * (η * AccΛ) ≥ (δ / 2) ^ (L - 1 - q) / 2 := by
      linarith [hrηAhalf]
    linarith [hγlb0, hstep]
  -- the Field-A margin `s·((1/γ)·nb)·η ≤ δ` from `γ ≥ TL/2`, `nb ≤ η·AccΛ`, `η ≤ 1`, `hmF`
  have hfieldA : (s : ℝ) * ((1 / γ) * nb) * η ≤ δ := by
    have hTLpos : 0 < (δ / 2) ^ (L - 1 - q) := by positivity
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
    -- `(1/γ)·nb ≤ (2/TL)·(η·AccΛ)` since `γ ≥ TL/2` and `nb ≤ η·AccΛ`
    have hinvγ : 1 / γ ≤ 2 / (δ / 2) ^ (L - 1 - q) := by
      rw [div_le_div_iff₀ hγpos hTLpos]; nlinarith [hγlb, hTLpos]
    have hnbηA : nb ≤ η * AccΛ := hnbA
    -- assemble; use η ≤ 1 so η·η ≤ η
    have hηnn : (0 : ℝ) ≤ η := hηpos'
    have hstep1 : (1 / γ) * nb ≤ (2 / (δ / 2) ^ (L - 1 - q)) * (η * AccΛ) := by
      apply mul_le_mul hinvγ hnbηA hnb0
      positivity
    have hsη : (0 : ℝ) ≤ (s : ℝ) * η := mul_nonneg hs0 hηnn
    have hcFnn : (0 : ℝ) ≤ (s : ℝ) * (2 / (δ / 2) ^ (L - 1 - q)) * AccΛ := by positivity
    -- the field-A term is `O(η²)`; bound `η² ≤ η` (since `η ≤ 1`), then use `hmF` (cF·η ≤ δ)
    have hη2 : η * η ≤ η := by nlinarith [hη1, hηnn]
    set cF : ℝ := (s : ℝ) * (2 / (δ / 2) ^ (L - 1 - q)) * AccΛ with hcFdef
    have hmul : (s : ℝ) * η * ((1 / γ) * nb)
        ≤ (s : ℝ) * η * ((2 / (δ / 2) ^ (L - 1 - q)) * (η * AccΛ)) :=
      mul_le_mul_of_nonneg_left hstep1 hsη
    have hLHS : (s : ℝ) * ((1 / γ) * nb) * η = (s : ℝ) * η * ((1 / γ) * nb) := by ring
    have hRHS : (s : ℝ) * η * ((2 / (δ / 2) ^ (L - 1 - q)) * (η * AccΛ)) = cF * (η * η) := by
      rw [hcFdef]; ring
    have hη2' : cF * (η * η) ≤ cF * η := mul_le_mul_of_nonneg_left hη2 hcFnn
    have hbnd : (s : ℝ) * ((1 / γ) * nb) * η ≤ cF * η := by
      rw [hLHS]; rw [hRHS] at hmul; linarith [hmul, hη2']
    calc (s : ℝ) * ((1 / γ) * nb) * η ≤ cF * η := hbnd
      _ ≤ δ := hmF
  -- feed `smearedChartDataGen_of_dets`; `2·δ = ε` (δ = ε/2)
  have h2δ : (2 : ℝ) * δ = ε := by rw [hδdef]; ring
  rw [← h2δ]
  refine ⟨smearedChartDataGen_of_dets M hL hrs hr hc hN p e1 e2 hp q hq hqL hMq
    (2 * δ) δ box₀ hδ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · -- hSpre: via `hSpre_gen` fed the uniform `hLam` (from `hLamBound` + front-carrier layers + Gram)
    have hmarginG : (r : ℝ) * (η * AccG) < (δ / 2) ^ (L - 1) := by nlinarith [hmG]
    -- the uniform `hLam` over the condBox
    have hLam : ∀ (u : Fin (routeMAmbient M) → ℝ),
        u ∈ condBox (pivotCoordG M hL hrs hr hc) (boxGen M hL r δ η) δ →
        ∀ a : Fin r, ∀ b : Fin s, |Lam0uG M hL hrs u a b| ≤ (1 / γ) * nb := by
      intro u hu a b
      have hlayers : ∀ t : Fin L, q ≤ (t : ℕ) → (t : ℕ) < L - 1 →
          CarrierLayer (frontTupleG M u t) r δ η :=
        fun t _ htL => condBox_boxGen_frontLayers M hL hrs hr hc hu.2 t htL
      have hlayersAll : ∀ t : Fin L, (t : ℕ) < L - 1 →
          CarrierLayer (frontTupleG M u t) r δ η :=
        fun t htL => condBox_boxGen_frontLayers M hL hrs hr hc hu.2 t htL
      have hgram := hGramEta η hηpos' hηδ hmarginG u hlayersAll
      exact hLamBound hγpos u hlayers hgram a b
    exact hSpre_gen M hL hrs hr hc hN p hp hδ hγpos hηδ hη1 hηpos' hnb0 hfieldA
      (fun b j => coordOfG_botSlotG_ne_pivot M hL hrs hr hc b j) hLam
  · -- hRinj: `RmapG` injective on the condBox (pivot ∈ Ioo 0 δ ⟹ ≠ 0)
    exact RmapG_injOn_condBox M hL hrs hr hc (hN ▸ p) hp (fun k => box₀ (hN ▸ k)) δ
  · -- hboxmeas: each `box₀ (p.succAbove k) = boxGen (hN ▸ p.succAbove k)`, measurable
    intro k; rw [hbox₀def]; exact measurableSet_boxGen M hL r δ η _
  · -- hboxmeasAll
    intro k; rw [hbox₀def]; exact measurableSet_boxGen M hL r δ η _
  · -- hboxpos: `boxGen_pos` (both Icc branches nonempty for `0 < δ`, `0 < η`)
    have := boxGen_pos (r := r) M hL hδ hηpos hN p
    convert this using 3
  · -- hGram: `gram_det_ne_uniformEta` at η*, fed the front-carrier layers of the peeled point
    intro z hz y hy
    have hmargin : (r : ℝ) * (η * AccG) < (δ / 2) ^ (L - 1) := by nlinarith [hmG]
    have hfront := insertNth_hN_frontBox M hL hrs hr hc hN p hp z box₀ hbox₀eq hy
    exact hGramEta η hηpos' hηδ hmargin (hN ▸ Fin.insertNth p z y)
      (fun t htL => condBox_boxGen_frontLayers M hL hrs hr hc hfront t htL)
  · -- hGram0: same at `z = 0` (which is in the closure but the front layers still land in boxGen)
    intro y hy
    have hmargin : (r : ℝ) * (η * AccG) < (δ / 2) ^ (L - 1) := by nlinarith [hmG]
    have hfront := insertNth_hN_frontBox M hL hrs hr hc hN p hp (0:ℝ) box₀ hbox₀eq hy
    exact hGramEta η hηpos' hηδ hmargin (hN ▸ Fin.insertNth p (0:ℝ) y)
      (fun t htL => condBox_boxGen_frontLayers M hL hrs hr hc hfront t htL)
  · -- hWaist: from the Gram det via `waist_det_ne_of_gram`
    intro z hz y hy U V hUV
    have hmargin : (r : ℝ) * (η * AccG) < (δ / 2) ^ (L - 1) := by nlinarith [hmG]
    have hfront := insertNth_hN_frontBox M hL hrs hr hc hN p hp z box₀ hbox₀eq hy
    have hgram := hGramEta η hηpos' hηδ hmargin (hN ▸ Fin.insertNth p z y)
      (fun t htL => condBox_boxGen_frontLayers M hL hrs hr hc hfront t htL)
    exact waist_det_ne_of_gram hL hrs (hN ▸ Fin.insertNth p z y) hgram U V hUV

end DLNFibre.DLN.RLCT
