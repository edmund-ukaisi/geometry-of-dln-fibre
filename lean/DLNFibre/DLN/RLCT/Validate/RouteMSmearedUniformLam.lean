import DLNFibre.DLN.RLCT.Validate.RouteMSmearedSquareGen

/-!
# `RouteMSmearedUniformLam` — the UNIFORM-in-`u` `Λ₀`-entry bound (item 1)

R2's `hSpre_gen` needs the `Λ₀`-entry bound `hLam : ∀ u ∈ condBox, ∀ a b, |Lam0uG u a b| ≤ (1/γ)·nb`
with `γ, nb` UNIFORM over the box. The banked `Lam0uG_entry_bound` returns `γ, nb, Acc` as a per-`u`
existential — but the underlying suffix recursion (`wideCarrierBound_suffix`) builds the scalars
`dlb, nb, pub, Acc` by a `Nat.le_induction` whose updates read ONLY `(M, δ, η, q, k)`, never `u`. This
module exposes that `u`-independence: it re-runs the suffix induction with the scalar existential pulled
OUTSIDE the `∀ u` — a single `∃ dlb nb pub Acc, [scalar invariants] ∧ ∀ (front-carrier) u, ∃ Y, …` — so
the box supplier can pick ONE `η` making the margin hold for every `u` at once.

* `wideCarrierBound_suffix_uniform` — the `∃ scalars, ∀ u` suffix carrier bound.
* `waist_carrier_data_uniform` — the waist factorization + carrier data with `u`-free `dlb, nb, Acc`.
* `Lam0uG_entry_bound_uniform` — the uniform `Λ₀`-entry bound: for fixed `γ, nb` and the margin,
  every front-carrier `u` (with its own Gram-det condition) has `|Lam0uG u a b| ≤ (1/γ)·nb`.
* `hLam_uniform_of_boxGen` — packages `Lam0uG_entry_bound_uniform` into the exact `hLam` shape
  `hSpre_gen` consumes (`∀ u ∈ condBox (pivot) (boxGen) δ, …`).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

open DLNFibre.Core.Matrix

variable {L : ℕ} {M : Fin (L + 1) → ℕ} {r s : ℕ}

/-! ## The suffix carrier bound with `∃ scalars` OUTSIDE `∀ u` (the uniform witnesses) -/

/-- **The uniform suffix-product carrier bound.** Same content as `wideCarrierBound_suffix`, but the
scalar witnesses `dlb, nb, pub, Acc` are produced ONCE (independent of the layer tuple `A`), and the
factorization + `WideCarrierBound` hold for EVERY `A` whose layers `p..k−1` are `CarrierLayer`s. The
scalars are the same `u`-free recursion; only `Y` depends on `A`. -/
theorem wideCarrierBound_suffix_uniform {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ)
    (p : ℕ) (hp : p < L + 1)
    (hwidth : ∀ t : ℕ, t < L → r ≤ Wext M t) :
    ∀ (k : ℕ) (_hpk : p ≤ k) (_hkub : k ≤ L - 1) (hk : k < L + 1),
      ∃ (dlb nb pub Acc : ℝ),
        0 ≤ nb ∧ 0 ≤ pub ∧ 0 ≤ Acc
          ∧ nb ≤ η * Acc ∧ (δ / 2) ^ (k - p) - η * Acc ≤ dlb
          ∧ ∀ (A : Params M),
              (∀ t : Fin L, p ≤ (t : ℕ) → (t : ℕ) < L - 1 → CarrierLayer (A t) r δ η) →
              ∃ (Y : Matrix (Fin (M ⟨p, hp⟩)) (Fin (M ⟨k, hk⟩)) ℝ),
                prodAux M A k hk = prodAux M A p hp * Y ∧ WideCarrierBound Y r dlb nb pub := by
  intro k hpk
  induction k, hpk using Nat.le_induction with
  | base =>
      intro _ hk
      refine ⟨1, 0, 1, 0, le_refl _, by norm_num, le_refl _, by simp, by simp, ?_⟩
      intro A _
      exact ⟨1, (Matrix.mul_one _).symm, wideCarrierBound_one⟩
  | succ k hpk ih =>
      intro hkub hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hkub' : k ≤ L - 1 := by omega
      have hkLm1 : k < L - 1 := by omega
      obtain ⟨dlb, nb, pub, Acc, hnb0, hpub0, hAcc0, hnbA, hdlbA, hfac⟩ := ih hkub' hk'
      -- the interface width `M ⟨k,_⟩ ≥ r`
      have hrw : r ≤ M (⟨k, hk'⟩ : Fin (L + 1)) := by
        have := hwidth k hkL; rwa [Wext_apply M k hk'] at this
      refine ⟨dlb * (δ / 2) - (M (⟨k, hk'⟩ : Fin (L + 1)) - 1 : ℕ) * pub * η,
        nb * δ + M (⟨k, hk'⟩ : Fin (L + 1)) * pub * η, M (⟨k, hk'⟩ : Fin (L + 1)) * pub * δ,
        δ * Acc + M (⟨k, hk'⟩ : Fin (L + 1)) * pub, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        positivity
      · have : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        positivity
      · have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        have : (0:ℝ) ≤ δ * Acc := mul_nonneg (le_of_lt hδ) hAcc0
        positivity
      · have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        have h1 : nb * δ ≤ η * (δ * Acc) := by
          nlinarith [hnbA, hδ.le, mul_le_mul_of_nonneg_right hnbA hδ.le]
        nlinarith [h1, mul_nonneg (mul_nonneg hM hpub0) hη]
      · have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
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
      · -- the `∀ A` factorization at the advanced scalars
        intro A hlayers
        obtain ⟨Y, hY, hWCB⟩ := hfac A (fun t htp htL => hlayers t htp htL)
        have e1 : M (⟨k, hk'⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).castSucc) := by
          apply congrArg; apply Fin.ext; simp [Fin.castSucc]
        have e2 : M (⟨k + 1, hk⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).succ) := by
          apply congrArg; apply Fin.ext; simp [Fin.succ]
        set Alay := Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k, hkL⟩) with hAlay
        have hCL : CarrierLayer Alay r δ η :=
          carrierLayer_reindex (A ⟨k, hkL⟩) (hlayers ⟨k, hkL⟩ hpk hkLm1) e1.symm e2.symm
        have hstep := wideCarrier_mul hWCB hCL hpub0 hnb0 hη hηδ hrw
        refine ⟨Y * Alay, ?_, hstep⟩
        rw [prodAux_succ M A k hk e1 e2, hY, ← Matrix.mul_assoc]

/-! ## Option-D: `∃ (η-free pub, Acc) OUTSIDE ∀ η` (for the single-`η*` box supplier)

The suffix recursion's `pub, Acc` read `M, δ` only — never `η`. Pulling `∃ pub Acc` outside `∀ η` gives
the box supplier a single `Acc` to compute the small-`η*` margins against BEFORE fixing `η*`. Re-runs the
suffix induction carrying `∀ η` inside (the `η`-free `pub, Acc` recursions on the outside, the
`η`-dependent `dlb, nb` inside). -/

/-- **The η-uniform suffix carrier bound.** `∃ pub Acc` (η-free) such that for EVERY `0 ≤ η ≤ δ` there
are `dlb, nb` with the fused invariant and the `∀ A` factorization at this `η`. -/
theorem wideCarrierBound_suffix_uniformEta (M : Fin (L + 1) → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (p : ℕ) (hp : p < L + 1) (hwidth : ∀ t : ℕ, t < L → r ≤ Wext M t) :
    ∀ (k : ℕ) (_hpk : p ≤ k) (_hkub : k ≤ L - 1) (hk : k < L + 1),
      ∃ (pub Acc : ℝ), 0 ≤ pub ∧ 0 ≤ Acc ∧
        ∀ (η : ℝ), 0 ≤ η → η ≤ δ →
          ∃ (dlb nb : ℝ), 0 ≤ nb ∧ nb ≤ η * Acc ∧ (δ / 2) ^ (k - p) - η * Acc ≤ dlb
            ∧ ∀ (A : Params M),
                (∀ t : Fin L, p ≤ (t : ℕ) → (t : ℕ) < L - 1 → CarrierLayer (A t) r δ η) →
                ∃ (Y : Matrix (Fin (M ⟨p, hp⟩)) (Fin (M ⟨k, hk⟩)) ℝ),
                  prodAux M A k hk = prodAux M A p hp * Y ∧ WideCarrierBound Y r dlb nb pub := by
  intro k hpk
  induction k, hpk using Nat.le_induction with
  | base =>
      intro _ hk
      refine ⟨1, 0, zero_le_one, le_refl _, fun η hη _ => ⟨1, 0, le_refl _, by simp, by simp, ?_⟩⟩
      intro A _
      exact ⟨1, (Matrix.mul_one _).symm, wideCarrierBound_one⟩
  | succ k hpk ih =>
      intro hkub hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hkub' : k ≤ L - 1 := by omega
      have hkLm1 : k < L - 1 := by omega
      obtain ⟨pub, Acc, hpub0, hAcc0, hstepη⟩ := ih hkub' hk'
      have hrw : r ≤ M (⟨k, hk'⟩ : Fin (L + 1)) := by
        have := hwidth k hkL; rwa [Wext_apply M k hk'] at this
      have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
      -- η-free advanced pub, Acc
      refine ⟨M (⟨k, hk'⟩ : Fin (L + 1)) * pub * δ, δ * Acc + M (⟨k, hk'⟩ : Fin (L + 1)) * pub,
        by positivity, by positivity, fun η hη hηδ => ?_⟩
      obtain ⟨dlb, nb, hnb0, hnbA, hdlbA, hfac⟩ := hstepη η hη hηδ
      refine ⟨dlb * (δ / 2) - (M (⟨k, hk'⟩ : Fin (L + 1)) - 1 : ℕ) * pub * η,
        nb * δ + M (⟨k, hk'⟩ : Fin (L + 1)) * pub * η, by positivity, ?_, ?_, ?_⟩
      · -- `nb' ≤ η · Acc'`
        have h1 : nb * δ ≤ η * (δ * Acc) := by
          nlinarith [hnbA, hδ.le, mul_le_mul_of_nonneg_right hnbA hδ.le]
        nlinarith [h1, mul_nonneg (mul_nonneg hM hpub0) hη]
      · -- `(δ/2)^{(k+1)−p} − η·Acc' ≤ dlb'`
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
      · -- the `∀ A` factorization
        intro A hlayers
        obtain ⟨Y, hY, hWCB⟩ := hfac A (fun t htp htL => hlayers t htp htL)
        have e1 : M (⟨k, hk'⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).castSucc) := by
          apply congrArg; apply Fin.ext; simp [Fin.castSucc]
        have e2 : M (⟨k + 1, hk⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).succ) := by
          apply congrArg; apply Fin.ext; simp [Fin.succ]
        set Alay := Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k, hkL⟩) with hAlay
        have hCL : CarrierLayer Alay r δ η :=
          carrierLayer_reindex (A ⟨k, hkL⟩) (hlayers ⟨k, hkL⟩ hpk hkLm1) e1.symm e2.symm
        have hstep := wideCarrier_mul hWCB hCL hpub0 hnb0 hη hηδ hrw
        refine ⟨Y * Alay, ?_, hstep⟩
        rw [prodAux_succ M A k hk e1 e2, hY, ← Matrix.mul_assoc]

/-! ## The uniform waist carrier data (`u`-free `dlb, nb, Acc`) -/

/-- **The uniform waist carrier data.** Same content as `waist_carrier_data`, but the scalar witnesses
`dlb, nb, Acc` are produced ONCE (independent of `u`), and the factorization + carrier bounds hold for
EVERY front-carrier `u`. The width lower bound is over FRONT layers `t < L` only (the deepest `M ⟨L⟩` is
not in the carrier corridor). -/
theorem waist_carrier_data_uniform (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc))
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ)
    (q : ℕ) (hq : q < L + 1) (hqL : q ≤ L - 1) (hMq : M ⟨q, hq⟩ = r)
    (hwidth : ∀ t : ℕ, t < L → r ≤ Wext M t) :
    ∃ (dlb nb Acc : ℝ),
      0 ≤ nb ∧ 0 ≤ Acc ∧ nb ≤ η * Acc ∧ (δ / 2) ^ (L - 1 - q) - η * Acc ≤ dlb
      ∧ ∀ (u : Fin (routeMAmbient M) → ℝ),
          (∀ t : Fin L, q ≤ (t : ℕ) → (t : ℕ) < L - 1 → CarrierLayer (frontTupleG M u t) r δ η) →
          ∃ (U : Matrix (Fin (M 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (M ⟨L - 1, by omega⟩)) ℝ),
            frontProd M (frontTupleG M u) hL = U * V
              ∧ CarrierBound (V.submatrix (id : Fin r → Fin r)
                  (fun k : Fin r => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k))) dlb nb
              ∧ (∀ i : Fin r, ∀ b : Fin s,
                  |(V.submatrix (id : Fin r → Fin r)
                    (fun j : Fin s => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr j))) i b| ≤ nb) := by
  obtain ⟨dlb, nb, pub, Acc, hnb0, _hpub0, hAcc0, hnbA, hdlbA, hfac⟩ :=
    wideCarrierBound_suffix_uniform hδ hη hηδ q hq hwidth (L - 1) hqL (le_refl _) (by omega)
  refine ⟨dlb, nb, Acc, hnb0, hAcc0, hnbA, hdlbA, fun u hlayers => ?_⟩
  obtain ⟨Y, hY, hWCB⟩ := hfac (frontTupleG M u) hlayers
  refine ⟨(prodAux M (frontTupleG M u) q hq).submatrix (id : _ → _) (Fin.cast hMq.symm),
    Y.submatrix (Fin.cast hMq.symm) (id : _ → _), ?_, ?_, ?_⟩
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
    · rw [Matrix.submatrix_apply, id_eq, Matrix.submatrix_apply, id_eq]
      refine hdiag (Fin.cast hMq.symm i) (by simp [Fin.cast])
        (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl i)) ?_
      simp only [Fin.coe_cast, deepWidthEquiv, Equiv.trans_apply, finCongr_apply, Fin.coe_cast,
        finSumFinEquiv_apply_left, Fin.coe_castAdd]
    · rw [Matrix.submatrix_apply, id_eq, Matrix.submatrix_apply, id_eq]
      refine hnb (Fin.cast hMq.symm i) (by simp [Fin.cast])
        (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k)) ?_
      simp only [Fin.coe_cast, deepWidthEquiv, Equiv.trans_apply, finCongr_apply, Fin.coe_cast,
        finSumFinEquiv_apply_left, Fin.coe_castAdd]
      exact fun h => hik (Fin.ext h)
  · -- `Vσ` uniform bound
    intro i b
    rw [Matrix.submatrix_apply, id_eq]
    obtain ⟨_, hnb, _⟩ := hWCB
    refine hnb (Fin.cast hMq.symm i) (by simp [Fin.cast])
      (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr b)) ?_
    simp only [Fin.coe_cast, deepWidthEquiv, Equiv.trans_apply, finCongr_apply, Fin.coe_cast,
      finSumFinEquiv_apply_right, Fin.coe_natAdd]
    omega

/-! ## The uniform `Λ₀`-entry bound (fixed `γ, nb`, every front-carrier `u`) -/

/-- **The uniform `Λ₀`-entry bound.** For a boundary-smeared waist `q` and `u`-free scalars `dlb, nb,
Acc` from `waist_carrier_data_uniform`, set `γ := dlb − (r−1)·nb`. If `(r−1)·nb < (δ/2)^{L−1−q} − η·Acc`
(the small-`η` margin, `u`-free), then `γ > 0` and every front-carrier `u` with `det (P₁ᵀP₁) ≠ 0` has
`|Lam0uG u a b| ≤ (1/γ)·nb`. The uniform (`∀ u`) analog of `Lam0uG_entry_bound`. -/
theorem Lam0uG_entry_bound_uniform (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc))
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ) (hr : 0 < r)
    (q : ℕ) (hq : q < L + 1) (hqL : q ≤ L - 1) (hMq : M ⟨q, hq⟩ = r)
    (hwidth : ∀ t : ℕ, t < L → r ≤ Wext M t) :
    ∃ (γ nb Acc : ℝ), 0 ≤ nb ∧ 0 ≤ Acc ∧ nb ≤ η * Acc
      ∧ (((r : ℝ) - 1) * nb < (δ / 2) ^ (L - 1 - q) - η * Acc → 0 < γ)
      ∧ (0 < γ → ∀ (u : Fin (routeMAmbient M) → ℝ),
          (∀ t : Fin L, q ≤ (t : ℕ) → (t : ℕ) < L - 1 → CarrierLayer (frontTupleG M u t) r δ η) →
          ((P1uG M hL hrs u).transpose * P1uG M hL hrs u).det ≠ 0 →
          ∀ a : Fin r, ∀ b : Fin s, |Lam0uG M hL hrs u a b| ≤ (1 / γ) * nb) := by
  obtain ⟨dlb, nb, Acc, hnb0, hAcc0, hnbA, hdlbA, hdata⟩ :=
    waist_carrier_data_uniform M hL hrs hδ hη hηδ q hq hqL hMq hwidth
  refine ⟨dlb - ((r : ℝ) - 1) * nb, nb, Acc, hnb0, hAcc0, hnbA, ?_, ?_⟩
  · intro hsmall
    have : ((r : ℝ) - 1) * nb < dlb := lt_of_lt_of_le hsmall hdlbA
    linarith
  · intro hγpos u hlayers hgram a b
    obtain ⟨U, V, hUV, hVρbound, hVσbound⟩ := hdata u hlayers
    set Vρ : Matrix (Fin r) (Fin r) ℝ := V.submatrix (id : Fin r → Fin r)
      (fun k : Fin r => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k)) with hVρdef
    set Vσ : Matrix (Fin r) (Fin s) ℝ := V.submatrix (id : Fin r → Fin r)
      (fun j : Fin s => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr j)) with hVσdef
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have hdomlt : ((r : ℝ) - 1) * nb < dlb := by linarith [hγpos]
    have hSRD : StrictRowDominant Vρ (dlb - ((r : ℝ) - 1) * nb) :=
      hVρbound.strictRowDominant hdomlt
    have hVρdet : Vρ.det ≠ 0 := hSRD.det_ne_zero
    have hLamEq : Lam0uG M hL hrs u = Vρ⁻¹ * Vσ := by
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
    have hcol : ∀ i, |Vσ i b| ≤ nb := fun i => hVσbound i b
    exact hSRD.inv_mul_entry_bound Vσ b (Mj := nb) hcol a

/-! ## The uniform Gram / waist determinants (`u`-free `Acc`, one small-`η` margin)

The Gram carrier block is the `p = 0` suffix (`prodAux (L−1) = prodAux 0 · Y = Y`), so
`wideCarrierBound_suffix_uniform` at `p = 0` gives a `u`-free `WideCarrierBound` on the whole front
product — hence a `u`-free `Acc` for the Gram/waist small-`η` margins. -/

/-- **The uniform WideCarrierBound on `frontProd`.** `frontProd = prodAux (L−1)` is the `p = 0` suffix,
so the uniform suffix bound at `p = 0` gives `u`-free scalars `dlb, nb, pub, Acc` with a
`WideCarrierBound (frontProd M (frontTupleG M u)) r dlb nb pub` for every all-front-carrier `u`. -/
theorem wideCarrierBound_frontProd_uniform (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ)
    (hwidth : ∀ t : ℕ, t < L → r ≤ Wext M t) :
    ∃ (dlb nb pub Acc : ℝ),
      0 ≤ nb ∧ 0 ≤ pub ∧ 0 ≤ Acc ∧ nb ≤ η * Acc ∧ (δ / 2) ^ (L - 1) - η * Acc ≤ dlb
      ∧ ∀ (u : Fin (routeMAmbient M) → ℝ),
          (∀ t : Fin L, (t : ℕ) < L - 1 → CarrierLayer (frontTupleG M u t) r δ η) →
          WideCarrierBound (frontProd M (frontTupleG M u) hL) r dlb nb pub := by
  obtain ⟨dlb, nb, pub, Acc, hnb0, hpub0, hAcc0, hnbA, hdlbA, hfac⟩ :=
    wideCarrierBound_suffix_uniform (M := M) (r := r) hδ hη hηδ 0 (by omega) hwidth
      (L - 1) (by omega) (le_refl _) (by omega)
  rw [Nat.sub_zero] at hdlbA
  refine ⟨dlb, nb, pub, Acc, hnb0, hpub0, hAcc0, hnbA, hdlbA, fun u hlayers => ?_⟩
  obtain ⟨Y, hY, hWCB⟩ := hfac (frontTupleG M u) (fun t _ htL => hlayers t htL)
  -- `frontProd = prodAux (L−1) = prodAux 0 · Y = 1 · Y = Y` (`prodAux 0 = 1` definitionally)
  have hfront : frontProd M (frontTupleG M u) hL = Y := by
    rw [frontProd, hY]
    simp only [prodAux]
    exact Matrix.one_mul Y
  rw [hfront]; exact hWCB

/-- **The uniform Gram determinant.** For a fixed `δ` and the `u`-free `Acc`, if `r·(η·Acc) <
(δ/2)^{L−1}` then every all-front-carrier `u` has `det ((P1uG u)ᵀ P1uG u) ≠ 0`. The uniform (`∀ u`)
analog of `gram_det_ne_of_carrierLayers`. -/
theorem gram_det_ne_uniform (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc))
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ) (hr : 0 < r)
    (hr0 : r ≤ M 0) (hrL : r ≤ M (⟨L - 1, by omega⟩ : Fin (L + 1)))
    (hwidth : ∀ t : ℕ, t < L → r ≤ Wext M t) :
    ∃ Acc : ℝ, 0 ≤ Acc ∧ ((r : ℝ) * (η * Acc) < (δ / 2) ^ (L - 1) →
      ∀ (u : Fin (routeMAmbient M) → ℝ),
        (∀ t : Fin L, (t : ℕ) < L - 1 → CarrierLayer (frontTupleG M u t) r δ η) →
        ((P1uG M hL hrs u).transpose * P1uG M hL hrs u).det ≠ 0) := by
  obtain ⟨dlb, nb, pub, Acc, hnb0, _hpub0, hAcc0, hnbA, hdlbA, hWCB⟩ :=
    wideCarrierBound_frontProd_uniform M hL hδ hη hηδ hwidth
  refine ⟨Acc, hAcc0, fun hsmall u hlayers => ?_⟩
  have hdom := dominance_of_small_eta (L := L) (r := r) hr hη hAcc0 hnb0 hnbA hdlbA hsmall
  -- the carrier block of `frontProd` has `det ≠ 0`
  have hblock : (Matrix.of (fun i j : Fin r => prodAux M (frontTupleG M u) (L - 1) (by omega)
      ⟨i, lt_of_lt_of_le i.isLt hr0⟩ ⟨j, lt_of_lt_of_le j.isLt hrL⟩)).det ≠ 0 := by
    have hcb := ((hWCB u hlayers).carrierBlock hr0 hrL)
    have hcb' : CarrierBound (Matrix.of (fun i j : Fin r => prodAux M (frontTupleG M u) (L - 1)
        (by omega) ⟨i, lt_of_lt_of_le i.isLt hr0⟩ ⟨j, lt_of_lt_of_le j.isLt hrL⟩)) dlb nb := by
      exact hcb
    exact hcb'.det_ne_zero hdom
  refine gram_det_ne_zero_of_submatrix_det_ne (P1uG M hL hrs u)
    (fun a : Fin r => (⟨a, lt_of_lt_of_le a.isLt hr0⟩ : Fin (M 0))) (id : Fin r → Fin r) ?_
  have hEq : (P1uG M hL hrs u).submatrix
      (fun a : Fin r => (⟨a, lt_of_lt_of_le a.isLt hr0⟩ : Fin (M 0))) (id : Fin r → Fin r)
      = Matrix.of (fun i j : Fin r => prodAux M (frontTupleG M u) (L - 1) (by omega)
          ⟨i, lt_of_lt_of_le i.isLt hr0⟩ ⟨j, lt_of_lt_of_le j.isLt hrL⟩) := by
    funext i j
    exact P1uG_submatrix_eq_carrierBlock hL hrs u hr0 hrL i j
  rw [hEq]; exact hblock

/-! ## Option-D uniform det / `Λ₀` bounds (`∃ Acc` OUTSIDE `∀ η`, for the single-`η*` supplier) -/

/-- **The η-uniform Gram determinant.** `∃ Acc_G ≥ 0` such that for EVERY `0 ≤ η ≤ δ` with the margin
`r·(η·Acc_G) < (δ/2)^{L−1}`, every all-front-carrier `u` (at that `η`) has `det ((P1uG u)ᵀ P1uG u) ≠ 0`.
The η-free `Acc_G` lets the box supplier fix `η*` against it. -/
theorem gram_det_ne_uniformEta (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc))
    {δ : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (hr0 : r ≤ M 0) (hrL : r ≤ M (⟨L - 1, by omega⟩ : Fin (L + 1)))
    (hwidth : ∀ t : ℕ, t < L → r ≤ Wext M t) :
    ∃ Acc : ℝ, 0 ≤ Acc ∧ ∀ (η : ℝ), 0 ≤ η → η ≤ δ →
      ((r : ℝ) * (η * Acc) < (δ / 2) ^ (L - 1) →
        ∀ (u : Fin (routeMAmbient M) → ℝ),
          (∀ t : Fin L, (t : ℕ) < L - 1 → CarrierLayer (frontTupleG M u t) r δ η) →
          ((P1uG M hL hrs u).transpose * P1uG M hL hrs u).det ≠ 0) := by
  obtain ⟨pub, Acc, _hpub0, hAcc0, hstepη⟩ :=
    wideCarrierBound_suffix_uniformEta (M := M) (r := r) hδ 0 (by omega) hwidth
      (L - 1) (by omega) (le_refl _) (by omega)
  refine ⟨Acc, hAcc0, fun η hη hηδ hsmall u hlayers => ?_⟩
  obtain ⟨dlb, nb, hnb0, hnbA, hdlbA, hfac⟩ := hstepη η hη hηδ
  rw [Nat.sub_zero] at hdlbA
  have hdom := dominance_of_small_eta (L := L) (r := r) hr hη hAcc0 hnb0 hnbA hdlbA hsmall
  obtain ⟨Y, hY, hWCB⟩ := hfac (frontTupleG M u) (fun t _ htL => hlayers t htL)
  have hfront : frontProd M (frontTupleG M u) hL = Y := by
    rw [frontProd, hY]; simp only [prodAux]; exact Matrix.one_mul Y
  have hblock : (Matrix.of (fun i j : Fin r => prodAux M (frontTupleG M u) (L - 1) (by omega)
      ⟨i, lt_of_lt_of_le i.isLt hr0⟩ ⟨j, lt_of_lt_of_le j.isLt hrL⟩)).det ≠ 0 := by
    have hWCBf : WideCarrierBound (frontProd M (frontTupleG M u) hL) r dlb nb pub := hfront ▸ hWCB
    exact ((hWCBf.carrierBlock hr0 hrL).det_ne_zero hdom)
  refine gram_det_ne_zero_of_submatrix_det_ne (P1uG M hL hrs u)
    (fun a : Fin r => (⟨a, lt_of_lt_of_le a.isLt hr0⟩ : Fin (M 0))) (id : Fin r → Fin r) ?_
  have hEq : (P1uG M hL hrs u).submatrix
      (fun a : Fin r => (⟨a, lt_of_lt_of_le a.isLt hr0⟩ : Fin (M 0))) (id : Fin r → Fin r)
      = Matrix.of (fun i j : Fin r => prodAux M (frontTupleG M u) (L - 1) (by omega)
          ⟨i, lt_of_lt_of_le i.isLt hr0⟩ ⟨j, lt_of_lt_of_le j.isLt hrL⟩) := by
    funext i j; exact P1uG_submatrix_eq_carrierBlock hL hrs u hr0 hrL i j
  rw [hEq]; exact hblock

/-- **The η-uniform waist carrier data.** `∃ Acc_Λ ≥ 0` such that for EVERY `0 ≤ η ≤ δ` there is a
`u`-free `nb ≤ η·Acc_Λ` and a `u`-free lower bound `dlb ≥ (δ/2)^{L−1−q} − η·Acc_Λ`, with the
factorization + carrier bounds holding for every front-carrier `u` at that `η`. -/
theorem waist_carrier_data_uniformEta (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) {δ : ℝ} (hδ : 0 < δ)
    (q : ℕ) (hq : q < L + 1) (hqL : q ≤ L - 1) (hMq : M ⟨q, hq⟩ = r)
    (hwidth : ∀ t : ℕ, t < L → r ≤ Wext M t) :
    ∃ Acc : ℝ, 0 ≤ Acc ∧ ∀ (η : ℝ), 0 ≤ η → η ≤ δ →
      ∃ (dlb nb : ℝ), 0 ≤ nb ∧ nb ≤ η * Acc ∧ (δ / 2) ^ (L - 1 - q) - η * Acc ≤ dlb
        ∧ ∀ (u : Fin (routeMAmbient M) → ℝ),
            (∀ t : Fin L, q ≤ (t : ℕ) → (t : ℕ) < L - 1 → CarrierLayer (frontTupleG M u t) r δ η) →
            ∃ (U : Matrix (Fin (M 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (M ⟨L - 1, by omega⟩)) ℝ),
              frontProd M (frontTupleG M u) hL = U * V
                ∧ CarrierBound (V.submatrix (id : Fin r → Fin r)
                    (fun k : Fin r => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k))) dlb nb
                ∧ (∀ i : Fin r, ∀ b : Fin s,
                    |(V.submatrix (id : Fin r → Fin r)
                      (fun j : Fin s => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr j))) i b|
                        ≤ nb) := by
  obtain ⟨pub, Acc, _hpub0, hAcc0, hstepη⟩ :=
    wideCarrierBound_suffix_uniformEta (M := M) (r := r) hδ q hq hwidth
      (L - 1) hqL (le_refl _) (by omega)
  refine ⟨Acc, hAcc0, fun η hη hηδ => ?_⟩
  obtain ⟨dlb, nb, hnb0, hnbA, hdlbA, hfac⟩ := hstepη η hη hηδ
  refine ⟨dlb, nb, hnb0, hnbA, hdlbA, fun u hlayers => ?_⟩
  obtain ⟨Y, hY, hWCB⟩ := hfac (frontTupleG M u) hlayers
  refine ⟨(prodAux M (frontTupleG M u) q hq).submatrix (id : _ → _) (Fin.cast hMq.symm),
    Y.submatrix (Fin.cast hMq.symm) (id : _ → _), ?_, ?_, ?_⟩
  · rw [frontProd, hY]
    funext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Fintype.sum_equiv (finCongr hMq)
      (fun a => (prodAux M (frontTupleG M u) q hq) i a * Y a j)
      (fun k => (prodAux M (frontTupleG M u) q hq).submatrix (id : _ → _) (Fin.cast hMq.symm) i k
        * Y.submatrix (Fin.cast hMq.symm) (id : _ → _) k j) (fun a => ?_)
    simp only [Matrix.submatrix_apply, id_eq, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  · obtain ⟨hdiag, hnb, _⟩ := hWCB
    refine ⟨fun i => ?_, fun i k hik => ?_⟩
    · rw [Matrix.submatrix_apply, id_eq, Matrix.submatrix_apply, id_eq]
      refine hdiag (Fin.cast hMq.symm i) (by simp [Fin.cast])
        (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl i)) ?_
      simp only [Fin.coe_cast, deepWidthEquiv, Equiv.trans_apply, finCongr_apply, Fin.coe_cast,
        finSumFinEquiv_apply_left, Fin.coe_castAdd]
    · rw [Matrix.submatrix_apply, id_eq, Matrix.submatrix_apply, id_eq]
      refine hnb (Fin.cast hMq.symm i) (by simp [Fin.cast])
        (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k)) ?_
      simp only [Fin.coe_cast, deepWidthEquiv, Equiv.trans_apply, finCongr_apply, Fin.coe_cast,
        finSumFinEquiv_apply_left, Fin.coe_castAdd]
      exact fun h => hik (Fin.ext h)
  · intro i b
    rw [Matrix.submatrix_apply, id_eq]
    obtain ⟨_, hnb, _⟩ := hWCB
    refine hnb (Fin.cast hMq.symm i) (by simp [Fin.cast])
      (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr b)) ?_
    simp only [Fin.coe_cast, deepWidthEquiv, Equiv.trans_apply, finCongr_apply, Fin.coe_cast,
      finSumFinEquiv_apply_right, Fin.coe_natAdd]
    omega

/-- **The η-uniform `Λ₀`-entry bound.** `∃ Acc_Λ ≥ 0` such that for EVERY `0 ≤ η ≤ δ` there are `γ, nb`
with `nb ≤ η·Acc_Λ`, `((r−1)·nb < (δ/2)^{L−1−q} − η·Acc_Λ → 0 < γ)`, and (if `γ > 0`) `|Lam0uG u a b| ≤
(1/γ)·nb` for every front-carrier `u` with `det (P₁ᵀP₁) ≠ 0`. -/
theorem Lam0uG_entry_bound_uniformEta (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) {δ : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (q : ℕ) (hq : q < L + 1) (hqL : q ≤ L - 1) (hMq : M ⟨q, hq⟩ = r)
    (hwidth : ∀ t : ℕ, t < L → r ≤ Wext M t) :
    ∃ Acc : ℝ, 0 ≤ Acc ∧ ∀ (η : ℝ), 0 ≤ η → η ≤ δ →
      ∃ (γ nb : ℝ), 0 ≤ nb ∧ nb ≤ η * Acc
        ∧ (((r : ℝ) - 1) * nb < (δ / 2) ^ (L - 1 - q) - η * Acc → 0 < γ)
        ∧ (0 < γ → ∀ (u : Fin (routeMAmbient M) → ℝ),
            (∀ t : Fin L, q ≤ (t : ℕ) → (t : ℕ) < L - 1 → CarrierLayer (frontTupleG M u t) r δ η) →
            ((P1uG M hL hrs u).transpose * P1uG M hL hrs u).det ≠ 0 →
            ∀ a : Fin r, ∀ b : Fin s, |Lam0uG M hL hrs u a b| ≤ (1 / γ) * nb) := by
  obtain ⟨Acc, hAcc0, hdata⟩ :=
    waist_carrier_data_uniformEta M hL hrs hδ q hq hqL hMq hwidth
  refine ⟨Acc, hAcc0, fun η hη hηδ => ?_⟩
  obtain ⟨dlb, nb, hnb0, hnbA, hdlbA, hdataη⟩ := hdata η hη hηδ
  refine ⟨dlb - ((r : ℝ) - 1) * nb, nb, hnb0, hnbA, ?_, ?_⟩
  · intro hsmall
    have : ((r : ℝ) - 1) * nb < dlb := lt_of_lt_of_le hsmall hdlbA
    linarith
  · intro hγpos u hlayers hgram a b
    obtain ⟨U, V, hUV, hVρbound, hVσbound⟩ := hdataη u hlayers
    set Vρ : Matrix (Fin r) (Fin r) ℝ := V.submatrix (id : Fin r → Fin r)
      (fun k : Fin r => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k)) with hVρdef
    set Vσ : Matrix (Fin r) (Fin s) ℝ := V.submatrix (id : Fin r → Fin r)
      (fun j : Fin s => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr j)) with hVσdef
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have hdomlt : ((r : ℝ) - 1) * nb < dlb := by linarith [hγpos]
    have hSRD : StrictRowDominant Vρ (dlb - ((r : ℝ) - 1) * nb) :=
      hVρbound.strictRowDominant hdomlt
    have hVρdet : Vρ.det ≠ 0 := hSRD.det_ne_zero
    have hLamEq : Lam0uG M hL hrs u = Vρ⁻¹ * Vσ := by
      have hP1 : P1uG M hL hrs u = U * Vρ := P1uG_eq_mul_Vrho hL hrs u U V hUV
      have hP2 : P2uG M hL hrs u = U * Vσ := by
        funext i j
        rw [P2uG, hUV, Matrix.mul_apply, Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun a _ => by rw [hVσdef, Matrix.submatrix_apply]; rfl)
      have hunitVρ : IsUnit Vρ.det := isUnit_iff_ne_zero.mpr hVρdet
      have hfacP : P2uG M hL hrs u = P1uG M hL hrs u * (Vρ⁻¹ * Vσ) := by
        rw [hP2, hP1]
        calc U * Vσ = U * (1 : Matrix (Fin r) (Fin r) ℝ) * Vσ := by rw [Matrix.mul_one]
          _ = U * (Vρ * Vρ⁻¹) * Vσ := by rw [Matrix.mul_nonsing_inv _ hunitVρ]
          _ = U * Vρ * (Vρ⁻¹ * Vσ) := by simp only [Matrix.mul_assoc]
      rw [Lam0uG, hfacP, gram_routing_eq_factor _ _ hgram]
    rw [hLamEq]
    have hcol : ∀ i, |Vσ i b| ≤ nb := fun i => hVσbound i b
    exact hSRD.inv_mul_entry_bound Vσ b (Mj := nb) hcol a

end DLNFibre.DLN.RLCT
