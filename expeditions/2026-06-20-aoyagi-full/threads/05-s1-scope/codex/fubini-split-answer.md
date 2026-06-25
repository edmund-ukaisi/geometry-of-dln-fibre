Use a two-case split on `lamH = 0`. The clean ENNReal move is `ENNReal.exists_lt_add_of_lt_add`; it gives the strict `a < 1/2` automatically when `lamH ≠ 0`.

```lean
-- Useful local facts.
have half_ne_zero : (1 / 2 : ℝ≥0∞) ≠ 0 := by
  rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : NNReal) : ℝ≥0∞) by simp]
  exact_mod_cast (by norm_num : (1 / 2 : NNReal) ≠ 0)

have half_ne_top : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by
  rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : NNReal) : ℝ≥0∞) by simp]
  exact ENNReal.coe_ne_top

have half_toReal : ((1 / 2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by
  rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : NNReal) : ℝ≥0∞) by simp]
  simp

apply le_of_forall_lt_imp_le_of_dense
intro q hq

have push_to_sSup :
    ∀ (a b : ℝ), 0 ≤ a → a < 1 / 2 → 0 ≤ b →
      q ≤ ENNReal.ofReal (a + b) →
      (∃ Ω : Set Y, IsOpen Ω ∧ y0 ∈ Ω ∧
        IntegrableOn (fun y => |H y| ^ (-b)) Ω volume) →
      q ≤ sSup S_joint := by
  intro a b ha0 halt hb0 hqle hcore
  have hab0 : 0 ≤ a + b := by linarith
  have hjoint := joint_admissible_of_split a b ha0 halt hb0 hcore
  refine le_sSup_of_le ?hmem hqle
  rcases hjoint with ⟨Ω, hΩopen, hpΩ, hint⟩
  refine ⟨⟨a + b, hab0⟩, ?_, Ω, hΩopen, ?_, ?_⟩
  · exact ENNReal.ofReal_eq_coe_nnreal hab0
  · -- if your `S_joint` uses `{(0,y0)} ⊆ Ω`, use singleton intro here
    simpa using hpΩ
  · change IntegrableOn
      (fun p => |joint p| ^ (-(a + b)) * (1 : ℝ)) Ω volume
    exact hint

by_cases hlam0 : lamH = 0
· -- Then q < 1/2, so choose a strictly between q and 1/2; b = 0.
  have hqhalf : q < (1 / 2 : ℝ≥0∞) := by
    simpa [hlam0] using hq
  obtain ⟨r, hqr, hrhalf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqhalf
  refine push_to_sSup (r : ℝ) 0 (by positivity) ?_ (by norm_num) ?_ ?_
  · have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top half_ne_top).2 hrhalf
    rwa [half_toReal] at this
  · simpa using hqr.le
  · simpa using core_admissible_zero
· -- Nonzero core threshold: split q below the sum with both pieces strictly below.
  obtain ⟨u, huhalf, v, hvlam, hquv⟩ :=
    ENNReal.exists_lt_add_of_lt_add hq half_ne_zero hlam0
  let a : ℝ := u.toReal
  let b : NNReal := v.toNNReal
  have hvfin : v ≠ ⊤ := hvlam.ne_top
  have ha_lt : a < 1 / 2 := by
    have := (ENNReal.toReal_lt_toReal huhalf.ne_top half_ne_top).2 huhalf
    rwa [half_toReal] at this
  have hb_lt : (b : ℝ≥0∞) < lamH := by
    simpa [b, ENNReal.coe_toNNReal hvfin] using hvlam
  have hqle : q ≤ ENNReal.ofReal (a + (b : ℝ)) := by
    have hsum : ENNReal.ofReal (a + (b : ℝ)) = u + v := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity : 0 ≤ (b : ℝ))]
      rw [show ENNReal.ofReal a = u by
        simpa [a] using ENNReal.ofReal_toReal huhalf.ne_top]
      rw [show ENNReal.ofReal (b : ℝ) = v by
        rw [show ENNReal.ofReal (b : ℝ) = (b : ℝ≥0∞) by simp]
        simpa [b] using ENNReal.coe_toNNReal hvfin]
    exact hquv.le.trans_eq hsum.symm
  exact push_to_sSup a (b : ℝ) ENNReal.toReal_nonneg ha_lt (by positivity) hqle
    (core_admissible_of_lt b hb_lt)
```

Lemma-name status:

- `le_of_forall_lt_imp_le_of_dense`: **CONFIDENT-exists**
- `ENNReal.exists_lt_add_of_lt_add`: **CONFIDENT-exists**
- `ENNReal.lt_iff_exists_nnreal_btwn`: **CONFIDENT-exists**
- `ENNReal.coe_toNNReal`, `ENNReal.ofReal_toReal`, `ENNReal.ofReal_add`: **CONFIDENT-exists**
- `le_sSup_of_le`, `le_sSup`, `sSup_le_sSup`: **CONFIDENT-exists**

A set-level `sSup_image2` route is possible, but I would not use it here unless you already have named smooth/core admissible sets and their `sSup` values. You would need to prove `Set.image2 (· + ·) S_smooth S_core ⊆ S_joint` and then identify `sSup (Set.image2 ...) = sSup S_smooth + sSup S_core` using `ENNReal.sSup_add` / `ENNReal.add_sSup`. The dense pointwise proof above is usually less brittle and handles `lamH = 0` and `lamH = ⊤` explicitly.