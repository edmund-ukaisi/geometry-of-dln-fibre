import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankGeneric
import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceAssembly
import DLNFibre.DLN.RLCT.Validate.DeepestCoreNonvanishing

set_option linter.style.longLine false

/-!
# `RouteMSJDeepRankGen` — the deep-factor generic-rank input `hZrank` (rankgen route (c))

**Thread `genm-arch1build` (aoyagi-full Stage 2), the ARCH-1 mint-path — the ONE genuinely-new AG input
the coupled-incidence route needs** (arch1probe §1.3 (ii); rankgen cert §4 route (c)).

`hGae_from_deepRank` (`RouteMSJCorankGeneric`) reduces the joint corank-Gram positivity `hGae` to the
deep-factor generic rank `hZrank : ∀ᵐ z, M₁−u ≤ rank (deeperFlagZdeep M u z)`. This module DISCHARGES the
generic-rank content:

> **Generic rank of a chain product = min width.** For a chain `H : Fin (N+1) → ℕ` and `ρ ≤ H i` (all `i`),
> a.e. parameter `A` has `ρ ≤ rank (prod H A)`. (`prod_minor_rank_ge_ae`)

Deep factor: `deeperFlagZdeep M u z = prod (dropHead (redChain u M)) ((paramsHeadSplit … z).2)` is the
product of the deep-tail layers of widths `(M₂,…,M_last)`, whose min is `deepTailMin M`. So
`∀ᵐ z, deepTailMin M ≤ rank (deeperFlagZdeep M u z)` (`deepFactor_rank_ge_deepTailMin_ae`), transferred
from the general lemma along the measure-preserving head split + `Prod.snd`. Feeding
`b := M₁−u ≤ deepTailMin M` (the caller's binding-cut Nat fact) gives the `hGae_from_deepRank` input
(`deepFactor_hZrank_of_le`).

Proof shape (mirrors `corank_survival_ae` / `DeepestCoreNonvanishing`): the top-left `ρ×ρ` minor of
`prod H A` is `eval (flat A)` of a fixed polynomial `prodMinorPoly`; it is `≠ 0` because the
rectangular-identity witness `rectId H` makes that minor `= det (1) = 1`; a nonzero polynomial is a.e.
nonzero (`MvPolynomial.ae_eval_ne_zero` + `measurePreserving_paramsEquivFlat`); a nonzero minor forces
`rank ≥ ρ` (`Core.submatrix_det_eq_zero_of_rank_le`). Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory MvPolynomial
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## A generic cast-entry helper (the `DeepestCoreNonvanishing.cast_e00_entry` form, any `f`) -/

/-- A dimension-cast pushes through to entries of an `of` matrix: the cast preserves the entry formula,
with the indices `Fin.cast`-ed. (The `cast_e00_entry` proof, generalised to any `f`.) -/
private theorem cast_of_entry {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    (h : Matrix (Fin a) (Fin b) ℝ = Matrix (Fin a') (Fin b') ℝ)
    (f : Fin a → Fin b → ℝ) (i : Fin a') (j : Fin b') :
    (cast h (Matrix.of f)) i j = f (Fin.cast ha.symm i) (Fin.cast hb.symm j) := by
  subst ha; subst hb; rfl

/-! ## The rectangular-identity witness -/

/-- The rectangular-identity parameter: every layer is `[i = j]` (the rectangular identity). Its layer
product's top-left `ρ×ρ` block is the identity for any `ρ` below every width — the achievability witness
for `rank (prod H ·) = min width`. -/
noncomputable def rectId (H : Fin (L + 1) → ℕ) : Params H :=
  fun _ => Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0

/-- **The top-left `ρ×ρ` block of the rectangular-identity product is the identity.** For any `ρ` at most
every width, `prodAux H (rectId H) k` restricted to indices `< ρ` is `[i = j]` (induction on chain
length; each layer contributes a single `[l = j]` at the valid middle index). -/
theorem prodAux_rectId_topleft (H : Fin (L + 1) → ℕ) (ρ : ℕ) (hρ : ∀ i, ρ ≤ H i) :
    ∀ (k : ℕ) (hk : k < L + 1) (i : Fin (H 0)) (j : Fin (H ⟨k, hk⟩)),
      (i : ℕ) < ρ → (j : ℕ) < ρ →
        prodAux H (rectId H) k hk i j = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0 := by
  intro k
  induction k with
  | zero =>
      intro hk i j hi hj
      -- `prodAux 0 = 1`; `(1) i j = [i = j] = [↑i = ↑j]`.
      show (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) i j = _
      rw [Matrix.one_apply]
      by_cases h : (i : ℕ) = (j : ℕ)
      · rw [if_pos (Fin.ext h), if_pos h]
      · rw [if_neg (fun he => h (by rw [he])), if_neg h]
  | succ k ih =>
      intro hk i j hi hj
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      set Lyr : Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ :=
        (by rw [e1, e2]; exact rectId H ⟨k, hkL⟩) with hLyr
      have hLyr_entry : ∀ (a : Fin (H ⟨k, hk'⟩)) (b : Fin (H ⟨k + 1, hk⟩)),
          Lyr a b = if (a : ℕ) = (b : ℕ) then (1 : ℝ) else 0 := by
        intro a b
        simp only [hLyr, rectId, eq_mpr_eq_cast, cast_cast]
        exact (cast_of_entry (congrArg H e1) (congrArg H e2) (by rw [e1, e2]) _ a b).trans (by
          simp)
      -- middle-width bound: `ρ ≤ H ⟨k, hk'⟩`, so `⟨↑j, _⟩` is a valid middle index
      have hjmid : (j : ℕ) < H ⟨k, hk'⟩ := lt_of_lt_of_le hj (hρ _)
      show (prodAux H (rectId H) k hk' * Lyr) i j = _
      rw [Matrix.mul_apply,
        Finset.sum_eq_single (⟨(j : ℕ), hjmid⟩ : Fin (H ⟨k, hk'⟩))]
      · rw [hLyr_entry, ih hk' i ⟨(j : ℕ), hjmid⟩ hi (by simpa using hj)]
        simp
      · intro l _ hl
        have hlj : (l : ℕ) ≠ (j : ℕ) := fun h => hl (Fin.ext (by simpa using h))
        rw [hLyr_entry, if_neg hlj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The `ρ×ρ`-minor polynomial and its a.e. non-vanishing -/

/-- **The top-left `ρ×ρ`-minor polynomial** of the chain product, in the flat coordinates of `Params H`.
Its `eval (flat A)` is the top-left `ρ×ρ` minor of `prod H A` (`eval_prodMinorPoly`). -/
noncomputable def prodMinorPoly (H : Fin (L + 1) → ℕ) (ρ : ℕ) (hρ0 : ρ ≤ H 0)
    (hρlast : ρ ≤ H (Fin.last L)) : MvPolynomial (Fin (flatDim H)) ℝ :=
  ((prodPolyAux H (coreXmat H) L (Nat.lt_succ_self L)).submatrix
      (Fin.castLE hρ0) (Fin.castLE hρlast)).det

/-- **The minor-polynomial encoding.** `eval z (prodMinorPoly H ρ …)` is the top-left `ρ×ρ` minor of
`prod H ((paramsEquivFlat H).symm z)`. The `prodPolyAux`-over-`coreXmat` maps (under `eval z`) to
`prodAux H (flatSymm z) = prod H (flatSymm z)` (`prodPolyAux_map` + `coreXmat_map_eval` +
`prodPolyAux_eq_prodAux`), and `eval z` commutes with `det`/`submatrix`. -/
theorem eval_prodMinorPoly (H : Fin (L + 1) → ℕ) (ρ : ℕ) (hρ0 : ρ ≤ H 0)
    (hρlast : ρ ≤ H (Fin.last L)) (z : Fin (flatDim H) → ℝ) :
    MvPolynomial.eval z (prodMinorPoly H ρ hρ0 hρlast)
      = ((prod H ((paramsEquivFlat H).symm z)).submatrix
          (Fin.castLE hρ0) (Fin.castLE hρlast)).det := by
  have hmapM : (prodPolyAux H (coreXmat H) L (Nat.lt_succ_self L)).map (MvPolynomial.eval z)
      = prod H ((paramsEquivFlat H).symm z) := by
    rw [prodPolyAux_map (MvPolynomial.eval z) H (coreXmat H)
      (fun s => ((paramsEquivFlat H).symm z) s) (coreXmat_map_eval H z) L (Nat.lt_succ_self L),
      prodPolyAux_eq_prodAux]
    rfl
  rw [prodMinorPoly, RingHom.map_det]
  exact congrArg Matrix.det
    (congrArg (fun M => M.submatrix (Fin.castLE hρ0) (Fin.castLE hρlast)) hmapM)

/-- **The minor polynomial is nonzero** — the rectangular-identity witness makes the top-left `ρ×ρ`
minor of `prod H (rectId H)` equal to `det (1) = 1`. -/
theorem prodMinorPoly_ne_zero (H : Fin (L + 1) → ℕ) (ρ : ℕ) (hρ : ∀ i, ρ ≤ H i)
    (hρ0 : ρ ≤ H 0) (hρlast : ρ ≤ H (Fin.last L)) :
    prodMinorPoly H ρ hρ0 hρlast ≠ 0 := by
  intro hzero
  have hev := eval_prodMinorPoly H ρ hρ0 hρlast (paramsEquivFlat H (rectId H))
  rw [hzero, map_zero] at hev
  rw [show (paramsEquivFlat H).symm (paramsEquivFlat H (rectId H)) = rectId H from by simp] at hev
  -- the top-left `ρ×ρ` minor of `prod H (rectId H)` is the identity, det `1`
  have hI : (prod H (rectId H)).submatrix (Fin.castLE hρ0) (Fin.castLE hρlast)
      = (1 : Matrix (Fin ρ) (Fin ρ) ℝ) := by
    ext i j
    rw [Matrix.submatrix_apply]
    show prodAux H (rectId H) L (Nat.lt_succ_self L) (Fin.castLE hρ0 i) (Fin.castLE hρlast j) = _
    rw [prodAux_rectId_topleft H ρ hρ L (Nat.lt_succ_self L) (Fin.castLE hρ0 i) (Fin.castLE hρlast j)
        (by rw [Fin.val_castLE]; exact i.isLt) (by rw [Fin.val_castLE]; exact j.isLt),
      Matrix.one_apply]
    simp only [Fin.val_castLE]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos h, if_pos (Fin.ext h)]
    · rw [if_neg h, if_neg (fun he => h (by rw [he]))]
  rw [hI, Matrix.det_one] at hev
  exact one_ne_zero hev.symm

/-- **Generic rank of a chain product ≥ min width** (the `≥` half; the `≤` half is deterministic and not
needed downstream). For a chain `H` and `ρ ≤ H i` for every `i`, a.e. parameter `A` has
`ρ ≤ rank (prod H A)`. The top-left `ρ×ρ` minor is `eval (flat A)` of the nonzero
`prodMinorPoly`, hence `≠ 0` a.e. (`MvPolynomial.ae_eval_ne_zero` + `measurePreserving_paramsEquivFlat`);
a nonzero `ρ×ρ` minor forces `rank ≥ ρ` (`Core.submatrix_det_eq_zero_of_rank_le`). -/
theorem prod_minor_rank_ge_ae {N : ℕ} (H : Fin (N + 1) → ℕ) (ρ : ℕ) (hρ : ∀ i, ρ ≤ H i) :
    ∀ᵐ A ∂(volume : Measure (Params H)), ρ ≤ (prod H A).rank := by
  rcases Nat.eq_zero_or_pos ρ with h0 | hpos
  · filter_upwards with A; omega
  obtain ⟨r, rfl⟩ : ∃ r, ρ = r + 1 := ⟨ρ - 1, by omega⟩
  have hρ0 : r + 1 ≤ H 0 := hρ 0
  have hρlast : r + 1 ≤ H (Fin.last N) := hρ (Fin.last N)
  have hne := prodMinorPoly_ne_zero H (r + 1) hρ hρ0 hρlast
  have hae := MvPolynomial.ae_eval_ne_zero (prodMinorPoly H (r + 1) hρ0 hρlast) hne
  filter_upwards [(measurePreserving_paramsEquivFlat H).quasiMeasurePreserving.ae hae] with A hA
  rw [eval_prodMinorPoly,
    show (paramsEquivFlat H).symm (paramsEquivFlat H A) = A from by simp] at hA
  by_contra hlt
  rw [not_le] at hlt
  exact hA (Core.submatrix_det_eq_zero_of_rank_le (A := prod H A) (r := r) (by omega)
    (Fin.castLE hρ0) (Fin.castLE hρlast))

/-! ## Specialisation to the deep factor `deeperFlagZdeep` -/

/-- `deepTailMin M ≤ dropHead (redChain u M) i` for every `i` — the deep-tail minimum is below every
deep-tail width (`Finset.inf'_le`, after `dropHead (redChain u M) i = M i.succ.succ`). -/
theorem deepTailMin_le_dropHead_redChain (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (i : Fin (L + 1)) :
    deepTailMin M ≤ dropHead (redChain u M) i := by
  have hi : dropHead (redChain u M) i = M i.succ.succ := by
    rw [dropHead]; exact redChain_succ u M i
  rw [hi, deepTailMin]
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- **The deep-factor generic rank** `∀ᵐ z, deepTailMin M ≤ rank (deeperFlagZdeep M u z)` (rankgen route
(c)). `deeperFlagZdeep M u z = prod (dropHead (redChain u M)) ((paramsHeadSplit … z).2)`, so the generic
rank of the deep-tail product (`prod_minor_rank_ge_ae` with `ρ = deepTailMin M`) transfers along the
quasi-measure-preserving `Prod.snd ∘ paramsHeadSplit` (measure-preserving head split + `Prod.snd`). -/
theorem deepFactor_rank_ge_deepTailMin_ae (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) :
    ∀ᵐ z ∂(volume : Measure (Params (redChain u M))),
      deepTailMin M ≤ (deeperFlagZdeep M u z).rank := by
  have hgen := prod_minor_rank_ge_ae (dropHead (redChain u M)) (deepTailMin M)
    (deepTailMin_le_dropHead_redChain M u)
  have hHS : Measure.QuasiMeasurePreserving (paramsHeadSplit (redChain u M))
      (volume : Measure (Params (redChain u M)))
      ((volume : Measure (Fin (redChain u M 0) → Fin (redChain u M 1) → ℝ)).prod
        (volume : Measure (Params (dropHead (redChain u M))))) := by
    rw [← Measure.volume_eq_prod]
    exact (paramsHeadSplit_mp (redChain u M)).quasiMeasurePreserving
  filter_upwards [(Measure.quasiMeasurePreserving_snd.comp hHS).ae hgen] with z hz
  exact hz

/-- **The `hGae_from_deepRank` input `hZrank`, given the caller's binding-cut Nat fact
`M₁−u ≤ deepTailMin M`.** Restricts the full-space generic rank to the parameter box and monotonises
`M₁−u ≤ deepTailMin M ≤ rank`. This is the exact hypothesis the coupled-incidence route's `hGae` reduces
to (`hGae_from_deepRank`), with `M₁−u ≤ deepTailMin M` supplied at the binding cut
(`tailWidth_le_deepTailMin_of_binding`). -/
theorem deepFactor_hZrank_of_le (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hb : M 1 - u ≤ deepTailMin M) :
    ∀ᵐ z ∂(volume.restrict (paramsBoxM (redChain u M) 1)),
      M 1 - u ≤ (deeperFlagZdeep M u z).rank := by
  filter_upwards [ae_restrict_of_ae (deepFactor_rank_ge_deepTailMin_ae M u)] with z hz
  exact le_trans hb hz

end DLNFibre.DLN.RLCT
