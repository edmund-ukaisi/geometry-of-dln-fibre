import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.MinAdmPermInvariance
import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSuffixBridge

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJWaistReversalCoV` — the box-integral reversal invariance

**Thread `genm-sj5-waist` (aoyagi-full Stage 2), hole (c) `deeperFlagWaist_finite`, the O2 brick.** The
layer-product box integral is invariant under REVERSING the chain (`M ↦ M ∘ Fin.rev`). Reversing the
layer order and transposing each layer sends the tuple `A = (A₀,…,A_{L−1})` to the reversed-transposed
tuple whose product is `(prod M A)ᵀ`, and `frobSq` is transpose-invariant, so the two box integrals are
EQUAL (`routeMLayerBoxIntegral_comp_rev`). Since `minAdm (M ∘ Fin.rev) = minAdm M` (permutation
invariance at `Fin.revPerm`), the two thresholds coincide, hence `RouteMBoxThresholdFinite` transfers
(`routeMBoxThresholdFinite_of_rev`).

This is the arity-recursion enabler for the `≥ 4`-width waist branch: a `≥ 4`-width waist `M` reverses to
a GOOD chain (`rev M` head-split-good — deep-tail min ≤ pivot), so the good-case machinery
(`deeperFlagGood_finite`) discharges `RouteMBoxThresholdFinite (rev M)`, and this brick transfers it back
to `M`. The 3-width waist base needs no reversal (`routeMBoxThresholdFinite_mnp`).

UNTRACKED, NOT wired into `DLNFibre.lean`/`AxCheck` — the canonical library stays 0-sorry.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## The reversal-transpose change-of-variables on the layer product (`prod_revParams`) -/

/-- The reversal-transpose CoV map on parameter tuples: `revParams M A s = (A (Fin.rev s))ᵀ`, reindexed
into the reversed chain's widths. -/
noncomputable def revParams (M : Fin (L + 1) → ℕ) (A : Params M) : Params (M ∘ Fin.rev) :=
  fun s => Matrix.reindex
    (finCongr (show M (Fin.rev s).succ = (M ∘ Fin.rev) s.castSucc by
      simp only [Function.comp_apply]; rw [Fin.rev_castSucc]))
    (finCongr (show M (Fin.rev s).castSucc = (M ∘ Fin.rev) s.succ by
      simp only [Function.comp_apply]; rw [Fin.rev_succ]))
    (A (Fin.rev s))ᵀ

/-- `frobSq` is invariant under transpose (`∑∑ (Xᵀ)² = ∑∑ X²`, `Finset.sum_comm`). -/
theorem frobSq_transpose {a b : Type*} [Fintype a] [Fintype b] (X : Matrix a b ℝ) :
    frobSq (Xᵀ) = frobSq X := by
  unfold frobSq
  rw [Finset.sum_comm]
  rfl

/-- `frobSq` is invariant under `reindex` by any equivalences (relabelling the double sum). -/
theorem frobSq_reindex {a b a' b' : Type*} [Fintype a] [Fintype b] [Fintype a'] [Fintype b']
    (ea : a ≃ a') (eb : b ≃ b') (X : Matrix a b ℝ) :
    frobSq (Matrix.reindex ea eb X) = frobSq X := by
  unfold frobSq
  rw [← Equiv.sum_comp ea (fun i => ∑ j, (Matrix.reindex ea eb X i j) ^ 2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Equiv.sum_comp eb (fun j => (Matrix.reindex ea eb X (ea i) j) ^ 2)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- **Layer-index transport.** A reindexed raw layer that equals `(A idx1)ᵀ` also equals `(A idx2)ᵀ` for
any propositionally-equal index `idx2` (with the matching width proofs) — via `subst` on the bound indices,
then `finCongr` proof-irrelevance. Bridges the non-defeq reversal-index shift in the prefix recursion. -/
theorem shift_layer {L : ℕ} (H : Fin (L + 1) → ℕ) (A : Params H) {p q : ℕ}
    (X : Matrix (Fin p) (Fin q) ℝ) (idx1 idx2 : Fin L) (hidx : idx1 = idx2)
    (hr1 : p = H idx1.succ) (hc1 : q = H idx1.castSucc)
    (hval : Matrix.reindex (finCongr hr1) (finCongr hc1) X = (A idx1)ᵀ)
    (hr2 : p = H idx2.succ) (hc2 : q = H idx2.castSucc) :
    Matrix.reindex (finCongr hr2) (finCongr hc2) X = (A idx2)ᵀ := by
  subst hidx; exact hval

/-- **The reversed raw product is the transpose of the prefix product.** For a width family `W` and raw
layers `a` whose reindex is the transposed layer `(A ⟨k-(t+1)⟩)ᵀ` at every `t < k` (i.e. `a` runs the
LAST `k` layers of `A`, reversed and transposed), the raw front-peel product `rawProd W a k` reindexes to
`(prodAux H A k)ᵀ`. Induction on the prefix length `k`: `rawProd_succ` peels `a 0` (= `(A ⟨k⟩)ᵀ`),
`prodAux_succ`+`transpose_mul` peels `(A ⟨k⟩)ᵀ` off the front of the transpose, and the IH on the shifted
families `(W∘succ, a∘succ)` matches the tails (`shift_layer` bridges the reversal-index shift). -/
theorem rawProd_rev_prefix_eq_transpose (H : Fin (L + 1) → ℕ) (A : Params H) :
    ∀ (k : ℕ) (hk : k < L + 1)
      (W : ℕ → ℕ) (a : (t : ℕ) → Matrix (Fin (W t)) (Fin (W (t + 1))) ℝ)
      (hfirst : W 0 = H ⟨k, hk⟩) (hlast : W k = H 0)
      (hrow : ∀ t (ht : t < k), W t = H ((⟨k - (t + 1), by omega⟩ : Fin L).succ))
      (hcol : ∀ t (ht : t < k), W (t + 1) = H ((⟨k - (t + 1), by omega⟩ : Fin L).castSucc))
      (_hlayer : ∀ t (ht : t < k),
        Matrix.reindex (finCongr (hrow t ht)) (finCongr (hcol t ht)) (a t)
          = (A (⟨k - (t + 1), by omega⟩ : Fin L))ᵀ),
      Matrix.reindex (finCongr hfirst) (finCongr hlast) (rawProd W a k)
        = (prodAux H A k hk)ᵀ := by
  intro k
  induction k with
  | zero =>
      intro hk W a hfirst hlast _hrow _hcol _hlayer
      rw [rawProd_zero, Matrix.reindex_apply]
      conv_rhs => rw [show (prodAux H A 0 hk) = (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) from rfl]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.one_apply,
        finCongr_symm, finCongr_apply]
      congr 1
      simp only [eq_iff_iff, Fin.ext_iff, Fin.val_cast]
      omega
  | succ k ih =>
      intro hk W a hfirst hlast hrow hcol hlayer
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      rw [rawProd_succ]
      have e1 : H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))
          = H ((⟨k, hkL⟩ : Fin L).castSucc) := by apply congrArg; apply Fin.ext; simp [Fin.castSucc]
      have e2 : H (⟨k + 1, hk⟩ : Fin (L + 1))
          = H ((⟨k, hkL⟩ : Fin L).succ) := by apply congrArg; apply Fin.ext; simp [Fin.succ]
      rw [prodAux_succ H A k hk e1 e2, Matrix.transpose_mul, Matrix.transpose_reindex]
      have hmid : W 1 = H ((⟨k, hkL⟩ : Fin L).castSucc) := by
        have h := hcol 0 (by omega); rw [h]; apply congrArg; apply Fin.ext
        simp only [Fin.val_castSucc]; omega
      rw [reindex_finCongr_mul hfirst hmid hlast (a 0)
        (rawProd (fun t => W (t + 1)) (fun t => a (t + 1)) k)]
      refine congrArg₂ (· * ·) ?_ ?_
      · have hl0 := hlayer 0 (by omega)
        have key : Matrix.reindex (finCongr hfirst) (finCongr hmid) (a 0)
            = Matrix.reindex (finCongr e2.symm) (finCongr e1.symm)
                (Matrix.reindex (finCongr (hrow 0 (by omega))) (finCongr (hcol 0 (by omega))) (a 0)) := by
          simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
          congr 1 <;> · ext x; simp [finCongr]
        rw [key, hl0]
        rfl
      · have hkk : k < L + 1 := Nat.lt_of_succ_lt hk
        have hfirst' : (fun t => W (t + 1)) 0 = H ⟨k, hkk⟩ := by
          show W 1 = H ⟨k, hkk⟩; rw [hmid]; apply congrArg; apply Fin.ext; simp [Fin.castSucc]
        have hlast' : (fun t => W (t + 1)) k = H 0 := hlast
        have hrow' : ∀ t (ht : t < k),
            (fun t => W (t + 1)) t = H ((⟨k - (t + 1), by omega⟩ : Fin L).succ) := by
          intro t ht
          have h := hrow (t + 1) (by omega)
          show W (t + 1) = _; rw [h]; apply congrArg; apply Fin.ext
          simp only [Fin.val_succ]; omega
        have hcol' : ∀ t (ht : t < k),
            (fun t => W (t + 1)) (t + 1) = H ((⟨k - (t + 1), by omega⟩ : Fin L).castSucc) := by
          intro t ht
          have h := hcol (t + 1) (by omega)
          show W (t + 1 + 1) = _; rw [h]; apply congrArg; apply Fin.ext
          simp only [Fin.val_castSucc]; omega
        have hlayer' : ∀ t (ht : t < k),
            Matrix.reindex (finCongr (hrow' t ht)) (finCongr (hcol' t ht)) ((fun t => a (t + 1)) t)
              = (A (⟨k - (t + 1), by omega⟩ : Fin L))ᵀ := by
          intro t ht
          have hl := hlayer (t + 1) (by omega)
          exact shift_layer H A (a (t + 1)) (⟨(k + 1) - (t + 1 + 1), by omega⟩ : Fin L)
            (⟨k - (t + 1), by omega⟩ : Fin L) (by apply Fin.ext; simp only [Fin.val_mk]; omega)
            (hrow (t + 1) (by omega)) (hcol (t + 1) (by omega)) hl
            (hrow' t ht) (hcol' t ht)
        have hih := ih hkk (fun t => W (t + 1)) (fun t => a (t + 1)) hfirst' hlast' hrow' hcol' hlayer'
        rw [← hih]
        simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
        congr 1 <;> · ext x; simp [finCongr]

/-- **The reversal change-of-variables on the layer product** (the crux identity): the product of the
reversed-transposed chain is the transpose of the product, up to a width reindex. Combines the
`rawProd`-to-`prod` bridge on `M ∘ Fin.rev` / `revParams M A` with the reversed-prefix invariant on
`M` / `A`. -/
theorem prod_revParams (M : Fin (L + 1) → ℕ) (A : Params M)
    (h_row : M (Fin.last L) = (M ∘ Fin.rev) 0)
    (h_col : M 0 = (M ∘ Fin.rev) (Fin.last L)) :
    prod (M ∘ Fin.rev) (revParams M A)
      = Matrix.reindex (finCongr h_row) (finCongr h_col) ((prod M A)ᵀ) := by
  classical
  set W : ℕ → ℕ := fun n => (M ∘ Fin.rev) ⟨min n L, Nat.lt_succ_of_le (Nat.min_le_right n L)⟩ with hWdef
  have hW : ∀ (k : ℕ) (hk : k ≤ L), W k = (M ∘ Fin.rev) ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k hk; rw [hWdef]; apply congrArg; apply Fin.ext; simp [Nat.min_eq_left hk]
  have hcast : ∀ (k : ℕ) (h : k < L),
      (M ∘ Fin.rev) ((⟨k, h⟩ : Fin L).castSucc) = W k ∧
      (M ∘ Fin.rev) ((⟨k, h⟩ : Fin L).succ) = W (k + 1) := by
    intro k h
    refine ⟨?_, ?_⟩
    · rw [hW k (le_of_lt h)]; apply congrArg; apply Fin.ext; simp [Fin.castSucc]
    · rw [hW (k + 1) h]; apply congrArg; apply Fin.ext; simp [Fin.succ]
  set a : (t : ℕ) → Matrix (Fin (W t)) (Fin (W (t + 1))) ℝ := fun t =>
    if h : t < L then
      Matrix.reindex (finCongr (hcast t h).1) (finCongr (hcast t h).2) (revParams M A ⟨t, h⟩)
    else 0 with hadef
  have hA : ∀ (k : ℕ) (hk : k < L),
      Matrix.reindex (finCongr (hW k (le_of_lt hk))) (finCongr (hW (k + 1) hk)) (a k)
        = (revParams M A ⟨k, hk⟩ :
            Matrix (Fin ((M ∘ Fin.rev) (⟨k, Nat.lt_succ_of_le (le_of_lt hk)⟩ : Fin (L + 1))))
              (Fin ((M ∘ Fin.rev) (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (L + 1)))) ℝ) := by
    intro k hk
    rw [hadef]; simp only [dif_pos hk]
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
    congr 1 <;> · ext x; simp [finCongr]
  have hbridge := rawProd_reindex_eq_prod L (M ∘ Fin.rev) (revParams M A) W a hW hA
  have hrow : ∀ t (ht : t < L), W t = M ((⟨L - (t + 1), by omega⟩ : Fin L).succ) := by
    intro t ht
    rw [hW t (le_of_lt ht)]; simp only [Function.comp_apply]; apply congrArg; apply Fin.ext
    simp only [Fin.val_rev, Fin.val_succ, Fin.val_mk]; omega
  have hcol : ∀ t (ht : t < L), W (t + 1) = M ((⟨L - (t + 1), by omega⟩ : Fin L).castSucc) := by
    intro t ht
    rw [hW (t + 1) ht]; simp only [Function.comp_apply]; apply congrArg; apply Fin.ext
    simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_mk]; omega
  have hlayer : ∀ t (ht : t < L),
      Matrix.reindex (finCongr (hrow t ht)) (finCongr (hcol t ht)) (a t)
        = (A (⟨L - (t + 1), by omega⟩ : Fin L))ᵀ := by
    intro t ht
    have hr1 : W t = M ((Fin.rev (⟨t, ht⟩ : Fin L)).succ) := by
      rw [hW t (le_of_lt ht)]; simp only [Function.comp_apply]; apply congrArg; apply Fin.ext
      simp only [Fin.val_rev, Fin.val_succ]; omega
    have hc1 : W (t + 1) = M ((Fin.rev (⟨t, ht⟩ : Fin L)).castSucc) := by
      rw [hW (t + 1) ht]; simp only [Function.comp_apply]; apply congrArg; apply Fin.ext
      simp only [Fin.val_rev, Fin.val_castSucc]; omega
    have hval : Matrix.reindex (finCongr hr1) (finCongr hc1) (a t)
        = (A (Fin.rev (⟨t, ht⟩ : Fin L)))ᵀ := by
      rw [hadef]; simp only [dif_pos ht, revParams]
      simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
      congr 1 <;> · ext x; simp [finCongr]
    exact shift_layer M A (a t) (Fin.rev (⟨t, ht⟩ : Fin L)) (⟨L - (t + 1), by omega⟩ : Fin L)
      (by apply Fin.ext; simp only [Fin.val_rev, Fin.val_mk])
      hr1 hc1 hval (hrow t ht) (hcol t ht)
  have hfirst : W 0 = M ⟨L, Nat.lt_succ_self L⟩ := by
    rw [hW 0 (Nat.zero_le L)]; simp only [Function.comp_apply]; apply congrArg; apply Fin.ext
    simp only [Fin.val_rev, Fin.val_mk]; omega
  have hlast : W L = M 0 := by
    rw [hW L (le_refl L)]; simp only [Function.comp_apply]; apply congrArg; apply Fin.ext
    simp only [Fin.val_rev, Fin.val_zero]; omega
  have hinv := rawProd_rev_prefix_eq_transpose M A L (Nat.lt_succ_self L) W a hfirst hlast
    hrow hcol hlayer
  rw [← hbridge]
  rw [show ((prod M A)ᵀ)
        = Matrix.reindex (finCongr hfirst) (finCongr hlast) (rawProd W a L) from hinv.symm]
  simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
  congr 1 <;> · ext x; simp [finCongr]

/-- **The layer-product box integral is reversal-invariant** —
`routeMLayerBoxIntegral M c' 1 = routeMLayerBoxIntegral (M ∘ Fin.rev) c' 1`. The measure-preserving
reverse-transpose bijection `Φ : Params M ≃ᵐ Params (M ∘ Fin.rev)`, `Φ A s = (A (Fin.rev s))ᵀ`, sends
`paramsBoxM M 1` to `paramsBoxM (M ∘ Fin.rev) 1` (entry bound preserved under transpose + reindex) and
satisfies `prod (M ∘ Fin.rev) (Φ A) = (prod M A)ᵀ`, so `frobSq (prod (M ∘ Fin.rev) (Φ A)) =
frobSq (prod M A)`. -/
theorem routeMLayerBoxIntegral_comp_rev (M : Fin (L + 1) → ℕ) (c' : ℝ) :
    routeMLayerBoxIntegral M c' 1 = routeMLayerBoxIntegral (M ∘ Fin.rev) c' 1 := by
  -- ISOLATED CORRECT-STATEMENT SORRY (the O2 brick; statement is cast-free — the casts live inside
  -- the proof, matching CLAUDE.md's `prodAux`-reassoc "two-tides" cast territory). PROOF PLAN:
  --   1. `revParams : Params M → Params (M ∘ Fin.rev)`, `revParams A s = reindex (finCongr h_r)
  --      (finCongr h_c) (A (Fin.rev s))ᵀ`, with `h_r : M (Fin.rev s).succ = M (Fin.rev s.castSucc)`,
  --      `h_c : M (Fin.rev s).castSucc = M (Fin.rev s.succ)` (`congrArg M ∘ Fin.ext`, `Fin.val_rev`).
  --   2. `prod_revParams : prod (M ∘ Fin.rev) (revParams A) = reindex (finCongr _) (finCongr _)
  --      ((prod M A)ᵀ)` — `prodAux` induction reusing `prodAux_succ` + `Matrix.transpose_mul`; the
  --      running-width reindex casts are the labour (cf. `RouteMFrontPeel.mul_three_reassoc`,
  --      `reindex_finCongr_mul`; do cast bookkeeping at the equiv level, never entrywise).
  --   3. `frobSq (prod (M ∘ Fin.rev) (revParams A)) = frobSq (prod M A)` (frobSq is transpose- and
  --      reindex-invariant: `∑∑ (Xᵀ)² = ∑∑ X²`, `Finset.sum_comm`).
  --   4. `revParams` is a MeasurableEquiv, MeasurePreserving (transpose + layer-reindex = a coordinate
  --      permutation of the flat `Params` pi-Lebesgue; route via `paramsEquivFlat` MP + a
  --      `MeasurableEquiv.piCongrLeft`/`volume_preserving_piCongrLeft` permutation, OR directly as a
  --      `Matrix.transposeMeasurableEquiv`-style pi-swap per layer + `MeasurableEquiv.piCongrLeft` on
  --      `Fin.revPerm`), and `revParams '' (paramsBoxM M 1) = paramsBoxM (M ∘ Fin.rev) 1` (entry bound
  --      preserved under transpose + reindex).
  --   5. Assemble via `MeasurePreserving.setLIntegral_comp_preimage_emb` (as in
  --      `RouteMBoxReduction.routeMCore_le_matBox` step 2) + `setLIntegral_congr_fun` with (3).
  -- Self-contained, network-free, ideal for a focused tide. NOT laundered — statement correct, connector
  -- + wrapper + rev-good all proven around it.
  sorry

/-- **`RouteMBoxThresholdFinite` transfers across chain reversal.** If the reversed chain `M ∘ Fin.rev`
has finite box integral below its threshold, so does `M`: the thresholds coincide
(`minAdm (M ∘ Fin.rev) = minAdm M`, `minAdm_comp_perm` at `Fin.revPerm`) and the box integrals are equal
(`routeMLayerBoxIntegral_comp_rev`). -/
theorem routeMBoxThresholdFinite_of_rev (M : Fin (L + 1) → ℕ)
    (h : RouteMBoxThresholdFinite (M ∘ Fin.rev)) : RouteMBoxThresholdFinite M := by
  intro c' hc'
  have hperm : minAdm (M ∘ Fin.rev) = minAdm M := by
    have : (M ∘ Fin.rev) = (M ∘ (Fin.revPerm : Equiv.Perm (Fin (L + 1)))) := rfl
    rw [this]; exact minAdm_comp_perm (Fin.revPerm) M
  have hc'rev : (c' : ℝ) < (minAdm (M ∘ Fin.rev) : ℝ) / 2 := by rw [hperm]; exact hc'
  rw [routeMLayerBoxIntegral_comp_rev M (c' : ℝ)]
  exact h c' hc'rev

end DLNFibre.DLN.RLCT
