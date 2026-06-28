import DLNFibre.DLN.RLCT.Validate.FrontPivotWLOG

/-!
# `DLNFibre.DLN.RLCT.Validate.FrontPivotRowWLOG` — the ROW-permutation WLOG transfer

The row dual of `FrontPivotWLOG`'s column-permutation transfer. A **row** permutation `R` of the
target `B` (permuting the `H 0` OUTPUT coordinates) leaves the headline learning-coefficient infimum
invariant. This is the second WLOG (KC1) needed to front-align the deepest point's boundary layers:
the column-perm (`FrontPivotWLOG`) makes the LAST layer's front-`r` columns a pivot set; the
row-perm here makes the FIRST layer's leading `r×r` block invertible (`Im(B)` projects
isomorphically onto the first `r` ambient output coordinates).

Structurally the mirror of `FrontPivotWLOG`, with one simplification **and** one asymmetry:
- SIMPLER: the first layer's `(⟨0,_⟩ : Fin L).castSucc` width is `H 0` SYNTACTICALLY (defeq), so the
  row permutation `R : Equiv.Perm (Fin (H 0))` types directly as the row-submatrix index — no
  `finCongr` conjugation (the column proof needed it for the last layer's `.succ` width).
- HEAVIER: the column perm rode the LAST layer (the top peel of the left-folding `prodAux`, prefix
  untouched); the row perm rides the FIRST layer (the base of the fold), so EVERY positive prefix
  carries it. The product identity is the shifted positive-prefix invariant
  `prodAux (τ_R A) (k+1) = (prodAux A (k+1)).submatrix R id` (base `k = 0` = `prodAux 1`, where the
  first layer is read; step by `Matrix.submatrix_mul_equiv` pulling the left
  row-submatrix through the product).

The four lemmas mirror lemmas 2–4 of `FrontPivotWLOG`:
1. `prod_paramRowFirst` — `prod (τ_R A) = (prod A).submatrix R id`.
2. `dlnLoss_rowPerm_eq` — `dlnLoss H B A = dlnLoss H (B.submatrix R id) (τ_R A)`.
3. `paramRowFirst_measurePreserving` — `τ_R` is measure-preserving.
4. `rlct_infimum_rowPerm_eq` — the `⨅`-over-`optimalSet` RLCT transfer.
-/

open Matrix MeasureTheory Topology
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The `prodAux` recursion-step with the dependent-`Fin` cast discharged by HEq (local copy of
`FrontPivotWLOG`'s private helper): if `A ⟨k,_⟩` is HEq to `Mstep`, then
`prodAux (k+1) = prodAux k * Mstep`. -/
private theorem prodAux_step (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    (Mstep : Matrix (Fin (H ⟨k, Nat.lt_of_succ_lt hk⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)
    (hheq : HEq (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩) Mstep) :
    prodAux H A (k + 1) hk = prodAux H A k (Nat.lt_of_succ_lt hk) * Mstep := by
  rw [prodAux]; congr 1; rw [eq_comm]; apply eq_of_heq
  exact hheq.symm.trans (heq_of_eqRec_eq rfl rfl)

/-- The first layer index `⟨0, _⟩ : Fin L` (`0 < L` from `1 ≤ L`). Its `.castSucc` has `H`-width
`H 0` syntactically (defeq), so a permutation of `Fin (H 0)` indexes its rows directly. -/
def firstLayerIdx (hL : 1 ≤ L) : Fin L := ⟨0, by omega⟩

/-- `τ_R` : left-multiply the first layer's input rows by the permutation `R` (a row permutation of
the first-layer matrix), leaving every other layer fixed. `R : Equiv.Perm (Fin (H 0))` types
directly as the row index (the first layer's `.castSucc` width is `H 0` defeq) — no conjugation. -/
noncomputable def paramRowFirst (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (R : Equiv.Perm (Fin (H 0))) (A : Params H) : Params H :=
  Function.update A (firstLayerIdx hL)
    ((A (firstLayerIdx hL)).submatrix (R : Fin (H 0) → Fin (H 0)) id)

/-! ## Lemma 1 — `prod_paramRowFirst` (the product picks up the row permutation on the left) -/

/-- The positive-prefix invariant: `prodAux (τ_R A) (k+1) = (prodAux A (k+1)).submatrix R id`. The
first layer (read at the `0 → 1` step) carries the row permutation; it then rides through every
prefix by `submatrix_mul_equiv` (left row-submatrix pulls out of the product). -/
private theorem prodAux_paramRowFirst (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (R : Equiv.Perm (Fin (H 0))) (A : Params H) :
    ∀ (k : ℕ) (hk : k + 1 < L + 1),
      prodAux H (paramRowFirst H hL R A) (k + 1) hk
        = (prodAux H A (k + 1) hk).submatrix (R : Fin (H 0) → Fin (H 0))
            (id : Fin (H ⟨k + 1, hk⟩) → Fin (H ⟨k + 1, hk⟩)) := by
  set A' := paramRowFirst H hL R A with hA'
  intro k
  induction k with
  | zero =>
    intro hk
    -- `firstLayerIdx hL = ⟨0, _⟩ : Fin L` DEFEQ the induction's layer-0 index, so use it directly
    -- (no `⟨0,hkL⟩ ↔ firstLayerIdx` rewrite — `Function.update_self` fires on the nose).
    have hkL : ((firstLayerIdx hL : Fin L) : ℕ) = 0 := by simp [firstLayerIdx]
    have e1 : (⟨0, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1)) = (firstLayerIdx hL).castSucc := by
      apply Fin.ext; simp only [Fin.castSucc, Fin.castAdd, Fin.castLE, firstLayerIdx]
    have e2 : (⟨0 + 1, hk⟩ : Fin (L + 1)) = (firstLayerIdx hL).succ := by
      apply Fin.ext; simp only [Fin.succ, firstLayerIdx]
    -- The clean step matrix for `A` at the first layer (HEq to `A (firstLayerIdx hL)`).
    let Mstep : Matrix (Fin (H ⟨0, Nat.lt_of_succ_lt hk⟩)) (Fin (H ⟨0 + 1, hk⟩)) ℝ := by
      rw [e1, e2]; exact A (firstLayerIdx hL)
    have hM : HEq (A (firstLayerIdx hL)) Mstep := by
      dsimp only [Mstep]; exact heq_of_eqRec_eq rfl rfl
    -- `A'`'s first-layer step matrix, built the SAME way (HEq to `A' (firstLayerIdx hL)`).
    let Mstep' : Matrix (Fin (H ⟨0, Nat.lt_of_succ_lt hk⟩)) (Fin (H ⟨0 + 1, hk⟩)) ℝ := by
      rw [e1, e2]; exact A' (firstLayerIdx hL)
    have hM' : HEq (A' (firstLayerIdx hL)) Mstep' := by
      dsimp only [Mstep']; exact heq_of_eqRec_eq rfl rfl
    -- `A' (first) = (A (first)).submatrix R id` (`Function.update_self`) ⟹ the `Mstep' =` form.
    have hupd : A' (firstLayerIdx hL)
        = (A (firstLayerIdx hL)).submatrix (R : Fin (H 0) → Fin (H 0)) id := by
      rw [hA']
      exact Function.update_self (firstLayerIdx hL)
        ((A (firstLayerIdx hL)).submatrix (R : Fin (H 0) → Fin (H 0)) id) A
    have hstep_rel : Mstep' = Mstep.submatrix (R : Fin (H 0) → Fin (H 0)) id := by
      have hM'' : HEq (A' (firstLayerIdx hL)) (Mstep.submatrix (R : Fin (H 0) → Fin (H 0)) id) := by
        rw [hupd]
        clear hupd hM' hA'
        cases e1; cases e2
        cases (eq_of_heq hM)
        rfl
      exact eq_of_heq (hM'.symm.trans hM'')
    -- `prodAux_step` reads layer `⟨0, _⟩`; `A ⟨0,_⟩` and `A (firstLayerIdx)` are defeq.
    have hMfst : HEq (A ⟨0, Nat.lt_of_succ_lt_succ hk⟩) Mstep := hM
    have hMfst' : HEq (A' ⟨0, Nat.lt_of_succ_lt_succ hk⟩) Mstep' := hM'
    rw [prodAux_step H A' 0 hk Mstep' hMfst', prodAux_step H A 0 hk Mstep hMfst, hstep_rel]
    -- `prodAux _ 0 = 1` (def); the goal is `1 * X = (1 * X).submatrix R id`. `Matrix.one_mul` won't
    -- fire by `rw`/`simp` at the opaque dependent width (CLAUDE.md note (i)) — close with
    -- terms: LHS `1 * (Mstep.submatrix R id) = Mstep.submatrix R id`, RHS `(1 * Mstep) = Mstep`.
    exact (Matrix.one_mul (Mstep.submatrix (R : Fin (H 0) → Fin (H 0)) id)).trans
      (congrArg (·.submatrix (R : Fin (H 0) → Fin (H 0)) id) (Matrix.one_mul Mstep)).symm
  | succ n ih =>
    intro hk
    have hk' : n + 1 < L + 1 := Nat.lt_of_succ_lt hk
    have hkL : n + 1 < L := Nat.lt_of_succ_lt_succ hk
    have hne : (⟨n + 1, hkL⟩ : Fin L) ≠ firstLayerIdx hL := by
      intro h; have := congrArg Fin.val h; simp [firstLayerIdx] at this
    let Mstep : Matrix (Fin (H ⟨n + 1, hk'⟩)) (Fin (H ⟨n + 1 + 1, hk⟩)) ℝ := by
      have e1 : (⟨n + 1, hk'⟩ : Fin (L + 1)) = (⟨n + 1, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨n + 1 + 1, hk⟩ : Fin (L + 1)) = (⟨n + 1, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      rw [e1, e2]; exact A ⟨n + 1, hkL⟩
    have hM : HEq (A ⟨n + 1, hkL⟩) Mstep := by dsimp only [Mstep]; exact heq_of_eqRec_eq rfl rfl
    have hMu : HEq (A' ⟨n + 1, hkL⟩) Mstep := by
      rw [hA', paramRowFirst, Function.update_of_ne hne]; exact hM
    rw [prodAux_step H A' (n + 1) hk Mstep hMu, prodAux_step H A (n + 1) hk Mstep hM, ih hk']
    rw [← Matrix.submatrix_mul_equiv (prodAux H A (n + 1) hk') Mstep (R : Fin (H 0) → Fin (H 0))
        (Equiv.refl (Fin (H ⟨n + 1, hk'⟩)))
          (id : Fin (H ⟨n + 1 + 1, hk⟩) → Fin (H ⟨n + 1 + 1, hk⟩))]
    simp

/-- **The product picks up the row permutation on the left.** `prod (τ_R A) = (prod A).submatrix R
id`: `τ_R` permutes only the first layer's rows, the left factor of the leading multiplication,
permutation rides through to the product's rows. -/
theorem prod_paramRowFirst (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (R : Equiv.Perm (Fin (H 0))) (A : Params H) :
    prod H (paramRowFirst H hL R A)
      = (prod H A).submatrix (R : Fin (H 0) → Fin (H 0)) id := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  exact prodAux_paramRowFirst H hL R A m (Nat.lt_succ_self _)

/-! ## Lemma 2 — `dlnLoss_rowPerm_eq` (the exact loss identity) -/

/-- **The exact loss identity.** `dlnLoss H B A = dlnLoss H (B.submatrix R id) (τ_R A)`: the
square-Frobenius loss against the row-permuted target reindexes exactly to the loss against `B`
(`prod (τ_R A) = (prod A).submatrix R id`, and summing the squared entries over the permuted ROW
index `R` reindexes the outer sum). A sum-reindex by the permutation, no orthogonal argument. -/
theorem dlnLoss_rowPerm_eq (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (R : Equiv.Perm (Fin (H 0))) (A : Params H) :
    dlnLoss H B A
      = dlnLoss H (B.submatrix (R : Fin (H 0) → Fin (H 0)) id) (paramRowFirst H hL R A) := by
  unfold dlnLoss
  rw [← Equiv.sum_comp R (fun i => ∑ j, ((prod H A - B) i j) ^ 2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [prod_paramRowFirst H hL R A]
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, id]

/-! ## Lemma 3 — `paramRowFirst_measurePreserving` (`τ_R` is MP) -/

/-- A coordinate permutation of the rows `M ↦ fun i => M (R i)` is measure-preserving (`piCongrLeft`
on the row factor, identity on each column). -/
private theorem mp_rowperm_layer {m k : ℕ} (R : Equiv.Perm (Fin m)) :
    MeasurePreserving
      (fun M : (Fin m) → (Fin k) → ℝ => (fun i => M (R i)))
      (volume : Measure ((Fin m) → (Fin k) → ℝ))
      (volume : Measure ((Fin m) → (Fin k) → ℝ)) := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : Fin m => (Fin k) → ℝ) R).symm
  have heq : (fun M : (Fin m) → (Fin k) → ℝ => (fun i => M (R i)))
      = ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin m => (Fin k) → ℝ) R).symm := by
    funext M a
    change M (R a) = (MeasurableEquiv.piCongrLeft (fun _ : Fin m => (Fin k) → ℝ) R).symm M a
    rw [show ((MeasurableEquiv.piCongrLeft (fun _ : Fin m => (Fin k) → ℝ) R).symm M a)
        = (Equiv.piCongrLeft (fun _ : Fin m => (Fin k) → ℝ) R).symm M a from rfl,
      Equiv.piCongrLeft_symm_apply]
  rw [heq]; exact h

/-- `τ_R` is continuous (`Function.update` of the identity by a continuous row-permutation). -/
private theorem continuous_paramRowFirst (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (R : Equiv.Perm (Fin (H 0))) : Continuous (paramRowFirst H hL R) := by
  unfold paramRowFirst
  exact Continuous.update continuous_id _
    (Continuous.matrix_submatrix ((continuous_apply (firstLayerIdx hL))) _ _)

/-- **`τ_R` is measure-preserving.** `τ_R` permutes the first layer's row-indexed entries — a
coordinate permutation of `Params H`. Built from `volume_preserving_pi` (componentwise: identity off
the first layer; a row permutation = a `piCongrLeft` reindex of the first layer's rows). -/
theorem paramRowFirst_measurePreserving (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (R : Equiv.Perm (Fin (H 0))) :
    MeasurePreserving (paramRowFirst H hL R)
      (volume : Measure (Params H)) (volume : Measure (Params H)) := by
  let flayer : (s : Fin L) → ((Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ)
      → ((Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ) :=
    Function.update (fun _ M => M) (firstLayerIdx hL)
      (fun M => (fun i => M ((R : Fin (H 0) → Fin (H 0)) i)))
  have hfun : (paramRowFirst H hL R) = fun (A : Params H) (s : Fin L) => flayer s (A s) := by
    funext A s
    simp only [paramRowFirst, flayer]
    by_cases h : s = firstLayerIdx hL
    · subst h; rw [Function.update_self, Function.update_self]
      funext i j; rfl
    · rw [Function.update_of_ne h, Function.update_of_ne h]
  rw [hfun]
  refine volume_preserving_pi (β' := fun s : Fin L => (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ)
    (f := fun s => flayer s) ?_
  intro s
  by_cases h : s = firstLayerIdx hL
  · subst h
    change MeasurePreserving (flayer (firstLayerIdx hL)) _ _
    simp only [flayer, Function.update_self]
    exact mp_rowperm_layer (R : Equiv.Perm (Fin (H ((firstLayerIdx hL).castSucc))))
  · change MeasurePreserving (flayer s) _ _
    simp only [flayer, Function.update_of_ne h]
    exact MeasurePreserving.id _

/-! ## Lemma 4 — `rlct_infimum_rowPerm_eq` (the `⨅`-transfer) -/

/-- `τ_R` undoes by `τ_{R⁻¹}` (row-perm by `R` then `R⁻¹` is the identity on the first layer). -/
private theorem paramRowFirst_inv (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (R : Equiv.Perm (Fin (H 0))) (A : Params H) :
    paramRowFirst H hL R⁻¹ (paramRowFirst H hL R A) = A := by
  unfold paramRowFirst
  rw [Function.update_self]
  funext s
  by_cases h : s = firstLayerIdx hL
  · subst h
    rw [Function.update_self, Matrix.submatrix_submatrix]
    have hid : ∀ x : Fin (H 0),
        (R : Fin (H 0) → Fin (H 0)) ((R⁻¹ : Equiv.Perm (Fin (H 0))) x) = x :=
      fun x => by simp
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.submatrix_apply, Function.comp_apply, hid, id_eq]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

/-- **The `⨅`-over-`optimalSet` RLCT is invariant under a row permutation of `B`.** `τ_R` is
MP homeomorphism (lemma 3) mapping `optimalSet H B` bijectively to `optimalSet H (B.submatrix R id)`
(by the loss identity, lemma 2), and preserving each point's local `rlctAt` (banked
`rlctAtOn_comp_homeomorph`). So the infimum is preserved — the row dual of the colPerm lemma. -/
theorem rlct_infimum_rowPerm_eq (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (R : Equiv.Perm (Fin (H 0))) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w)
      = ⨅ w ∈ optimalSet H (B.submatrix (R : Fin (H 0) → Fin (H 0)) id),
          rlctAt H (dlnLoss H (B.submatrix (R : Fin (H 0) → Fin (H 0)) id)) w := by
  set Bp := B.submatrix (R : Fin (H 0) → Fin (H 0))
    (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))
    with hBp
  let τ : Params H ≃ₜ Params H :=
    { toFun := paramRowFirst H hL R
      invFun := paramRowFirst H hL R⁻¹
      left_inv := fun A => paramRowFirst_inv H hL R A
      right_inv := fun A => by
        have := paramRowFirst_inv H hL R⁻¹ A; simpa [inv_inv] using this
      continuous_toFun := continuous_paramRowFirst H hL R
      continuous_invFun := continuous_paramRowFirst H hL R⁻¹ }
  have hmp : MeasurePreserving τ (volume : Measure (Params H)) volume :=
    paramRowFirst_measurePreserving H hL R
  haveI : BorelSpace (Params H) :=
    inferInstanceAs (BorelSpace (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))
  have hemb : MeasurableEmbedding τ := τ.measurableEmbedding
  have hpoint : ∀ w : Params H,
      rlctAt H (dlnLoss H Bp) (τ w) = rlctAt H (dlnLoss H B) w := by
    intro w
    have htrans := rlctAtOn_comp_homeomorph τ hmp hemb (dlnLoss H Bp) w
    have hcomp : (fun w => dlnLoss H Bp (τ w)) = dlnLoss H B := by
      funext A
      change dlnLoss H Bp (paramRowFirst H hL R A) = dlnLoss H B A
      rw [hBp, ← dlnLoss_rowPerm_eq H hL B R A]
    rw [hcomp, rlctAtOn_eq_rlctAt, rlctAtOn_eq_rlctAt] at htrans
    exact htrans.symm
  have hmaps : ∀ A, prod H A = B → prod H (τ A) = Bp := by
    intro A hA
    change prod H (paramRowFirst H hL R A) = Bp
    rw [prod_paramRowFirst H hL R A, hA, hBp]
  have hbij : Set.BijOn τ (optimalSet H B) (optimalSet H Bp) := by
    refine ⟨fun A hA => hmaps A hA, τ.injective.injOn, fun A' hA' => ?_⟩
    refine ⟨τ.symm A', ?_, τ.apply_symm_apply A'⟩
    change prod H (τ.symm A') = B
    have h1 : (prod H (τ.symm A')).submatrix (R : Fin (H 0) → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L))) = prod H A' := by
      have := prod_paramRowFirst H hL R (τ.symm A')
      rw [show paramRowFirst H hL R (τ.symm A') = τ (τ.symm A') from rfl,
        τ.apply_symm_apply] at this
      exact this.symm
    have hA'eq : prod H A' = Bp := hA'
    rw [hA'eq, hBp] at h1
    funext i j
    have := congrFun (congrFun h1 (R.symm i)) j
    simpa [Matrix.submatrix_apply] using this
  exact Set.BijOn.iInf_congr (rlctAt H (dlnLoss H B)) (rlctAt H (dlnLoss H Bp)) hbij hpoint

end DLNFibre.DLN.RLCT
