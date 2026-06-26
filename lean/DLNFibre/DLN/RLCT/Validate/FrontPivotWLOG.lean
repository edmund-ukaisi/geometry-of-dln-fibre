import DLNFibre.DLN.RLCT.Foundations.LossContinuity
import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import DLNFibre.Core.Matrix.RankNormalForm
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Logic.Equiv.Fintype

/-!
# `DLNFibre.DLN.RLCT.Validate.FrontPivotWLOG` — the column-permutation WLOG transfer

The headline-level `rlctAt`-invariance under a column permutation of the target `B`, used to
discharge the gauge chart's front-pivot hypothesis `hJfront`. INDEPENDENT of the gauge chart /
producer / `hfin`: purely `dlnLoss` + the column permutation + the banked `rlctAtOn`-MP-invariance.

The transfer rests on the EXACT reindexing identity (no orthogonal-Frobenius argument needed): if
`τ_P` right-multiplies the last layer's columns by `P` (`paramColPermLast`), then
`prod (τ_P A) = (prod A).submatrix id P` (the column permutation rides on the right of the last
matrix factor), so the square-Frobenius loss against the column-permuted target `B.submatrix id P`
reindexes exactly to the loss against `B`. `τ_P` is a coordinate permutation of `Params H`
(measure-preserving), so it is a global MP homeomorphism; the four lemmas (b-wlog-spec.md 1–4) are:

1. `front_pivot_perm_exists` — a column permutation `P` bringing `B`'s rank-`r` pivot columns to the
   front `{0..r-1}` (so the first `r` columns of `B.submatrix id P` are linearly independent).
2. `dlnLoss_colPerm_eq` — the exact loss identity
   `dlnLoss H B A = dlnLoss H (B.submatrix id P) (τ_P A)`.
3. `paramColPermLast_measurePreserving` — `τ_P` is measure-preserving.
4. `rlct_infimum_colPerm_eq` — the `⨅`-over-`optimalSet` RLCT transfer (the banked
   `rlctAtOn_comp_homeomorph` + an `iInf`-over-bijection congruence).

The headline `rw` (lemma 5) and the squeeze relocation are NOT here — they are the
controller-coordinated final wire. (The permutation binder is named `P`, not capital-Pi, to dodge
the `lean/CLAUDE.md` lexer-reject on confusable Greek capitals.)
-/

open Matrix MeasureTheory Topology
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Last-layer indexing (self-contained) -/

/-- The last layer index `⟨L-1, _⟩ : Fin L` (`0 < L` from `1 ≤ L`); its `.succ` is `Fin.last L`. -/
def lastLayerIdx (hL : 1 ≤ L) : Fin L := ⟨L - 1, by omega⟩

/-- `(lastLayerIdx hL).succ` has the same `H`-width as `Fin.last L` (the last layer's columns). -/
theorem H_lastLayerIdx_succ (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    H ((lastLayerIdx hL).succ) = H (Fin.last L) := by
  congr 1; apply Fin.ext; simp [lastLayerIdx, Fin.succ, Fin.last]; omega

/-! ## The parameter column-permutation `τ_P` -/

/-- `τ_P` : right-multiply the last layer's output columns by the permutation `P` (a column
permutation of the last-layer matrix), leaving every other layer fixed. The column index `P` lives
on `Fin (H (Fin.last L))` (the type `prod H A`'s columns live in); it is transported into the last
layer's `.succ` width by the `finCongr` of `H_lastLayerIdx_succ`. -/
noncomputable def paramColPermLast (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (P : Equiv.Perm (Fin (H (Fin.last L)))) (A : Params H) : Params H :=
  Function.update A (lastLayerIdx hL)
    ((A (lastLayerIdx hL)).submatrix id
      (((finCongr (H_lastLayerIdx_succ H hL)).trans
        (P.trans (finCongr (H_lastLayerIdx_succ H hL)).symm)) : Fin _ → Fin _))

/-! ## Lemma 1 — `front_pivot_perm_exists` (routine linear algebra) -/

/-- **Front-pivot column permutation.** For a rank-`r` matrix `B`, there is a column permutation `P`
bringing `r` linearly-independent columns to the FRONT `{0..r-1}`: `B.submatrix id P` keeps rank `r`
(`P` invertible) and its first `r` columns (the submatrix at the front embedding `Fin.castLE`) have
rank `r`. This is the `hJfront` (front-pivot) datum the WLOG transfer supplies the gauge chart. -/
theorem front_pivot_perm_exists {H0 n : ℕ} (B : Matrix (Fin H0) (Fin n) ℝ) {r : ℕ}
    (hB : B.rank = r) :
    ∃ (P : Equiv.Perm (Fin n)) (hrn : r ≤ n),
      (B.submatrix id (P : Fin n → Fin n)).rank = r ∧
      ((B.submatrix id (P : Fin n → Fin n)).submatrix id
        (Fin.castLE hrn : Fin r → Fin n)).rank = r := by
  classical
  -- (i) Select `r` linearly-independent columns of `B` (maximal independent subfamily of `B.col`).
  obtain ⟨J, hJ⟩ : ∃ J : Fin r ↪ Fin n,
      (B.submatrix (id : Fin H0 → Fin H0) (J : Fin r → Fin n)).rank = r := by
    obtain ⟨κ, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' ℝ B.col
    haveI : Finite κ := ha_li.finite
    haveI : Fintype κ := Fintype.ofFinite κ
    have hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range B.col)) = r := by
      rw [← Matrix.rank_eq_finrank_span_cols B, hB]
    have hcard : Fintype.card κ = r := by
      have hfin : Module.finrank ℝ (Submodule.span ℝ (Set.range (B.col ∘ a))) = Fintype.card κ :=
        finrank_span_eq_card ha_li
      rw [ha_span] at hfin
      exact hfin.symm.trans hrank
    let e : κ ≃ Fin r := Fintype.equivFinOfCardEq hcard
    let J : Fin r ↪ Fin n :=
      ⟨fun i => a (e.symm i), fun i j hij => e.symm.injective (ha_inj hij)⟩
    refine ⟨J, ?_⟩
    have hJli : LinearIndependent ℝ (fun i : Fin r => B.col (J i)) := by
      have := ha_li.comp (e.symm : Fin r → κ) e.symm.injective
      simpa [J, Function.comp_def] using this
    rw [Matrix.rank_eq_finrank_span_cols]
    have hsubcol : (B.submatrix (id : Fin H0 → Fin H0) (J : Fin r → Fin n)).col
        = fun i => B.col (J i) := by funext k i; rfl
    rw [hsubcol, finrank_span_eq_card hJli]; simp
  -- (ii) `r ≤ n` (an embedding `Fin r ↪ Fin n`); extend `J` to a permutation fronting its range.
  have hrn : r ≤ n := by simpa using Fintype.card_le_of_embedding J
  let pf : Fin n → Prop := fun x => (x : ℕ) < r
  let qf : Fin n → Prop := fun x => x ∈ Set.range J
  let eFront : Fin r ≃ {x : Fin n // pf x} :=
    { toFun := fun i => ⟨Fin.castLE hrn i, by simp [pf]⟩
      invFun := fun x => ⟨(x : Fin n), by have := x.2; simpa [pf] using this⟩
      left_inv := by intro i; apply Fin.ext; simp [Fin.castLE]
      right_inv := by intro x; apply Subtype.ext; rfl }
  let eJ : Fin r ≃ {x : Fin n // qf x} := J.toEquivRange
  let e : {x : Fin n // pf x} ≃ {x : Fin n // qf x} := eFront.symm.trans eJ
  -- The extended permutation maps the front `{0..r-1}` bijectively onto `range J`, exactly to `J`.
  have hfront : ∀ i : Fin r, e.extendSubtype (Fin.castLE hrn i) = J i := by
    intro i
    have hmem : pf (Fin.castLE hrn i) := by simp [pf]
    rw [Equiv.extendSubtype_apply_of_mem e _ hmem]
    change (e ⟨Fin.castLE hrn i, hmem⟩ : Fin n) = J i
    dsimp only [e, Equiv.trans_apply]
    have hef : eFront.symm ⟨Fin.castLE hrn i, hmem⟩ = i := by
      apply eFront.injective; rw [Equiv.apply_symm_apply]; apply Subtype.ext; apply Fin.ext; rfl
    rw [hef]
    change (J.toEquivRange i : Fin n) = J i
    exact congrArg Subtype.val (Function.Embedding.toEquivRange_apply J i)
  refine ⟨e.extendSubtype, hrn, ?_, ?_⟩
  · -- `B.submatrix id P` has the same rank as `B` (`P` an equiv-reindex of the columns).
    have h := Matrix.rank_submatrix B (Equiv.refl (Fin H0)) e.extendSubtype
    rw [hB] at h; simpa using h
  · -- The first `r` columns of `B.submatrix id P` are `B`'s pivots (`submatrix ∘ submatrix`).
    have hcomp : (B.submatrix (id : Fin H0 → Fin H0) (e.extendSubtype : Fin n → Fin n)).submatrix
        (id : Fin H0 → Fin H0) (Fin.castLE hrn : Fin r → Fin n)
        = B.submatrix (id : Fin H0 → Fin H0) (J : Fin r → Fin n) := by
      rw [Matrix.submatrix_submatrix]
      congr 1
      funext i; simp only [Function.comp_apply]; exact hfront i
    rw [hcomp]; exact hJ

/-! ## Lemma 2 — `dlnLoss_colPerm_eq` (the exact loss identity) -/

/-- The `prodAux` recursion-step with the dependent-`Fin` cast discharged by HEq (local copy of the
`Skeleton`/`LossHomogeneity` private helper): if `A ⟨k,_⟩` is HEq to `Mstep`, then
`prodAux (k+1) = prodAux k * Mstep`. -/
private theorem prodAux_step (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    (Mstep : Matrix (Fin (H ⟨k, Nat.lt_of_succ_lt hk⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)
    (hheq : HEq (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩) Mstep) :
    prodAux H A (k + 1) hk = prodAux H A k (Nat.lt_of_succ_lt hk) * Mstep := by
  rw [prodAux]; congr 1; rw [eq_comm]; apply eq_of_heq
  exact hheq.symm.trans (heq_of_eqRec_eq rfl rfl)

/-- **The prefix product ignores an updated layer past it.** `prodAux (update A s v) k = prodAux A
k` whenever `k ≤ s` — the prefix `A⁽¹⁾⋯A⁽ᵏ⁾` reads only layers `< k ≤ s`, none of them `s`. -/
private theorem prodAux_update_eq_of_le (H : Fin (L + 1) → ℕ) (A : Params H) (s : Fin L)
    (v : Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ) :
    ∀ (k : ℕ) (hk : k < L + 1), k ≤ (s : ℕ) →
      prodAux H (Function.update A s v) k hk = prodAux H A k hk := by
  intro k
  induction k with
  | zero => intro hk _; simp only [prodAux]
  | succ k ih =>
      intro hk hks
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      -- Layer `⟨k, hkL⟩ ≠ s` since `k < k+1 ≤ s`.
      have hne : (⟨k, hkL⟩ : Fin L) ≠ s := fun h => by
        have : (s : ℕ) = k := by rw [← h]
        omega
      -- The clean transported step matrix for the UNUPDATED tuple, HEq to `A ⟨k,hkL⟩`.
      let Mstep : Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ := by
        have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
          apply Fin.ext; simp [Fin.castSucc]
        have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
          apply Fin.ext; simp [Fin.succ]
        rw [e1, e2]; exact A ⟨k, hkL⟩
      have hM : HEq (A ⟨k, hkL⟩) Mstep := by dsimp only [Mstep]; exact heq_of_eqRec_eq rfl rfl
      have hMu : HEq ((Function.update A s v) ⟨k, hkL⟩) Mstep := by
        rw [Function.update_of_ne hne]; exact hM
      rw [prodAux_step H (Function.update A s v) k hk Mstep hMu,
          prodAux_step H A k hk Mstep hM, ih hk' (by omega)]

/-- **The product picks up the column permutation on the right.** `prod (τ_P A) = (prod A).submatrix
id P`: `τ_P` permutes only the last layer's columns, which is the right factor of the final
multiplication, so the permutation rides through to the product's columns. -/
theorem prod_paramColPermLast (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (P : Equiv.Perm (Fin (H (Fin.last L)))) (A : Params H) :
    prod H (paramColPermLast H hL P A)
      = (prod H A).submatrix id (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L))) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  -- With `L = m+1`, `lastLayerIdx = ⟨m,_⟩` and `.succ = Fin.last (m+1)` are DEFEQ, so the
  -- `finCongr` cast in `paramColPermLast` collapses to the identity (on values).
  set A' := paramColPermLast H hL P A with hA'
  have hk : m + 1 < (m + 1) + 1 := Nat.lt_succ_self _
  have hkL : m < m + 1 := by omega
  have hk' : m < (m + 1) + 1 := by omega
  -- The conjugated permutation on the last-layer `.succ` width.
  set Q := (((finCongr (H_lastLayerIdx_succ H hL)).trans
        (P.trans (finCongr (H_lastLayerIdx_succ H hL)).symm))
        : Fin (H ((lastLayerIdx hL).succ)) → Fin (H ((lastLayerIdx hL).succ))) with hQ
  -- The transported step matrix for `A` (HEq to `A ⟨m,hkL⟩`; sidesteps the `prodAux` Eq.mpr cast).
  let Mstep : Matrix (Fin (H ⟨m, hk'⟩)) (Fin (H ⟨m + 1, hk⟩)) ℝ := by
    have e1 : (⟨m, hk'⟩ : Fin ((m + 1) + 1)) = (⟨m, hkL⟩ : Fin (m + 1)).castSucc := by
      apply Fin.ext; simp [Fin.castSucc]
    have e2 : (⟨m + 1, hk⟩ : Fin ((m + 1) + 1)) = (⟨m, hkL⟩ : Fin (m + 1)).succ := by
      apply Fin.ext; simp [Fin.succ]
    rw [e1, e2]; exact A ⟨m, hkL⟩
  have hM : HEq (A ⟨m, hkL⟩) Mstep := by dsimp only [Mstep]; exact heq_of_eqRec_eq rfl rfl
  have hstepA : prod H A = prodAux H A m hk' * Mstep := by
    rw [prod]; exact prodAux_step H A m hk Mstep hM
  -- `A'`'s step matrix is `Mstep` column-permuted by `P` (`Pfun` on the `⟨m+1,hk⟩` width).
  set Pfun : Fin (H ⟨m + 1, hk⟩) → Fin (H ⟨m + 1, hk⟩) := (P : Fin _ → Fin _) with hPfun
  let Mstep' : Matrix (Fin (H ⟨m, hk'⟩)) (Fin (H ⟨m + 1, hk⟩)) ℝ := Mstep.submatrix id Pfun
  have hM' : HEq (A' ⟨m, hkL⟩) Mstep' := by
    have hupd : A' (lastLayerIdx hL) = (A (lastLayerIdx hL)).submatrix id Q := by
      rw [hA', paramColPermLast, Function.update_self]
    have e : A' ⟨m, hkL⟩ = (A (lastLayerIdx hL)).submatrix id Q := hupd
    rw [e]
    apply HEq.trans (b := (A ⟨m, hkL⟩).submatrix id Pfun)
    · -- `Q` and `Pfun` have the same (defeq) type and are value-equal (the `finCongr` collapses).
      have hQP : Q
          = (Pfun : Fin (H ((lastLayerIdx hL).succ)) → Fin (H ((lastLayerIdx hL).succ))) := by
        funext x; apply Fin.ext
        simp only [hQ, hPfun, Equiv.trans_apply, finCongr_apply_coe, finCongr_symm]
        rfl
      rw [hQP]; rfl
    · dsimp only [Mstep']; congr 1
  -- assemble: both products = (common prefix) * (step matrix), with `Mstep' = Mstep.submatrix P`.
  have hstepA' : prod H A' = prodAux H A' m hk' * Mstep' := by
    rw [prod]; exact prodAux_step H A' m hk Mstep' hM'
  have hpre : prodAux H A' m hk' = prodAux H A m hk' := by
    rw [hA', paramColPermLast]
    exact prodAux_update_eq_of_le H A (lastLayerIdx hL) _ m hk' (by simp [lastLayerIdx])
  rw [hstepA', hstepA, hpre]
  change prodAux H A m hk' * Mstep.submatrix id Pfun
      = (prodAux H A m hk' * Mstep).submatrix id Pfun
  rw [← submatrix_mul_equiv (prodAux H A m hk') Mstep id (Equiv.refl _) Pfun]
  simp

/-- **The exact loss identity.** `dlnLoss H B A = dlnLoss H (B.submatrix id P) (τ_P A)`: the
square-Frobenius loss against the column-permuted target reindexes exactly to the loss against `B`
(`prod (τ_P A) = (prod A).submatrix id P`, and summing the squared entries over the permuted column
index `P` reindexes the sum). No orthogonal-matrix argument — a sum-reindex by the permutation. -/
theorem dlnLoss_colPerm_eq (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (P : Equiv.Perm (Fin (H (Fin.last L)))) (A : Params H) :
    dlnLoss H B A
      = dlnLoss H (B.submatrix id (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L))))
          (paramColPermLast H hL P A) := by
  unfold dlnLoss
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- The inner sum over the last-index reindexes by the permutation `P`.
  rw [← Equiv.sum_comp P (fun j => ((prod H A - B) i j) ^ 2)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [prod_paramColPermLast H hL P A]
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, id]

/-! ## Lemma 3 — `paramColPermLast_measurePreserving` (`τ_P` is MP) -/

/-- A coordinate permutation of one row `g ↦ g ∘ Q` is measure-preserving (`piCongrLeft`). -/
private theorem mp_compose_row {k : ℕ} (Q : Equiv.Perm (Fin k)) :
    MeasurePreserving (fun g : Fin k → ℝ => g ∘ (Q : Fin k → Fin k))
      (volume : Measure (Fin k → ℝ)) (volume : Measure (Fin k → ℝ)) := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : Fin k => ℝ) Q).symm
  have heq : (fun g : Fin k → ℝ => g ∘ (Q : Fin k → Fin k))
      = ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) Q).symm := by
    funext g a
    change g (Q a) = (MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) Q).symm g a
    rw [show ((MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) Q).symm g a)
        = (Equiv.piCongrLeft (fun _ : Fin k => ℝ) Q).symm g a from rfl,
      Equiv.piCongrLeft_symm_apply]
  rw [heq]; exact h

/-- A column permutation of a layer matrix `M ↦ (fun i => M i ∘ Q)` is measure-preserving
(`volume_preserving_pi` over rows, each row the compose-MP). -/
private theorem mp_colperm_layer {m k : ℕ} (Q : Equiv.Perm (Fin k)) :
    MeasurePreserving
      (fun M : (Fin m) → (Fin k) → ℝ => (fun i => (M i) ∘ (Q : Fin k → Fin k)))
      (volume : Measure ((Fin m) → (Fin k) → ℝ))
      (volume : Measure ((Fin m) → (Fin k) → ℝ)) :=
  volume_preserving_pi (fun _ : Fin m => mp_compose_row Q)

/-- **`τ_P` is measure-preserving.** `τ_P` permutes the last layer's column-indexed entries — a
coordinate permutation of `Params H`. Built from `volume_preserving_pi` (componentwise: identity off
the last layer; a column permutation = a `piCongrLeft` reindex of each row on the last layer). -/
theorem paramColPermLast_measurePreserving (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (P : Equiv.Perm (Fin (H (Fin.last L)))) :
    MeasurePreserving (paramColPermLast H hL P)
      (volume : Measure (Params H)) (volume : Measure (Params H)) := by
  set Q := (((finCongr (H_lastLayerIdx_succ H hL)).trans
        (P.trans (finCongr (H_lastLayerIdx_succ H hL)).symm))
        : Equiv.Perm (Fin (H ((lastLayerIdx hL).succ)))) with hQ
  -- The per-layer family of self-maps: identity off the last layer, the column permutation on it.
  let flayer : (s : Fin L) → ((Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ)
      → ((Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ) :=
    Function.update (fun _ M => M) (lastLayerIdx hL)
      (fun M => (fun i => (M i) ∘ (Q : Fin _ → Fin _)))
  have hfun : (paramColPermLast H hL P) = fun (A : Params H) (s : Fin L) => flayer s (A s) := by
    funext A s
    simp only [paramColPermLast, flayer]
    by_cases h : s = lastLayerIdx hL
    · subst h; rw [Function.update_self, Function.update_self]; rfl
    · rw [Function.update_of_ne h, Function.update_of_ne h]
  rw [hfun]
  refine volume_preserving_pi (β' := fun s : Fin L => (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ)
    (f := fun s => flayer s) ?_
  intro s
  by_cases h : s = lastLayerIdx hL
  · subst h
    change MeasurePreserving (flayer (lastLayerIdx hL)) _ _
    simp only [flayer, Function.update_self]
    exact mp_colperm_layer Q
  · change MeasurePreserving (flayer s) _ _
    simp only [flayer, Function.update_of_ne h]
    exact MeasurePreserving.id _

/-! ## Lemma 4 — `rlct_infimum_colPerm_eq` (the `⨅`-transfer) -/

/-- `τ_P` is continuous (`Function.update` of the identity by a continuous column-permutation). -/
private theorem continuous_paramColPermLast (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (P : Equiv.Perm (Fin (H (Fin.last L)))) : Continuous (paramColPermLast H hL P) := by
  unfold paramColPermLast
  exact Continuous.update continuous_id _
    (Continuous.matrix_submatrix ((continuous_apply (lastLayerIdx hL))) _ _)

/-- `τ_{P⁻¹}` undoes `τ_P` (column-perm by `P` then by `P⁻¹` is the identity on the last layer). -/
private theorem paramColPermLast_inv (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (P : Equiv.Perm (Fin (H (Fin.last L)))) (A : Params H) :
    paramColPermLast H hL P⁻¹ (paramColPermLast H hL P A) = A := by
  unfold paramColPermLast
  rw [Function.update_self]
  funext s
  by_cases h : s = lastLayerIdx hL
  · subst h
    rw [Function.update_self, Matrix.submatrix_submatrix]
    have hcols : (((finCongr (H_lastLayerIdx_succ H hL)).trans
              (P.trans (finCongr (H_lastLayerIdx_succ H hL)).symm)) : Fin _ → Fin _)
            ∘ (((finCongr (H_lastLayerIdx_succ H hL)).trans
              ((P⁻¹).trans (finCongr (H_lastLayerIdx_succ H hL)).symm)) : Fin _ → Fin _)
            = id := by
      funext x; apply Fin.ext; simp [Function.comp_apply]
    rw [hcols, Function.comp_id, Matrix.submatrix_id_id]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

/-- **The `⨅`-over-`optimalSet` RLCT is invariant under a column permutation of `B`.** `τ_P` is a
global MP homeomorphism (lemma 3) mapping `optimalSet H B` bijectively to `optimalSet H (B.submatrix
id P)` (by the loss identity, lemma 2), and preserving each point's local `rlctAt` (banked
`rlctAtOn_comp_homeomorph`). So the infimum is preserved — choice-independent, through the
headline's existing `⨅`-form. -/
theorem rlct_infimum_colPerm_eq (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (P : Equiv.Perm (Fin (H (Fin.last L)))) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w)
      = ⨅ w ∈ optimalSet H (B.submatrix id (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))),
          rlctAt H (dlnLoss H
            (B.submatrix id (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L))))) w := by
  set Bp := B.submatrix (id : Fin (H 0) → Fin (H 0))
    (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L))) with hBp
  -- `τ` : the column-permutation homeomorphism of `Params H`.
  let τ : Params H ≃ₜ Params H :=
    { toFun := paramColPermLast H hL P
      invFun := paramColPermLast H hL P⁻¹
      left_inv := fun A => paramColPermLast_inv H hL P A
      right_inv := fun A => by
        have := paramColPermLast_inv H hL P⁻¹ A; simpa [inv_inv] using this
      continuous_toFun := continuous_paramColPermLast H hL P
      continuous_invFun := continuous_paramColPermLast H hL P⁻¹ }
  have hmp : MeasurePreserving τ (volume : Measure (Params H)) volume :=
    paramColPermLast_measurePreserving H hL P
  haveI : BorelSpace (Params H) :=
    inferInstanceAs (BorelSpace (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))
  have hemb : MeasurableEmbedding τ := τ.measurableEmbedding
  -- Per-point: the local RLCT at `τ w` (against `Bp`) equals the local RLCT at `w` (against `B`).
  have hpoint : ∀ w : Params H,
      rlctAt H (dlnLoss H Bp) (τ w) = rlctAt H (dlnLoss H B) w := by
    intro w
    have htrans := rlctAtOn_comp_homeomorph τ hmp hemb (dlnLoss H Bp) w
    have hcomp : (fun w => dlnLoss H Bp (τ w)) = dlnLoss H B := by
      funext A
      change dlnLoss H Bp (paramColPermLast H hL P A) = dlnLoss H B A
      rw [hBp, ← dlnLoss_colPerm_eq H hL B P A]
    rw [hcomp, rlctAtOn_eq_rlctAt, rlctAtOn_eq_rlctAt] at htrans
    exact htrans.symm
  -- `τ` maps `optimalSet B` bijectively to `optimalSet Bp` (the loss-zero sets correspond).
  have hmaps : ∀ A, prod H A = B → prod H (τ A) = Bp := by
    intro A hA
    change prod H (paramColPermLast H hL P A) = Bp
    rw [prod_paramColPermLast H hL P A, hA, hBp]
  have hbij : Set.BijOn τ (optimalSet H B) (optimalSet H Bp) := by
    refine ⟨fun A hA => hmaps A hA, τ.injective.injOn, fun A' hA' => ?_⟩
    refine ⟨τ.symm A', ?_, τ.apply_symm_apply A'⟩
    change prod H (τ.symm A') = B
    have h1 : (prod H (τ.symm A')).submatrix (id : Fin (H 0) → Fin (H 0))
        (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L))) = prod H A' := by
      have := prod_paramColPermLast H hL P (τ.symm A')
      rw [show paramColPermLast H hL P (τ.symm A') = τ (τ.symm A') from rfl,
        τ.apply_symm_apply] at this
      exact this.symm
    have hA'eq : prod H A' = Bp := hA'
    rw [hA'eq, hBp] at h1
    funext i j
    have := congrFun (congrFun h1 i) (P.symm j)
    simpa [Matrix.submatrix_apply] using this
  exact Set.BijOn.iInf_congr (rlctAt H (dlnLoss H B)) (rlctAt H (dlnLoss H Bp)) hbij hpoint

end DLNFibre.DLN.RLCT
