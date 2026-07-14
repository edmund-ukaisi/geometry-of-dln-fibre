import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Lagrange

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJOrderedRootsMeasurable` — Brick F2a: `measurableEigenvalues₀`

The first analytic primitive of the measurable-eigendecomposition ladder (Brick F). For a
**measurable Hermitian** family `A : X → Matrix (Fin M₂) (Fin M₂) ℝ`, the **sorted**
eigenvalues `(A z).IsHermitian.eigenvalues₀` (decreasing) are a **measurable** function of `z`.

## Method — Vieta evaluations + Lusin–Souslin (contour-free, no root-continuity)

The sorted eigenvalues are in fact continuous in the matrix (Weyl's inequality), but Mathlib
v4.29 ships no such lemma; measurability is recovered without it, by **inverting a measurable
embedding**:

* `evalMap r j = (∏ i, (X - C (r i))).eval (node j)`, the monic `∏ (X - r i)` sampled at the
  `n+1` fixed distinct nodes `node j = (j : ℝ)`. As a map of `r` it is a finite product
  `∏ i, (node j - r i)` — **continuous, hence measurable** (`evalMap_measurable`).
* On the **antitone subtype** `{r | Antitone r}` (a closed, hence standard-Borel subset of
  `Fin n → ℝ`) `evalMap` is **injective** (`evalMap_injOn_antitone`): equal values at
  `n+1 > deg` distinct nodes force the two monic degree-`n` polynomials equal
  (`Polynomial.eq_of_degrees_lt_of_eval_index_eq`), hence equal root-multisets
  (`Polynomial.roots_multiset_prod_X_sub_C`), hence equal decreasing sorts, hence equal
  tuples (`List.ofFn_inj`).
* A measurable injection from a standard-Borel space into a countably-separated space is a
  **measurable embedding** (`Measurable.measurableEmbedding`), and
  `MeasurableEmbedding.measurable_comp_iff` inverts it:
  `Measurable (evalMap ∘ f) → Measurable f` (`measurable_orderedRoots_of_evalMap`).
* Instantiate at `f z := (A z).IsHermitian.eigenvalues₀`. The composite
  `evalMap (eigenvalues₀ z) j = (A z).charpoly.eval (node j) = det (node j • 1 - A z)`
  (`charpoly_eq_prod_eigenvalues₀` + `Matrix.eval_charpoly`) is **measurable in `z`**: a
  determinant is a finite sum of finite products of the (measurable) entries
  (`measurable_det_of_entries`).

Every step is Proved sorry-free; no cited/assumed analytic interface.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Matrix Polynomial Finset

/-- The `n+1` fixed distinct real evaluation nodes `node j = (j : ℝ)`, `j : Fin (n+1)`. -/
noncomputable def orderedRootsNode {n : ℕ} (j : Fin (n + 1)) : ℝ := ((j : ℕ) : ℝ)

lemma orderedRootsNode_injective {n : ℕ} :
    Function.Injective (orderedRootsNode (n := n)) :=
  fun _ _ h => Fin.val_injective (Nat.cast_injective h)

/-- `evalMap r j` is the monic polynomial `∏ i, (X - C (r i))` evaluated at the node `node j`. -/
noncomputable def evalMap {n : ℕ} (r : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun j => (∏ i : Fin n, (X - C (r i))).eval (orderedRootsNode j)

lemma evalMap_eq_prod {n : ℕ} (r : Fin n → ℝ) (j : Fin (n + 1)) :
    evalMap r j = ∏ i : Fin n, (orderedRootsNode j - r i) := by
  simp only [evalMap, eval_prod, eval_sub, eval_X, eval_C]

/-- `evalMap` is continuous, hence measurable, as a map `(Fin n → ℝ) → (Fin (n+1) → ℝ)`. -/
lemma evalMap_continuous {n : ℕ} : Continuous (evalMap (n := n)) := by
  refine continuous_pi fun j => ?_
  simp only [evalMap_eq_prod]
  exact continuous_finset_prod _ fun i _ => continuous_const.sub (continuous_apply i)

lemma evalMap_measurable {n : ℕ} : Measurable (evalMap (n := n)) :=
  evalMap_continuous.measurable

/-- The monic product `∏ i, (X - C (r i))` has `natDegree ≤ n`. -/
lemma natDegree_prod_X_sub_C_le {n : ℕ} (r : Fin n → ℝ) :
    (∏ i : Fin n, (X - C (r i))).natDegree ≤ n := by
  refine (natDegree_prod_le _ _).trans (le_of_eq ?_)
  calc ∑ i : Fin n, (X - C (r i)).natDegree = ∑ _i : Fin n, 1 := by
        simp
    _ = n := by simp

/-- The value-multiset of an antitone tuple sorts (decreasing) to its `ofFn` list. -/
lemma antitone_sort_map_univ {n : ℕ} (r : Fin n → ℝ) (hr : Antitone r) :
    (Multiset.map r Finset.univ.val).sort (· ≥ ·) = List.ofFn r := by
  simp_rw [Fin.univ_val_map, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact hr.sortedGE_ofFn

/-- The monic product written as a `Multiset.prod` over the value-multiset. -/
lemma prod_X_sub_C_eq_map {n : ℕ} (r : Fin n → ℝ) :
    (∏ i : Fin n, (X - C (r i)))
      = ((Multiset.map r Finset.univ.val).map fun a => X - C a).prod := by
  rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  rfl

/-- **Injectivity on the antitone subtype.** Two antitone tuples with equal Vieta evaluations at the
`n+1` nodes are equal. -/
lemma evalMap_injOn_antitone {n : ℕ} :
    Set.InjOn (evalMap (n := n)) {r : Fin n → ℝ | Antitone r} := by
  intro r hr s hs hrs
  have hr' : Antitone r := hr
  have hs' : Antitone s := hs
  -- The two monic polynomials.
  set p := ∏ i : Fin n, (X - C (r i)) with hp
  set q := ∏ i : Fin n, (X - C (s i)) with hq
  -- Equal evaluations at `n+1` distinct nodes force `p = q`.
  have hpq : p = q := by
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (v := orderedRootsNode)
      (Finset.univ : Finset (Fin (n + 1))) orderedRootsNode_injective.injOn ?_ ?_ ?_
    · calc p.degree ≤ (p.natDegree : WithBot ℕ) := degree_le_natDegree
        _ ≤ (n : WithBot ℕ) := by exact_mod_cast natDegree_prod_X_sub_C_le r
        _ < (Finset.univ : Finset (Fin (n + 1))).card := by
            rw [Finset.card_univ, Fintype.card_fin]; exact_mod_cast Nat.lt_succ_self n
    · calc q.degree ≤ (q.natDegree : WithBot ℕ) := degree_le_natDegree
        _ ≤ (n : WithBot ℕ) := by exact_mod_cast natDegree_prod_X_sub_C_le s
        _ < (Finset.univ : Finset (Fin (n + 1))).card := by
            rw [Finset.card_univ, Fintype.card_fin]; exact_mod_cast Nat.lt_succ_self n
    · intro j _
      have := congrFun hrs j
      simpa only [evalMap, hp, hq] using this
  -- `p = q` ⟹ equal root-multisets ⟹ equal decreasing sorts ⟹ equal tuples.
  have hroots : Multiset.map r Finset.univ.val = Multiset.map s Finset.univ.val := by
    have hpr : p.roots = Multiset.map r Finset.univ.val := by
      rw [hp, prod_X_sub_C_eq_map, roots_multiset_prod_X_sub_C]
    have hqr : q.roots = Multiset.map s Finset.univ.val := by
      rw [hq, prod_X_sub_C_eq_map, roots_multiset_prod_X_sub_C]
    rw [← hpr, ← hqr, hpq]
  have hofn : List.ofFn r = List.ofFn s := by
    rw [← antitone_sort_map_univ r hr', ← antitone_sort_map_univ s hs', hroots]
  exact List.ofFn_inj.mp hofn

/-- The set of antitone tuples is closed (finite intersection of closed half-spaces). -/
lemma isClosed_setOf_antitone {n : ℕ} : IsClosed {r : Fin n → ℝ | Antitone r} := by
  have hset : {r : Fin n → ℝ | Antitone r}
      = ⋂ (pq : Fin n × Fin n) (_ : pq.1 ≤ pq.2), {r : Fin n → ℝ | r pq.2 ≤ r pq.1} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h pq hpq; exact h hpq
    · intro h a b hab; exact h (a, b) hab
  rw [hset]
  exact isClosed_iInter fun pq => isClosed_iInter fun _ =>
    isClosed_le (continuous_apply pq.2) (continuous_apply pq.1)

/-- **The engine (Lusin–Souslin inversion).** An antitone-valued `f` whose Vieta-evaluation
composite `evalMap ∘ f` is measurable is itself measurable. -/
lemma measurable_orderedRoots_of_evalMap {n : ℕ} {X : Type*} [MeasurableSpace X]
    (f : X → Fin n → ℝ) (hant : ∀ z, Antitone (f z))
    (hmeas : Measurable (fun z => evalMap (f z))) :
    Measurable f := by
  have hSmeas : MeasurableSet {r : Fin n → ℝ | Antitone r} :=
    isClosed_setOf_antitone.measurableSet
  haveI : StandardBorelSpace {r : Fin n → ℝ | Antitone r} := hSmeas.standardBorel
  -- The Vieta map restricted to the antitone subtype.
  set V : {r : Fin n → ℝ | Antitone r} → (Fin (n + 1) → ℝ) := fun r => evalMap (r : Fin n → ℝ)
    with hV
  have hVmeas : Measurable V := evalMap_measurable.comp measurable_subtype_coe
  have hVinj : Function.Injective V := by
    intro a b hab
    exact Subtype.ext (evalMap_injOn_antitone a.2 b.2 hab)
  have hemb : MeasurableEmbedding V := hVmeas.measurableEmbedding hVinj
  -- Lift `f` through the subtype.
  set g : X → {r : Fin n → ℝ | Antitone r} := fun z => ⟨f z, hant z⟩ with hg
  have hcomp : Measurable (V ∘ g) := hmeas
  have hgmeas : Measurable g := hemb.measurable_comp_iff.mp hcomp
  exact measurable_subtype_coe.comp hgmeas

/-- `charpoly` of a real Hermitian matrix as the monic product over its sorted eigenvalues. -/
lemma charpoly_eq_prod_eigenvalues₀ {M₂ : ℕ} {A : Matrix (Fin M₂) (Fin M₂) ℝ}
    (hA : A.IsHermitian) :
    A.charpoly = ∏ j : Fin (Fintype.card (Fin M₂)), (X - C (hA.eigenvalues₀ j)) := by
  rw [hA.charpoly_eq]
  exact Fintype.prod_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm _ _ fun _ => rfl

/-- A determinant of a family with measurable entries is measurable. -/
lemma measurable_det_of_entries {X : Type*} [MeasurableSpace X] {m : ℕ}
    (B : X → Matrix (Fin m) (Fin m) ℝ) (hB : ∀ i k, Measurable (fun z => B z i k)) :
    Measurable (fun z => (B z).det) := by
  simp_rw [Matrix.det_apply']
  refine Finset.measurable_sum _ fun σ _ => ?_
  exact (Finset.measurable_prod _ fun i _ => hB (σ i) i).const_mul _

/-- **Brick F2a — measurable sorted eigenvalues.** The sorted eigenvalues of a measurable Hermitian
family are a measurable function of the parameter. -/
theorem measurableEigenvalues₀ {X : Type*} [MeasurableSpace X] {M₂ : ℕ}
    (A : X → Matrix (Fin M₂) (Fin M₂) ℝ) (hA : Measurable A)
    (hherm : ∀ z, (A z).IsHermitian) :
    Measurable (fun z => (hherm z).eigenvalues₀) := by
  -- Entrywise measurability of `A`.
  have hentry : ∀ i k, Measurable (fun z => A z i k) := fun i k =>
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA)
  refine measurable_orderedRoots_of_evalMap _ (fun z => (hherm z).eigenvalues₀_antitone) ?_
  -- The composite is a determinant with measurable entries.
  have key : ∀ z, (fun z => evalMap ((hherm z).eigenvalues₀)) z
      = fun j => (Matrix.scalar (Fin M₂) (orderedRootsNode j) - A z).det := by
    intro z
    funext j
    simp only [evalMap]
    rw [← charpoly_eq_prod_eigenvalues₀ (hherm z), Matrix.eval_charpoly]
  rw [funext key]
  refine measurable_pi_lambda _ fun j => ?_
  refine measurable_det_of_entries _ fun i k => ?_
  simp only [Matrix.sub_apply]
  exact measurable_const.sub (hentry i k)

end DLNFibre.DLN.RLCT
