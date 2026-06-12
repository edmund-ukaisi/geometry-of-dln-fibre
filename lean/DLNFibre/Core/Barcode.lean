import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# `DLNFibre.Core.Barcode` — the barcode-basis / interval normal form (rung 4d, the crux)

The **existence** half of the type-A Gabriel decomposition (Le Halleur–Rimányi 2024, Thm 2.5),
proved on an **abstract chain** of linear maps `V₀ --f₁--> V₁ --⋯--> V_N` between finite-dimensional
`k`-vector spaces (`k` a field). Working abstractly keeps the proof inside Mathlib's
`Submodule`/`comap`/`IsCompl` API and isolates the `Fin`/`Matrix` cast work to a (later) transport
lemma onto `Setup.Tuple`.

The single load-bearing lemma is the **splitting fact** (`isCompl_span_singleton_comap`):

> if `f v = w ≠ 0` and `W = k·w ⊕ U`, then `V = k·v ⊕ f⁻¹(U)`.

Applied down a chain (with `f_t v_{t-1} = v_t` along a forward trajectory), it peels one
interval-supported line off the chain at each step; total-dimension induction then exhibits the
chain as a direct sum of interval modules. **Scope.** This file states the existence/normal-form
content only; it is *not* the full Gabriel bijection (uniqueness is a separate, near-free step via
`RankPattern.diff_cumul`), and the name reflects that.

**Typeclass.** `Field k` (the splitting fact needs `c • w = 0 ∧ w ≠ 0 ⟹ c = 0`, i.e.
`NoZeroSMulDivisors`, automatic for a vector space) and finite-dimensional spaces where `finrank`
is used. **Dependency rule:** never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Submodule

universe u v

/-! ## The splitting fact (the load-bearing lemma)

For a linear map `f : V → W`, a vector `v` with `f v = w ≠ 0`, and a complement decomposition
`W = k·w ⊕ U`, the preimage `f⁻¹(U)` is a complement of the line `k·v` in `V`: `V = k·v ⊕ f⁻¹(U)`.
This is the one geometric fact behind the whole barcode peel; everything else is bookkeeping. -/

variable {k V W : Type*} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- **The splitting fact.** If `f v = w ≠ 0` and `W = k·w ⊕ U` (`IsCompl (k ∙ w) U`), then
`V = k·v ⊕ f⁻¹(U)` (`IsCompl (k ∙ v) (U.comap f)`). The preimage of a complement of the image line
is a complement of the source line. -/
theorem isCompl_span_singleton_comap (f : V →ₗ[k] W) {v : V} (hv : f v ≠ 0)
    {U : Submodule k W} (h : IsCompl (k ∙ f v) U) :
    IsCompl (k ∙ v) (U.comap f) := by
  constructor
  · -- Disjoint: `c • v ∈ f⁻¹(U) ⟹ c • (f v) ∈ U ∩ k·(f v) = 0 ⟹ c = 0`.
    rw [Submodule.disjoint_def]
    intro x hxv hxU
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxv
    rw [Submodule.mem_comap, map_smul] at hxU
    have hmem : c • f v ∈ (k ∙ f v) := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hzero : c • f v = 0 := (Submodule.disjoint_def.mp h.disjoint) _ hmem hxU
    rcases smul_eq_zero.mp hzero with hc | hfv
    · rw [hc, zero_smul]
    · exact absurd hfv hv
  · -- Codisjoint: for `x`, write `f x = a·(f v) + u` (`u ∈ U`); then `x = a·v + (x − a·v)`
    -- with `f (x − a·v) = u ∈ U`.
    rw [codisjoint_iff, eq_top_iff]
    intro x _
    have htop : (k ∙ f v) ⊔ U = ⊤ := codisjoint_iff.mp h.codisjoint
    have hfx : f x ∈ (k ∙ f v) ⊔ U := by rw [htop]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hfx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hmemv : a • v ∈ k ∙ v :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hrest : x - a • v ∈ U.comap f := by
      rw [Submodule.mem_comap, map_sub, map_smul]
      have hz' : f x - a • f v = z := by rw [← hyz]; abel
      rw [hz']; exact hz
    have hx : x = a • v + (x - a • v) := by abel
    rw [hx]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hmemv) (Submodule.mem_sup_right hrest)

/-- Over a field complements always exist, so the splitting fact applies to **every** `f, v` with
`f v ≠ 0`: there is a complement `U` of the image line `k·(f v)` whose preimage `f⁻¹(U)` is a
complement of the source line `k·v`. This is the form the barcode peel consumes — choose a
complement at the top of an interval and pull it back down the chain. -/
theorem exists_isCompl_comap (f : V →ₗ[k] W) {v : V} (hv : f v ≠ 0) :
    ∃ U : Submodule k W, IsCompl (k ∙ f v) U ∧ IsCompl (k ∙ v) (U.comap f) := by
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (k ∙ f v)
  exact ⟨U, hU, isCompl_span_singleton_comap f hv hU⟩

/-- **The dimension drop of one peel.** Peeling the line `k·v` off `V` through the preimage
complement drops `finrank` by exactly one: `finrank (f⁻¹U) + 1 = finrank V`. This is the
quantitative engine of the total-dimension induction — each interval line removed lowers the
running dimension total by one at its vertex, so the induction terminates. -/
theorem finrank_comap_add_one [FiniteDimensional k V] (f : V →ₗ[k] W) {v : V} (hv : f v ≠ 0)
    {U : Submodule k W} (h : IsCompl (k ∙ f v) U) :
    Module.finrank k (U.comap f) + 1 = Module.finrank k V := by
  have hcompl := isCompl_span_singleton_comap f hv h
  have hadd := Submodule.finrank_add_eq_of_isCompl hcompl
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0, map_zero])
  rw [finrank_span_singleton hv0] at hadd
  omega

section Witness

/-! ## Non-vacuity

The splitting fact's antecedent `f v ≠ 0` is satisfiable (the identity on `ℚ` at `v = 1`), and
over a field the rest of the antecedent (`IsCompl (k ∙ f v) U`) is *always* met, so
`exists_isCompl_comap` and `finrank_comap_add_one` fire on a concrete instance. -/

/-- A concrete `f, v` with `f v ≠ 0`: the identity on `ℚ` sends `1 ↦ 1 ≠ 0`. -/
example : (LinearMap.id (R := ℚ) (M := ℚ)) 1 ≠ 0 := one_ne_zero

/-- The splitting fact's complement form fires on the concrete instance. -/
example : ∃ U : Submodule ℚ ℚ,
    IsCompl (ℚ ∙ (LinearMap.id (R := ℚ) (M := ℚ)) 1) U
      ∧ IsCompl (ℚ ∙ (1 : ℚ)) (U.comap (LinearMap.id (R := ℚ) (M := ℚ))) :=
  exists_isCompl_comap _ one_ne_zero

/-- The dimension drop fires on the concrete instance: removing the line drops `finrank` by one. -/
example : ∃ U : Submodule ℚ ℚ,
    Module.finrank ℚ (U.comap (LinearMap.id (R := ℚ) (M := ℚ))) + 1 = Module.finrank ℚ ℚ := by
  obtain ⟨U, hU, _⟩ := exists_isCompl_comap (LinearMap.id (R := ℚ) (M := ℚ)) one_ne_zero
  exact ⟨U, finrank_comap_add_one _ one_ne_zero hU⟩

end Witness

/-! ## Abstract chains and the composite map (cast-free `submult` analogue)

An abstract chain is a family `V : Fin (N+1) → Type` of `k`-vector spaces with edge maps
`f t : V t.castSucc →ₗ[k] V t.succ`. The composite `compMap f i j : V i →ₗ[k] V j` (for `i ≤ j`)
is the ordered composition `f_{j-1} ∘ ⋯ ∘ f_i` of the edges from vertex `i` to vertex `j` (the
identity at `i = j`). It is the abstract, cast-free analogue of `Setup.submult`: defined by
`Nat.leRec` on the *upper* index with a function-valued motive carrying the `< N+1` bound and
holding `i` fixed, so the base (`= id`) and step (`compose f_m on the left`) close by the
`Nat.leRec` reduction lemmas with no dependent cast in any statement. -/

section Chain

variable {k : Type u} [Field k] {N : ℕ}
  (V : Fin (N + 1) → Type v) [∀ t, AddCommGroup (V t)] [∀ t, Module k (V t)]
  (f : ∀ t : Fin N, V t.castSucc →ₗ[k] V t.succ)

/-- The left-compose step of `compMap`: prepend the edge `f_m` to the composite reaching vertex
`m`. Named so the `Nat.leRec` reduction lemmas have a stable term (the `submultStep` analogue). -/
def compMapStep (i : Fin (N + 1)) :
    ⦃m : ℕ⦄ → (i ≤ m) → ((hm : m < N + 1) → (V i →ₗ[k] V ⟨m, hm⟩)) →
      ((hm : m + 1 < N + 1) → (V i →ₗ[k] V ⟨m + 1, hm⟩)) :=
  fun {m} _ rec hm =>
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ hm⟩
    show V i →ₗ[k] V p.succ from
      (f p).comp (show V i →ₗ[k] V p.castSucc from rec p.castSucc.isLt)

/-- The composite map `compMap f i j = f_{j-1} ∘ ⋯ ∘ f_i : V i →ₗ[k] V j` (the identity at
`i = j`). The abstract, cast-free analogue of `Setup.submult` (the `i = 0` slice is the chain's
total map). -/
def compMap (i j : Fin (N + 1)) (hij : i ≤ j) : V i →ₗ[k] V j :=
  Nat.leRec (motive := fun m _ => (hm : m < N + 1) → (V i →ₗ[k] V ⟨m, hm⟩))
    (fun _ => LinearMap.id) (compMapStep V f i) hij j.isLt

/-- The diagonal composite is the identity (the empty composition). -/
theorem compMap_self (i : Fin (N + 1)) : compMap V f i i le_rfl = LinearMap.id := by
  unfold compMap
  exact congrFun (Nat.leRec_self (motive := fun m _ => (hm : m < N + 1) →
    (V i →ₗ[k] V ⟨m, hm⟩)) (fun _ => LinearMap.id) (compMapStep V f i)) i.isLt

/-- **Composition step** (the `submult_succ` analogue): the composite to `p.succ` gains its top
edge on the left, `compMap f i p.succ = f_p ∘ compMap f i p.castSucc`. -/
theorem compMap_succ (i : Fin (N + 1)) (p : Fin N) (h : i ≤ p.castSucc) :
    compMap V f i p.succ (h.trans (Fin.castSucc_le_succ p))
      = (f p).comp (compMap V f i p.castSucc h) := by
  unfold compMap
  exact congrFun (Nat.leRec_succ (h1 := Fin.val_fin_le.mpr h)
    (h2 := Fin.val_fin_le.mpr (h.trans (Fin.castSucc_le_succ p)))
    (refl := fun _ => LinearMap.id) (le_succ_of_le := compMapStep V f i)) p.succ.isLt

/-- **Composition law.** The composite splits at any intermediate vertex `m`:
`compMap f i j = compMap f m j ∘ compMap f i m` for `i ≤ m ≤ j`. Proved by induction on the upper
index `j` through `compMap_succ`. The chain analogue of associativity of the ordered product. -/
theorem compMap_trans (i : Fin (N + 1)) {m j : Fin (N + 1)} (him : i ≤ m) (hmj : m ≤ j) :
    compMap V f i j (him.trans hmj)
      = (compMap V f m j hmj).comp (compMap V f i m him) := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl : m = 0 := Fin.le_zero_iff.mp hmj
    obtain rfl : i = 0 := Fin.le_zero_iff.mp him
    rw [compMap_self]; rfl
  | succ p ih =>
    rcases eq_or_lt_of_le hmj with rfl | hlt
    · rw [compMap_self, LinearMap.id_comp]
    · have hmp : m ≤ p.castSucc := by rw [Fin.le_castSucc_iff]; exact hlt
      have himp : i ≤ p.castSucc := him.trans hmp
      rw [compMap_succ V f i p himp, compMap_succ V f m p hmp, ih hmp, LinearMap.comp_assoc]

end Chain

end DLNFibre.Core
