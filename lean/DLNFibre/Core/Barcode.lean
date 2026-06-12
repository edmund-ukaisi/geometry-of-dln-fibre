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

/-- **The splitting fact, relative to an ambient pair `(P, Q)`** (recursion-ready form). If `f`
restricts to `P → Q` (`P.map f ≤ Q`), `v ∈ P` with `f v ≠ 0`, and `Q = k·(f v) ⊕ U` *inside `Q`*
(`Disjoint (k·f v) U` and `k·(f v) ⊔ U = Q`), then `P = k·v ⊕ (f⁻¹(U) ⊓ P)` *inside `P`*. This is
the form the total-dimension **induction** consumes: peeling a line off a *subrepresentation* `P_t`
(not just the ambient space) — the splitting happens within `P`, keeping the types fixed. Taking
`P = ⊤, Q = ⊤` recovers `isCompl_span_singleton_comap`. -/
theorem relSplitting (f : V →ₗ[k] W) {v : V} {P : Submodule k V} {Q : Submodule k W}
    (hvP : v ∈ P) (hfv : f v ≠ 0) (hPQ : P.map f ≤ Q)
    {U : Submodule k W} (hdisj : Disjoint (k ∙ f v) U) (hsup : k ∙ f v ⊔ U = Q) :
    Disjoint (k ∙ v) (U.comap f ⊓ P) ∧ k ∙ v ⊔ (U.comap f ⊓ P) = P := by
  refine ⟨?_, ?_⟩
  · -- Disjoint inside `P` (the `P`-membership is unused, exactly as in the ambient case).
    rw [Submodule.disjoint_def]
    intro x hxv hxinf
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxv
    have hxU : c • f v ∈ U := by
      have h1 : (c • v) ∈ U.comap f := (Submodule.mem_inf.mp hxinf).1
      rwa [Submodule.mem_comap, map_smul] at h1
    have hmem : c • f v ∈ (k ∙ f v) := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hzero : c • f v = 0 := (Submodule.disjoint_def.mp hdisj) _ hmem hxU
    rcases smul_eq_zero.mp hzero with hc | hfv'
    · rw [hc, zero_smul]
    · exact absurd hfv' hfv
  · -- Span `= P`: `≤` from `v ∈ P`; `≥` writes `f x = a·(f v) + u` for `x ∈ P` (`Q = k·f v ⊔ U`).
    apply le_antisymm
    · exact sup_le (by rw [Submodule.span_singleton_le_iff_mem]; exact hvP) inf_le_right
    · intro x hxP
      have hfx : f x ∈ k ∙ f v ⊔ U := by
        rw [hsup]; exact hPQ (Submodule.mem_map.mpr ⟨x, hxP, rfl⟩)
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hfx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
      have hmemv : a • v ∈ k ∙ v :=
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      have hrest : x - a • v ∈ U.comap f ⊓ P := by
        refine Submodule.mem_inf.mpr ⟨?_, P.sub_mem hxP (P.smul_mem a hvP)⟩
        rw [Submodule.mem_comap, map_sub, map_smul]
        have hz' : f x - a • f v = z := by rw [← hyz]; abel
        rw [hz']; exact hz
      have hx : x = a • v + (x - a • v) := by abel
      rw [hx]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hmemv) (Submodule.mem_sup_right hrest)

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

/-- `relSplitting` generalizes the ambient splitting fact: at `P = Q = ⊤` it reproduces
`isCompl_span_singleton_comap` (unfolded to `Disjoint` + `⊔ = ⊤`). -/
example (f : V →ₗ[k] W) {v : V} (hfv : f v ≠ 0) {U : Submodule k W} (h : IsCompl (k ∙ f v) U) :
    Disjoint (k ∙ v) (U.comap f ⊓ ⊤) ∧ k ∙ v ⊔ (U.comap f ⊓ ⊤) = ⊤ :=
  relSplitting f Submodule.mem_top hfv le_top h.disjoint (codisjoint_iff.mp h.codisjoint)

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

/-- The composite over a single edge `e` (vertex `e.castSucc → e.succ`) is that edge's map `f e`. -/
theorem compMap_edge (e : Fin N) (h : e.castSucc ≤ e.succ) :
    compMap V f e.castSucc e.succ h = f e := by
  have hstep := compMap_succ V f e.castSucc e le_rfl
  rw [compMap_self V f e.castSucc, LinearMap.comp_id] at hstep
  exact hstep

/-! ## The peel — local content (pointwise, no recursion)

The geometric heart of the barcode induction (design §2.2 steps 3–4), but *pointwise* rather than by
the design's downward recursion: along a forward trajectory `v_t := compMap f s t vs` that survives
to a top vertex `j` (`compMap f s j vs ≠ 0`), a complement `U_j` of the top line `k·v_j` pulls back
to `U_t := (compMap f t j)⁻¹(U_j)`, which is a complement of the line `k·v_t` at *every* interior
vertex `t ∈ [s,j]`. The collapse of the recursion is `compMap_trans`: `compMap f t j` sends
`v_t ↦ v_j`, so the splitting fact applies directly at each `t` with no threading down the chain.
This isolates the design's "single hardest formal step" to a one-line application of the splitting
fact plus the composition law. (Index-finding — the least-nonzero `s`, the last-nonzero `j` — and
the global total-dimension drop / strong induction are the remaining assembly; see the thread
findings.) -/

/-- **The interval complement splits the line at every interior vertex.** For a trajectory
`v_t = compMap f s t vs` surviving to `j` and a top complement `IsCompl (k·v_j) U_j`, the pullback
`U_t := (compMap f t j)⁻¹(U_j)` satisfies `IsCompl (k·v_t) U_t` for every `t ∈ [s,j]`. The splitting
fact applied to `g = compMap f t j` (sends `v_t ↦ v_j` by `compMap_trans`). -/
theorem isCompl_interval_complement
    {s j : Fin (N + 1)} (hsj : s ≤ j) (vs : V s) (hvs : compMap V f s j hsj vs ≠ 0)
    {Uj : Submodule k (V j)} (hUj : IsCompl (k ∙ compMap V f s j hsj vs) Uj)
    {t : Fin (N + 1)} (hst : s ≤ t) (htj : t ≤ j) :
    IsCompl (k ∙ compMap V f s t hst vs) (Uj.comap (compMap V f t j htj)) := by
  have hcomp : compMap V f t j htj (compMap V f s t hst vs)
      = compMap V f s j (hst.trans htj) vs := by
    rw [compMap_trans V f s hst htj]; rfl
  refine isCompl_span_singleton_comap (compMap V f t j htj)
    (v := compMap V f s t hst vs) ?_ ?_
  · rw [hcomp]; exact hvs
  · rw [hcomp]; exact hUj

/-- **The interval complement drops `finrank` by one at every interior vertex.** With the trajectory
and top complement as above, `finrank (U_t) + 1 = finrank (V_t)` for every `t ∈ [s,j]` — so summing
over the interval, the bar removes `j − s + 1` from the total dimension (the engine of termination
of the total-dimension induction). The dimension-drop fact applied to `g = compMap f t j`. -/
theorem finrank_interval_complement [∀ t, FiniteDimensional k (V t)]
    {s j : Fin (N + 1)} (hsj : s ≤ j) (vs : V s) (hvs : compMap V f s j hsj vs ≠ 0)
    {Uj : Submodule k (V j)} (hUj : IsCompl (k ∙ compMap V f s j hsj vs) Uj)
    {t : Fin (N + 1)} (hst : s ≤ t) (htj : t ≤ j) :
    Module.finrank k (Uj.comap (compMap V f t j htj)) + 1 = Module.finrank k (V t) := by
  have hcomp : compMap V f t j htj (compMap V f s t hst vs)
      = compMap V f s j (hst.trans htj) vs := by
    rw [compMap_trans V f s hst htj]; rfl
  refine finrank_comap_add_one (compMap V f t j htj) (v := compMap V f s t hst vs) ?_ ?_
  · rw [hcomp]; exact hvs
  · rw [hcomp]; exact hUj

/-- **The interval complement is forward-closed (a subrepresentation across each interior edge).**
For an edge `e` inside the bar (`e.succ ≤ j`), the pullback complement at the lower endpoint equals
the preimage under `f e` of the one at the upper endpoint:
`U_{e.castSucc} = (f e)⁻¹(U_{e.succ})`. Hence `f e` maps `U_{e.castSucc}` into `U_{e.succ}`, so the
complement chain is a subrepresentation along the bar. From `compMap_trans` +
`compMap_edge` + `comap_comp`. -/
theorem comap_compMap_edge {j : Fin (N + 1)} (e : Fin N) (hej : e.succ ≤ j)
    (Uj : Submodule k (V j)) :
    Uj.comap (compMap V f e.castSucc j ((Fin.castSucc_le_succ e).trans hej))
      = (Uj.comap (compMap V f e.succ j hej)).comap (f e) := by
  have hsplit : compMap V f e.castSucc j ((Fin.castSucc_le_succ e).trans hej)
      = (compMap V f e.succ j hej).comp (f e) := by
    rw [compMap_trans V f e.castSucc (Fin.castSucc_le_succ e) hej,
      compMap_edge V f e (Fin.castSucc_le_succ e)]
  rw [hsplit, Submodule.comap_comp]

section ChainWitness

/-! ## Non-vacuity for the chain layer

The two-vertex identity chain `ℚ --id--> ℚ` (`N = 1`): the forward trajectory from `vs = 1`
survives to the top vertex (`compMap = id`, value `1 ≠ 0`), so the peel theorems' antecedents are
satisfiable and `isCompl_interval_complement` / `finrank_interval_complement` fire on it. -/

/-- Witness chain spaces: two vertices, both `ℚ`. -/
abbrev witnessV : Fin 2 → Type := fun _ => ℚ

/-- Witness edge: the identity `ℚ →ₗ[ℚ] ℚ`. -/
def witnessF : ∀ t : Fin 1, witnessV t.castSucc →ₗ[ℚ] witnessV t.succ := fun _ => LinearMap.id

/-- The composite over the single edge is the identity, so the trajectory from `1` survives:
`compMap witnessV witnessF 0 1 (1) = 1 ≠ 0`. -/
theorem compMap_witness : compMap witnessV witnessF 0 1 (by decide) (1 : ℚ) = 1 := by
  have h01 : compMap witnessV witnessF (0 : Fin 1).castSucc (0 : Fin 1).succ
      (Fin.castSucc_le_succ 0) = witnessF 0 := compMap_edge witnessV witnessF 0 _
  exact congrFun (congrArg _ h01) 1

/-- The trajectory survives, so the peel's antecedent `compMap … vs ≠ 0` is satisfiable. -/
example : compMap witnessV witnessF 0 1 (by decide) (1 : ℚ) ≠ 0 := by
  rw [compMap_witness]; exact one_ne_zero

/-- `isCompl_interval_complement` fires on the witness chain: a complement of the top line pulls
back to a complement of the source line at vertex `0`. -/
example : ∃ Uj : Submodule ℚ (witnessV 1),
    IsCompl (ℚ ∙ compMap witnessV witnessF (0 : Fin 2) 0 le_rfl (1 : ℚ))
      (Uj.comap (compMap witnessV witnessF (0 : Fin 2) 1 (by decide))) := by
  have hvs : compMap witnessV witnessF 0 1 (by decide) (1 : ℚ) ≠ 0 := by
    rw [compMap_witness]; exact one_ne_zero
  obtain ⟨Uj, hUj⟩ :=
    Submodule.exists_isCompl (ℚ ∙ compMap witnessV witnessF 0 1 (by decide) (1 : ℚ))
  exact ⟨Uj, isCompl_interval_complement witnessV witnessF (by decide) 1 hvs hUj le_rfl (by decide)⟩

end ChainWitness

end Chain

/-! ## Subrepresentations and total dimension (induction substrate)

The total-dimension induction runs over **subrepresentations** `P_* ≤ V_*` of a *fixed* ambient
chain — families of submodules closed forward under the edge maps. Keeping the ambient `V` fixed and
inducting on `∑_t finrank (P_t)` (a `ℕ`) means the types never change; the peel produces a smaller
subrep and `relSplitting` does the splitting *inside* `P`. -/

section Subrep

variable {k : Type u} [Field k] {N : ℕ}
  (V : Fin (N + 1) → Type v) [∀ t, AddCommGroup (V t)] [∀ t, Module k (V t)]
  (f : ∀ t : Fin N, V t.castSucc →ₗ[k] V t.succ)

/-- A **subrepresentation**: a family of submodules forward-closed under every edge map,
`f e (P e.castSucc) ⊆ P e.succ`. -/
def IsSubrep (P : ∀ t, Submodule k (V t)) : Prop :=
  ∀ e : Fin N, (P e.castSucc).map (f e) ≤ P e.succ

/-- The whole chain `V_*` (every `P_t = ⊤`) is a subrepresentation. -/
theorem isSubrep_top : IsSubrep V f (fun _ => ⊤) := fun _ => le_top

/-- The composite map preserves a subrepresentation: `x ∈ P i ⟹ compMap f i j x ∈ P j`. -/
theorem compMap_mem {P : ∀ t, Submodule k (V t)} (hP : IsSubrep V f P) {i j : Fin (N + 1)}
    (hij : i ≤ j) {x : V i} (hx : x ∈ P i) : compMap V f i j hij x ∈ P j := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl : i = 0 := Fin.le_zero_iff.mp hij
    rw [show compMap V f 0 0 hij = LinearMap.id from compMap_self V f 0]
    exact hx
  | succ p ih =>
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rw [show compMap V f p.succ p.succ hij = LinearMap.id from compMap_self V f p.succ]; exact hx
    · have hip : i ≤ p.castSucc := by rw [Fin.le_castSucc_iff]; exact hlt
      rw [compMap_succ V f i p hip, LinearMap.comp_apply]
      exact hP p (Submodule.mem_map_of_mem (ih hip))

/-- The total dimension `∑_t finrank (P_t)` of a subrep family — the induction's well-founded
measure. -/
noncomputable def totalDim [∀ t, FiniteDimensional k (V t)] (P : ∀ t, Submodule k (V t)) : ℕ :=
  ∑ t, Module.finrank k (P t)

/-! ### Index-finding: the least-nonzero vertex `s` and the last-nonzero vertex `j` -/

/-- The **least vertex** `s` with `P_s ≠ ⊥` (every earlier vertex is `⊥`). The bottom of the bar;
its minimality is what makes the peeled complement forward-closed across the edge entering `s`. -/
theorem exists_least_nonzero {P : ∀ t, Submodule k (V t)} (h : ∃ t, P t ≠ ⊥) :
    ∃ s, P s ≠ ⊥ ∧ ∀ t, t < s → P t = ⊥ := by
  classical
  let S := Finset.univ.filter (fun t => P t ≠ ⊥)
  have hSne : S.Nonempty := by
    obtain ⟨t, ht⟩ := h; exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
  refine ⟨S.min' hSne, (Finset.mem_filter.mp (S.min'_mem hSne)).2, fun t ht => ?_⟩
  by_contra hP
  exact absurd (S.min'_le t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩)) (not_le.mpr ht)

/-- The **last vertex** `j ≥ s` at which the forward trajectory `compMap f s · vs` is nonzero
(beyond `j` it vanishes). The top of the bar; `compMap f s j vs ≠ 0` feeds the top complement, and
the death `compMap f s t vs = 0` for `t > j` is what makes the bar an interval module. -/
theorem exists_last_nonzero {s : Fin (N + 1)} {vs : V s} (hvs : vs ≠ 0) :
    ∃ j, ∃ hsj : s ≤ j, compMap V f s j hsj vs ≠ 0
      ∧ ∀ t (hst : s ≤ t), j < t → compMap V f s t hst vs = 0 := by
  classical
  let S := Finset.univ.filter (fun t => ∃ h : s ≤ t, compMap V f s t h vs ≠ 0)
  have hsS : s ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, by
    rw [show compMap V f s s le_rfl = LinearMap.id from compMap_self V f s]; exact hvs⟩
  have hSne : S.Nonempty := ⟨s, hsS⟩
  refine ⟨S.max' hSne, S.le_max' s hsS, ?_, fun t hst htgt => ?_⟩
  · obtain ⟨_, hne⟩ := (Finset.mem_filter.mp (S.max'_mem hSne)).2
    exact hne
  · by_contra hne
    exact absurd (S.le_max' t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hst, hne⟩))
      (not_le.mpr htgt)

end Subrep

end DLNFibre.Core
