import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Prod

/-!
# Through-layer subspaces for Aoyagi product charts

This file records elementary linear algebra used to choose layer bases adapted
to a fixed total product.  It does not state analytic or RLCT consequences.

The finite-chain section uses source-to-target indexing
`A i : V i.castSucc →ₗ[K] V i.succ`; in Aoyagi's paper notation this is the
chain after reversing the maps `A^(s) : V_(s+1) → V_s`.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

section ThroughLayer

variable {K E F G : Type*} [Field K]
variable [AddCommGroup E] [Module K E]
variable [AddCommGroup F] [Module K F]
variable [AddCommGroup G] [Module K G]

/-- If a subspace avoids the kernel of a composite, it avoids the kernel of the first map. -/
theorem disjoint_ker_of_disjoint_ker_comp (f : E →ₗ[K] F) (g : F →ₗ[K] G)
    (U : Submodule K E) (hU : Disjoint U (LinearMap.ker (g.comp f))) :
    Disjoint U (LinearMap.ker f) :=
  hU.mono_right (LinearMap.ker_le_ker_comp f g)

/-- A linear map restricts to an equivalence from a subspace avoiding its kernel to its image. -/
def linearEquivMapOfDisjointKer (f : E →ₗ[K] F) (U : Submodule K E)
    (hU : Disjoint U (LinearMap.ker f)) : U ≃ₗ[K] U.map f :=
  LinearEquiv.ofBijective
    ((f.comp U.subtype).codRestrict (U.map f) fun x ↦
      Submodule.mem_map_of_mem x.property)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      have hval : f (x : E) = f (y : E) := by
        simpa using congrArg Subtype.val hxy
      have hdiff : (x : E) - (y : E) ∈ U ⊓ LinearMap.ker f := by
        exact ⟨U.sub_mem x.property y.property, by simpa [map_sub] using sub_eq_zero.mpr hval⟩
      have hzero : (x : E) - (y : E) = 0 := by
        simpa [hU.eq_bot] using hdiff
      exact sub_eq_zero.mp hzero,
    by
      rintro ⟨y, hy⟩
      rcases hy with ⟨x, hxU, rfl⟩
      exact ⟨⟨x, hxU⟩, rfl⟩⟩

/-- The restricted equivalence applies as the original linear map. -/
@[simp]
theorem linearEquivMapOfDisjointKer_apply (f : E →ₗ[K] F) (U : Submodule K E)
    (hU : Disjoint U (LinearMap.ker f)) (x : U) :
    (linearEquivMapOfDisjointKer f U hU x : F) = f x :=
  rfl

/-- Mapping a subspace disjoint from the kernel preserves its `finrank`. -/
theorem finrank_map_eq_of_disjoint_ker (f : E →ₗ[K] F) (U : Submodule K E)
    (hU : Disjoint U (LinearMap.ker f)) :
    Module.finrank K (U.map f) = Module.finrank K U :=
  (linearEquivMapOfDisjointKer f U hU).finrank_eq.symm

/-- Disjointness from the kernel of a composite propagates to the image subspace. -/
theorem disjoint_map_ker_of_disjoint_ker_comp (f : E →ₗ[K] F) (g : F →ₗ[K] G)
    (U : Submodule K E) (hU : Disjoint U (LinearMap.ker (g.comp f))) :
    Disjoint (U.map f) (LinearMap.ker g) := by
  rw [disjoint_iff]
  apply le_antisymm ?_ bot_le
  rintro y ⟨hyU, hyg⟩
  rcases hyU with ⟨x, hxU, rfl⟩
  have hxKer : x ∈ LinearMap.ker (g.comp f) := by
    simpa [LinearMap.mem_ker] using hyg
  have hxZero : x = 0 := by
    have hxInf : x ∈ U ⊓ LinearMap.ker (g.comp f) := ⟨hxU, hxKer⟩
    simpa [hU.eq_bot] using hxInf
  simp [hxZero]

/-- A complement to the kernel of a map has the same `finrank` as the range. -/
theorem exists_isCompl_ker_and_finrank_eq_range (P : E →ₗ[K] F) :
    ∃ U : Submodule K E,
      IsCompl U (LinearMap.ker P) ∧
        Module.finrank K U = Module.finrank K (LinearMap.range P) := by
  rcases (LinearMap.ker P).exists_isCompl with ⟨U, hU⟩
  refine ⟨U, hU.symm, ?_⟩
  exact (LinearMap.kerComplementEquivRange P hU.symm).finrank_eq

/-- A complement to the kernel maps onto the range. -/
theorem map_eq_range_of_isCompl_ker (P : E →ₗ[K] F) {U : Submodule K E}
    (hU : IsCompl U (LinearMap.ker P)) :
    U.map P = LinearMap.range P := by
  apply le_antisymm
  · rintro _ ⟨x, _, rfl⟩
    exact LinearMap.mem_range_self P x
  · rintro _ ⟨x, rfl⟩
    obtain ⟨u, z, hu, hz, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hU.codisjoint x
    refine ⟨u, hu, ?_⟩
    rw [map_add, LinearMap.mem_ker.mp hz, add_zero]

/-- Two composable maps admit an intermediate through-subspace. -/
theorem exists_two_step_throughSubspace (f : E →ₗ[K] F) (g : F →ₗ[K] G) :
    ∃ U₂ : Submodule K E, ∃ U₁ : Submodule K F,
      IsCompl U₂ (LinearMap.ker (g.comp f)) ∧
        U₁ = U₂.map f ∧
          Disjoint U₂ (LinearMap.ker f) ∧
            Disjoint U₁ (LinearMap.ker g) ∧
              Module.finrank K U₂ = Module.finrank K (LinearMap.range (g.comp f)) ∧
                Module.finrank K U₁ = Module.finrank K (LinearMap.range (g.comp f)) := by
  rcases exists_isCompl_ker_and_finrank_eq_range (P := g.comp f) with ⟨U₂, hU₂, hfin₂⟩
  let U₁ : Submodule K F := U₂.map f
  have hdisj₂ : Disjoint U₂ (LinearMap.ker f) :=
    disjoint_ker_of_disjoint_ker_comp f g U₂ hU₂.disjoint
  have hdisj₁ : Disjoint U₁ (LinearMap.ker g) := by
    simpa [U₁] using disjoint_map_ker_of_disjoint_ker_comp f g U₂ hU₂.disjoint
  have hfin₁₂ : Module.finrank K U₁ = Module.finrank K U₂ := by
    simpa [U₁] using finrank_map_eq_of_disjoint_ker f U₂ hdisj₂
  refine ⟨U₂, U₁, hU₂, rfl, hdisj₂, hdisj₁, hfin₂, ?_⟩
  exact hfin₁₂.trans hfin₂

end ThroughLayer

section FiniteChain

variable {K : Type*} [Field K] {N : ℕ}
  (V : Fin (N + 1) → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  (A : ∀ i : Fin N, V i.castSucc →ₗ[K] V i.succ)

/-- The recursion step for the local Aoyagi chain composite `chainMap`. -/
private def chainMapStep (i : Fin (N + 1)) :
    ⦃m : ℕ⦄ → (i ≤ m) → ((hm : m < N + 1) → (V i →ₗ[K] V ⟨m, hm⟩)) →
      ((hm : m + 1 < N + 1) → (V i →ₗ[K] V ⟨m + 1, hm⟩)) :=
  fun {m} _ rec hm =>
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ hm⟩
    show V i →ₗ[K] V p.succ from
      (A p).comp (show V i →ₗ[K] V p.castSucc from rec p.castSucc.isLt)

/-- The ordered composite along an upward finite chain.

Here `V 0` is the product source/rightmost layer in Aoyagi's notation, and
`V (Fin.last N)` is the product target/leftmost layer.
-/
def chainMap (i j : Fin (N + 1)) (hij : i ≤ j) : V i →ₗ[K] V j :=
  Nat.leRec (motive := fun m _ => (hm : m < N + 1) → (V i →ₗ[K] V ⟨m, hm⟩))
    (fun _ => LinearMap.id) (chainMapStep V A i) hij j.isLt

/-- The empty chain composite is the identity. -/
theorem chainMap_self (i : Fin (N + 1)) : chainMap V A i i le_rfl = LinearMap.id := by
  unfold chainMap
  exact congrFun (Nat.leRec_self (motive := fun m _ => (hm : m < N + 1) →
    (V i →ₗ[K] V ⟨m, hm⟩)) (fun _ => LinearMap.id) (chainMapStep V A i)) i.isLt

/-- Extending the upper endpoint by one composes with the next edge on the left. -/
theorem chainMap_succ (i : Fin (N + 1)) (p : Fin N) (h : i ≤ p.castSucc) :
    chainMap V A i p.succ (h.trans (Fin.castSucc_le_succ p))
      = (A p).comp (chainMap V A i p.castSucc h) := by
  unfold chainMap
  exact congrFun (Nat.leRec_succ (h1 := Fin.val_fin_le.mpr h)
    (h2 := Fin.val_fin_le.mpr (h.trans (Fin.castSucc_le_succ p)))
    (refl := fun _ => LinearMap.id) (le_succ_of_le := chainMapStep V A i)) p.succ.isLt

/-- The chain composite splits at an intermediate vertex. -/
theorem chainMap_trans (i : Fin (N + 1)) {m j : Fin (N + 1)} (him : i ≤ m) (hmj : m ≤ j) :
    chainMap V A i j (him.trans hmj)
      = (chainMap V A m j hmj).comp (chainMap V A i m him) := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl : m = 0 := Fin.le_zero_iff.mp hmj
    obtain rfl : i = 0 := Fin.le_zero_iff.mp him
    rw [chainMap_self]
    rfl
  | succ p ih =>
    rcases eq_or_lt_of_le hmj with rfl | hlt
    · rw [chainMap_self, LinearMap.id_comp]
    · have hmp : m ≤ p.castSucc := by rw [Fin.le_castSucc_iff]; exact hlt
      have himp : i ≤ p.castSucc := him.trans hmp
      rw [chainMap_succ V A i p himp, chainMap_succ V A m p hmp, ih hmp,
        LinearMap.comp_assoc]

/-- The total chain map factors through any intermediate vertex. -/
theorem chainMap_zero_last_eq_suffix_comp_prefix (j : Fin (N + 1)) :
    chainMap V A 0 (Fin.last N) ((Fin.zero_le j).trans j.le_last)
      = (chainMap V A j (Fin.last N) j.le_last).comp
        (chainMap V A 0 j (Fin.zero_le j)) :=
  chainMap_trans V A 0 (Fin.zero_le j) j.le_last

/-- The composite over one edge is that edge. -/
theorem chainMap_edge (e : Fin N) (h : e.castSucc ≤ e.succ) :
    chainMap V A e.castSucc e.succ h = A e := by
  have hstep := chainMap_succ V A e.castSucc e le_rfl
  rw [chainMap_self V A e.castSucc, LinearMap.comp_id] at hstep
  exact hstep

/-- Image of the initial through-subspace at a later vertex of the chain. -/
def throughSubspace (U₀ : Submodule K (V 0)) (j : Fin (N + 1)) : Submodule K (V j) :=
  U₀.map (chainMap V A 0 j (Fin.zero_le j))

/-- At the initial vertex, the through-subspace is the chosen subspace. -/
theorem throughSubspace_zero (U₀ : Submodule K (V 0)) :
    throughSubspace V A U₀ 0 = U₀ := by
  simp [throughSubspace, chainMap_self]

/-- The through-subspace at the next vertex is the image of the current one by the edge map. -/
theorem throughSubspace_succ (U₀ : Submodule K (V 0)) (p : Fin N) :
    throughSubspace V A U₀ p.succ = (throughSubspace V A U₀ p.castSucc).map (A p) := by
  rw [throughSubspace, throughSubspace, chainMap_succ V A 0 p (Fin.zero_le p.castSucc),
    Submodule.map_comp]

/-- If the initial subspace avoids the kernel of a factored total map, its image avoids the
corresponding suffix kernel. -/
theorem disjoint_throughSubspace_ker_suffix_of_disjoint_ker_comp
    (U₀ : Submodule K (V 0)) (j : Fin (N + 1))
    (hU₀ : Disjoint U₀
      (LinearMap.ker ((chainMap V A j (Fin.last N) j.le_last).comp
        (chainMap V A 0 j (Fin.zero_le j))))) :
    Disjoint (throughSubspace V A U₀ j)
      (LinearMap.ker (chainMap V A j (Fin.last N) j.le_last)) := by
  simpa [throughSubspace] using
    disjoint_map_ker_of_disjoint_ker_comp (chainMap V A 0 j (Fin.zero_le j))
      (chainMap V A j (Fin.last N) j.le_last) U₀ hU₀

/-- If the initial subspace avoids the kernel of a factored total map, its image at any vertex has
the same `finrank`. -/
theorem finrank_throughSubspace_eq_of_disjoint_ker_comp
    (U₀ : Submodule K (V 0)) (j : Fin (N + 1))
    (hU₀ : Disjoint U₀
      (LinearMap.ker ((chainMap V A j (Fin.last N) j.le_last).comp
        (chainMap V A 0 j (Fin.zero_le j))))) :
    Module.finrank K (throughSubspace V A U₀ j) = Module.finrank K U₀ := by
  have hprefix : Disjoint U₀ (LinearMap.ker (chainMap V A 0 j (Fin.zero_le j))) :=
    disjoint_ker_of_disjoint_ker_comp (chainMap V A 0 j (Fin.zero_le j))
      (chainMap V A j (Fin.last N) j.le_last) U₀ hU₀
  simpa [throughSubspace] using
    finrank_map_eq_of_disjoint_ker (chainMap V A 0 j (Fin.zero_le j)) U₀ hprefix

/-- The edge map restricts to an isomorphism between adjacent through-subspaces. -/
def throughSubspaceEdgeEquiv (U₀ : Submodule K (V 0)) (p : Fin N)
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))))) :
    throughSubspace V A U₀ p.castSucc ≃ₗ[K] throughSubspace V A U₀ p.succ := by
  have hfactor : chainMap V A p.castSucc (Fin.last N) p.castSucc.le_last
      = (chainMap V A p.succ (Fin.last N) p.succ.le_last).comp (A p) := by
    rw [chainMap_trans V A p.castSucc (Fin.castSucc_le_succ p) p.succ.le_last,
      chainMap_edge V A p (Fin.castSucc_le_succ p)]
  have htotal_factor :
      chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))
        = (chainMap V A p.castSucc (Fin.last N) p.castSucc.le_last).comp
          (chainMap V A 0 p.castSucc (Fin.zero_le p.castSucc)) := by
    rw [chainMap_zero_last_eq_suffix_comp_prefix V A p.castSucc]
  have hcomp : Disjoint U₀
      (LinearMap.ker ((chainMap V A p.castSucc (Fin.last N) p.castSucc.le_last).comp
        (chainMap V A 0 p.castSucc (Fin.zero_le p.castSucc)))) := by
    simpa [← htotal_factor] using hU₀
  have hsuffix :
      Disjoint (throughSubspace V A U₀ p.castSucc)
        (LinearMap.ker (chainMap V A p.castSucc (Fin.last N) p.castSucc.le_last)) :=
    disjoint_throughSubspace_ker_suffix_of_disjoint_ker_comp V A U₀ p.castSucc hcomp
  have hcurrent :
      Disjoint (throughSubspace V A U₀ p.castSucc) (LinearMap.ker (A p)) := by
    have hcompEdge :
        Disjoint (throughSubspace V A U₀ p.castSucc)
          (LinearMap.ker ((chainMap V A p.succ (Fin.last N) p.succ.le_last).comp (A p))) := by
      simpa [← hfactor] using hsuffix
    exact disjoint_ker_of_disjoint_ker_comp (A p)
      (chainMap V A p.succ (Fin.last N) p.succ.le_last)
      (throughSubspace V A U₀ p.castSucc) hcompEdge
  exact (linearEquivMapOfDisjointKer (A p) (throughSubspace V A U₀ p.castSucc) hcurrent).trans
    (LinearEquiv.ofEq _ _ (throughSubspace_succ V A U₀ p).symm)

/-- The adjacent through-subspace equivalence is induced by the original edge map. -/
theorem throughSubspaceEdgeEquiv_apply (U₀ : Submodule K (V 0)) (p : Fin N)
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (x : throughSubspace V A U₀ p.castSucc) :
    (throughSubspaceEdgeEquiv V A U₀ p hU₀ x : V p.succ) = A p x := by
  simp [throughSubspaceEdgeEquiv]

/-- A complement to the total kernel yields through-subspaces at every vertex. -/
theorem exists_chain_throughSubspaces :
    ∃ U₀ : Submodule K (V 0), ∃ U : ∀ j : Fin (N + 1), Submodule K (V j),
      IsCompl U₀
          (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))) ∧
        (∀ j, U j = throughSubspace V A U₀ j) ∧
          U 0 = U₀ ∧
            (∀ p : Fin N, U p.succ = (U p.castSucc).map (A p)) ∧
              (∀ j, Disjoint (U j)
                (LinearMap.ker (chainMap V A j (Fin.last N) j.le_last))) ∧
                (∀ j, Module.finrank K (U j) =
                  Module.finrank K
                    (LinearMap.range
                      (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))))) ∧
                  U (Fin.last N) =
                    LinearMap.range
                      (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) := by
  let P : V 0 →ₗ[K] V (Fin.last N) :=
    chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))
  rcases exists_isCompl_ker_and_finrank_eq_range (P := P) with ⟨U₀, hU₀, hfinU₀⟩
  let U : ∀ j : Fin (N + 1), Submodule K (V j) := fun j ↦ throughSubspace V A U₀ j
  refine ⟨U₀, U, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hU₀
  · intro j
    rfl
  · exact throughSubspace_zero V A U₀
  · intro p
    exact throughSubspace_succ V A U₀ p
  · intro j
    have hfactor : chainMap V A 0 (Fin.last N) ((Fin.zero_le j).trans j.le_last)
        = (chainMap V A j (Fin.last N) j.le_last).comp
          (chainMap V A 0 j (Fin.zero_le j)) :=
      chainMap_zero_last_eq_suffix_comp_prefix V A j
    have htotal : Disjoint U₀
        (LinearMap.ker (chainMap V A 0 (Fin.last N) ((Fin.zero_le j).trans j.le_last))) := by
      simpa [P] using hU₀.disjoint
    have hcomp : Disjoint U₀
        (LinearMap.ker ((chainMap V A j (Fin.last N) j.le_last).comp
          (chainMap V A 0 j (Fin.zero_le j)))) := by
      simpa [← hfactor] using htotal
    simpa [U] using
      disjoint_throughSubspace_ker_suffix_of_disjoint_ker_comp V A U₀ j hcomp
  · intro j
    have hfactor : chainMap V A 0 (Fin.last N) ((Fin.zero_le j).trans j.le_last)
        = (chainMap V A j (Fin.last N) j.le_last).comp
          (chainMap V A 0 j (Fin.zero_le j)) :=
      chainMap_zero_last_eq_suffix_comp_prefix V A j
    have htotal : Disjoint U₀
        (LinearMap.ker (chainMap V A 0 (Fin.last N) ((Fin.zero_le j).trans j.le_last))) := by
      simpa [P] using hU₀.disjoint
    have hcomp : Disjoint U₀
        (LinearMap.ker ((chainMap V A j (Fin.last N) j.le_last).comp
          (chainMap V A 0 j (Fin.zero_le j)))) := by
      simpa [← hfactor] using htotal
    have hfinj :
        Module.finrank K (throughSubspace V A U₀ j) = Module.finrank K U₀ :=
      finrank_throughSubspace_eq_of_disjoint_ker_comp V A U₀ j hcomp
    simpa [U, P] using hfinj.trans hfinU₀
  · simpa [U, throughSubspace, P] using map_eq_range_of_isCompl_ker P hU₀

end FiniteChain

end Aoyagi
end DLN
end DLNFibre
