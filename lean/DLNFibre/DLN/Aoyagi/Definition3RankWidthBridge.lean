import DLNFibre.DLN.Aoyagi.Definition3Bridge
import DLNFibre.DLN.Aoyagi.ProductReductionBoundary

/-!
# Source-range rank-width bridge for Aoyagi Definition 3

This file connects the A2 product-rank boundary to the source-range rank-width
hypothesis consumed by the Definition 3 and final Theorem 2 sockets.

The bridge is elementary linear algebra: the total product factors through
each layer, so its rank is bounded by each layer dimension.  It does not
construct selected cutpoints, prove Definition 3's selection inequalities,
prove exact-rank openness, construct charts, prove finite exponent formulas,
or invoke the normal-crossing extraction theorem.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

universe u v

section RankWidth

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module K (W i)]
  [∀ i, ContinuousSMul K (W i)] [∀ i, FiniteDimensional K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

omit [CompleteSpace K] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The rank of Aoyagi's total product is bounded by every source layer
dimension.

The proof uses the through-subspace construction for the reversed chain:
a subspace of dimension `rank(product)` passes through every layer, hence has
dimension at most that layer's dimension. -/
theorem paperTotalMap_rank_le_layer_finrank
    {r : ℕ}
    (hrank : Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (k : Fin (N + 1)) :
    r ≤ Module.finrank K (W k) := by
  rcases exists_chain_throughSubspaces (K := K)
      (V := reverseVertex W) (A := reverseEdge W B) with
    ⟨U₀, U, hcompl, hU, hUzero, hUsucc, hdisj, hfin, hlast⟩
  have hrank_rev :
      Module.finrank K
          (LinearMap.range
            (chainMap (reverseVertex W) (reverseEdge W B) 0 (Fin.last N)
              (Fin.zero_le (Fin.last N)))) = r := by
    rw [chainMap_reverse_eq_paper]
    simpa [paperTotalMap] using hrank
  have hfin_k :
      Module.finrank K (U k.rev) = r :=
    (hfin k.rev).trans hrank_rev
  have hle :
      Module.finrank K (U k.rev) ≤
        Module.finrank K (reverseVertex W k.rev) :=
    Submodule.finrank_le _
  have hrev :
      Module.finrank K (reverseVertex W k.rev) =
        Module.finrank K (W k) := by
    simpa [reverseVertex] using
      congrArg (fun j : Fin (N + 1) ↦ Module.finrank K (W j))
        (Fin.rev_rev k)
  exact hfin_k ▸ hrev ▸ hle

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- Membership in the source-rank stratum gives the source-range rank-width
hypothesis used by Definition 3, after an explicit identification of Aoyagi's
displayed width function `H` with the layer finranks.

The source layer range is `s = 1, ..., N+1`; the theorem intentionally keeps
the dimension convention as a hypothesis. -/
theorem paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α} {H : ℕ → ℕ}
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    ∀ s : ℕ, 1 ≤ s → s ≤ N + 1 → r ≤ H s := by
  intro s hs1 hsN
  let k : Fin (N + 1) := ⟨s - 1, by omega⟩
  have hk : k.val + 1 = s := by
    dsimp [k]
    omega
  have hle :
      r ≤ Module.finrank K (W k) :=
    paperTotalMap_rank_le_layer_finrank W B hx.1 k
  simpa [hk] using hle.trans_eq (hH k).symm

namespace AoyagiDefinition3SourceData

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- Definition 3 source data plus an A2 source-rank stratum membership produce
the selected reduced-width family and ceiling datum, using the source-rank
stratum to discharge the source-range rank-width hypothesis.

Selected cutpoints and the Definition 3 source-data inequalities remain
supplied; this theorem only removes the separate `∀ s, r ≤ H s` input. -/
theorem exists_selectedReducedWidthCeilData_of_sourceRankStratum
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    {ell : ℕ} {H : ℕ → ℕ} {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData N ell H r C)
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      m = aoyagiSelectedReducedWidths H r C ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) :=
  S.exists_selectedReducedWidthCeilData_of_rankWidth
    (paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH)

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- All-source selected Definition 3 data plus an A2 source-rank stratum
membership produce the selected reduced-width family and ceiling datum.

The source-rank stratum is used only to discharge the source-range rank-width
hypothesis for the all-source ceiling-data package.  The strict all-source
selected inequality remains an explicit input. -/
theorem exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_sourceRankStratum
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α} {H : ℕ → ℕ}
    (hN : 0 < N)
    (hstrict :
      ∀ s : ℕ, 1 ≤ s → s ≤ N + 1 →
        (N : ℤ) * aoyagiReducedWidthInt H r s <
          ∑ j : Fin (N + 1), aoyagiReducedWidthInt H r (j.val + 1))
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    ∃ (C : AoyagiSelectedCutpoints N)
        (m : Fin (N + 1) → ℤ)
        (data : AoyagiDefinition3CeilData N m),
      (∀ j : Fin (N + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData N N H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      (∀ j : Fin (N + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (N + 1), 0 ≤ m j) ∧
      (∀ i : Fin (N + 1),
        (N : ℤ) * m i < ∑ j : Fin (N + 1), m j) ∧
      (∀ i : Fin (N + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat N m i) :=
  exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_rankWidth
    (L := N) (H := H) (r := r) hN hstrict
    (paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH)

end AoyagiDefinition3SourceData

end RankWidth

end Aoyagi
end DLN
end DLNFibre
