import DLNFibre.DLN.Aoyagi.FixedBasepointChart

/-!
# Source-facing boundary for Aoyagi product reduction

This module names the elementary/topological part of Aoyagi's product-reduction
theorem that has been proved so far.  The certificate records recursive
determinant charts, the deterministic endpoint block form, and residual-rank
conclusions only as pointwise implications from exact edge-rank hypotheses.

It deliberately does not assert exact-rank strata are open, does not transport
analytic ideals or normal-crossing certificates, and does not state an RLCT
consequence.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

section FixedBaseProductReductionBoundary

universe u v

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)] [∀ i, T2Space (W i)]
  [∀ i, Module K (W i)] [∀ i, ContinuousSMul K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

/-- The proved product-reduction boundary in endpoint bases fixed from a base chain `B`.

This is the source-facing package for the formalized elementary part of
Aoyagi's Theorem 3: recursive charts, endpoint block diagonalization, and
conditional residual-rank formulas. -/
structure PaperEndpointFixedBaseProductReductionCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ) (x : α) : Prop where
  detCharts :
    paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts W B U₀ hU₀ Cedge x
  blockDiagonal :
    paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal W B U₀ hU₀ Cedge x
  residualRankImplications :
    paperEndpointFixedBaseContinuousEdgesRecursiveResidualRankImplications
      W B U₀ hU₀ Cedge rEdge x

set_option linter.unusedSectionVars false in
/-- Recursive determinant charts pointwise produce the fixed-base product-reduction
certificate.  Exact edge ranks are still hypotheses of the residual-rank implications,
not neighborhood conclusions. -/
theorem paperEndpointFixedBaseProductReductionCertificate_of_recursiveDetCharts
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ) (x : α)
    (hcharts :
      paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts W B U₀ hU₀ Cedge x) :
    PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x := by
  classical
  let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  have hxE : ∀ p : Fin N,
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
          p
          (ChartLocalSuffixState.suffixState
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
            (Fin.last N) p.succ p.succ.le_last)) := by
    intro p
    simpa [paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts, E,
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges] using hcharts p
  refine
    { detCharts := hcharts
      blockDiagonal := ?_
      residualRankImplications := ?_ }
  · simpa [paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal, E] using
      paperEndpointFixedBaseChainMapMatrixOfReverseEdges_recursiveChart_blockDiagonal
        W B U₀ hU₀ E hxE
  · intro p hrank
    have hres :=
      rank_transformedEdge_fixedBaseReverseEdges_eq_range_sub
        W B U₀ hU₀ E p
        (ChartLocalSuffixState.suffixState
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
          (Fin.last N) p.succ p.succ.le_last)
        (hxE p)
    simpa [paperEndpointFixedBaseContinuousEdgesRecursiveResidualRankImplications,
      ChartLocalSuffixState.residualBlock, E, hrank] using hres

/-- Near a continuous reversed-edge family based at the fixed paper chain `B`, the
proved fixed-base product-reduction certificate holds. -/
theorem paperEndpointFixedBaseProductReductionCertificate_selfBase_mem_nhds
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    {x : α |
      PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x} ∈
      nhds x₀ := by
  have hraw :=
    paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_rankImp_mem_nhds
      W B U₀ hU₀ Cedge rEdge hCedge hbase
  exact Filter.mem_of_superset hraw (by
    intro x hx
    exact
      { detCharts := hx.1
        blockDiagonal := hx.2.1
        residualRankImplications := hx.2.2 })

/-- A local fixed-base package for the proved product-reduction boundary near a base
paper chain.  This pairs the basepoint adapted-coordinate certificate with the
neighborhood where the recursive fixed-base product-reduction certificate holds. -/
structure PaperEndpointFixedBaseProductReductionLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ) : Prop where
  basepoint : PaperEndpointBasepointCertificate W B U₀ hU₀
  mem_nhds :
    {x : α |
      PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x} ∈
      nhds x₀

/-- Any chosen total-kernel complement gives the local fixed-base product-reduction
certificate near a continuous edge family based at `B`. -/
theorem paperEndpointFixedBaseProductReductionLocalCertificate_of_isCompl
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    PaperEndpointFixedBaseProductReductionLocalCertificate W B U₀ hU₀ x₀ Cedge rEdge where
  basepoint := paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀
  mem_nhds :=
    paperEndpointFixedBaseProductReductionCertificate_selfBase_mem_nhds
      W B U₀ hU₀ Cedge rEdge hCedge hbase

/-- A continuous reversed-edge family based at `B` admits a local product-reduction
certificate after choosing endpoint bases from a total-kernel complement. -/
def PaperEndpointProductReductionLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ) : Prop :=
  ∃ U₀ : Submodule K (reverseVertex W 0),
    ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
      PaperEndpointFixedBaseProductReductionLocalCertificate W B U₀ hU₀ x₀ Cedge rEdge

/-- Finite-dimensional paper chains admit a local product-reduction certificate near any
continuous reversed-edge family based at the chain. -/
theorem exists_paperEndpointProductReductionLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    PaperEndpointProductReductionLocalCertificate W B x₀ Cedge rEdge := by
  rcases exists_paperEndpointBasepointCertificate W B with ⟨U₀, hU₀, _⟩
  exact ⟨U₀, hU₀,
    paperEndpointFixedBaseProductReductionLocalCertificate_of_isCompl
      W B U₀ hU₀ Cedge rEdge hCedge hbase⟩

end FixedBaseProductReductionBoundary

end Aoyagi
end DLN
end DLNFibre
