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
/-- The exact edge-rank stratum for a nearby paper-order edge family.  This is a
restriction set, not an asserted neighborhood. -/
def paperEndpointFixedBaseEdgeRankStratum
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ) : Set α :=
  {x | ∀ p : Fin N,
    Module.finrank K (LinearMap.range
      (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) =
        rEdge p}

set_option linter.unusedSectionVars false in
/-- The transformed-edge ranks used by the recursive Schur-residual construction
are exactly the source edge-rank stratum.  The accumulated left multiplier is
block-unitriangular, so it does not change matrix rank.  This is only a
rank-predicate bridge; it does not assert that exact-rank strata are open. -/
theorem paperEndpointFixedBase_transformedEdgeRanks_iff_edgeRankStratum
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ) (x : α) :
    (let E : ∀ p : Fin N,
        reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
        fun p ↦
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
     let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
     ∀ p : Fin N,
       (ChartLocalSuffixState.transformedEdge EMat p
          (ChartLocalSuffixState.suffixState EMat
            (Fin.last N) p.succ p.succ.le_last)).rank = rEdge p) ↔
      x ∈ paperEndpointFixedBaseEdgeRankStratum W Cedge rEdge := by
  classical
  let E : ∀ p : Fin N,
      reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦
      (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
  change
    (∀ p : Fin N,
      (ChartLocalSuffixState.transformedEdge EMat p
        (ChartLocalSuffixState.suffixState EMat
          (Fin.last N) p.succ p.succ.le_last)).rank = rEdge p) ↔
      x ∈ paperEndpointFixedBaseEdgeRankStratum W Cedge rEdge
  have hsame : ∀ p : Fin N,
      (ChartLocalSuffixState.transformedEdge EMat p
        (ChartLocalSuffixState.suffixState EMat
          (Fin.last N) p.succ p.succ.le_last)).rank =
        (EMat p).rank := by
    intro p
    let S :=
      ChartLocalSuffixState.suffixState EMat
        (Fin.last N) p.succ p.succ.le_last
    let A : Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.succ) K :=
      fromBlocks (1 : Matrix (Fin (Module.finrank K U₀))
          (Fin (Module.finrank K U₀)) K) S.B 0
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.succ) K)
    have hA : IsUnit A.det := by
      exact (Matrix.isUnit_iff_isUnit_det (A := A)).mp
        ((Matrix.isUnit_fromBlocks_zero₂₁).2 ⟨isUnit_one, isUnit_one⟩)
    simp [ChartLocalSuffixState.transformedEdge, S, A,
      Matrix.rank_mul_eq_right_of_isUnit_det A (EMat p) hA]
  constructor
  · intro h p
    have hraw : (EMat p).rank = rEdge p := (hsame p).symm.trans (h p)
    have hrange :=
      rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range
        W B U₀ hU₀ E p
    exact (by
      simpa [E] using hrange.symm.trans hraw)
  · intro h p
    have hrange :=
      rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range
        W B U₀ hU₀ E p
    have hsrc :
        Module.finrank K (LinearMap.range (E p)) = rEdge p := by
      simpa [E] using h p
    exact (hsame p).trans (hrange.trans hsrc)

/-- Aoyagi's source-shaped rank stratum: the fixed base product has rank `r`, the
nearby layer edges have ranks `rEdge`, and the source inequalities `r ≤ rEdge p`
are recorded.  This is a restriction set, not an asserted neighborhood. -/
def paperEndpointFixedBaseSourceRankStratum
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) : Set α :=
  {x |
    Module.finrank K (LinearMap.range (paperTotalMap W B)) = r ∧
    x ∈ paperEndpointFixedBaseEdgeRankStratum W Cedge rEdge ∧
    ∀ p : Fin N, r ≤ rEdge p}

/-- The base parameter lies in the source-shaped rank stratum once the source
rank equalities and inequalities are supplied explicitly.  This proves
basepoint membership only; it is not exact-rank openness. -/
theorem paperEndpointFixedBaseSourceRankStratum_selfBase_mem
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} {x₀ : α}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank K (LinearMap.range (reverseEdge W B p)) = rEdge p)
    (hle : ∀ p : Fin N, r ≤ rEdge p) :
    x₀ ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge := by
  refine ⟨hprod, ?_, hle⟩
  intro p
  have hpCLM :
      Cedge x₀ p = LinearMap.toContinuousLinearMap (reverseEdge W B p) :=
    congrFun hbase p
  have hp :
      (Cedge x₀ p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ) =
        reverseEdge W B p := by
    simpa using
      congrArg
        (fun f : reverseVertex W p.castSucc →L[K] reverseVertex W p.succ ↦
          (f : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))
        hpCLM
  rw [hp]
  exact hedge p

/-- Residual-rank equalities after restricting the product-reduction certificate to
the exact edge-rank stratum. -/
def paperEndpointFixedBaseContinuousEdgesRecursiveResidualRanks
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ) (x : α) : Prop :=
  let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  ∀ p : Fin N,
    (ChartLocalSuffixState.residualBlock
      (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
      (Fin.last N) p p.succ.le_last).rank =
      rEdge p - Module.finrank K U₀

/-- Source-shaped endpoint conclusion for the fixed-base product-reduction
boundary: triangular endpoint multipliers expose the transformed residual product,
and the visited residual blocks have Aoyagi's source-stratum ranks. -/
structure PaperEndpointFixedBaseTriangularResidualProductSourceRanks
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) (x : α) : Prop where
  triangularResidualProduct :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    ∃ F2 : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K,
      ∃ F3 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (Fin (Module.finrank K U₀)) K,
        ∃ Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K,
          IsUnit
              (fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                0 F3
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K)).det ∧
            IsUnit
              (fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                F2 0
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0)
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0) K)).det ∧
            IsUnit Ctop.det ∧
            fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                0 F3
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K) *
              paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E *
              fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                F2 0
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0)
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
              fromBlocks Ctop 0 0
                (ChartLocalSuffixState.residualProduct EMat (Fin.last N) 0
                  (Fin.zero_le (Fin.last N)))
  sourceResidualRanks :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    ∀ p : Fin N,
      (ChartLocalSuffixState.residualBlock EMat (Fin.last N) p p.succ.le_last).rank =
        rEdge p - r

/-- The product-reduction certificate after restricting to the exact edge-rank
stratum.  It deliberately records stratum membership instead of claiming exact
rank is open. -/
structure PaperEndpointFixedBaseProductReductionRankStratumCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ) (x : α) : Prop where
  certificate : PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x
  edgeRanks : x ∈ paperEndpointFixedBaseEdgeRankStratum W Cedge rEdge
  residualRanks :
    paperEndpointFixedBaseContinuousEdgesRecursiveResidualRanks W B U₀ hU₀ Cedge rEdge x

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

namespace PaperEndpointFixedBaseProductReductionCertificate

set_option linter.unusedSectionVars false in
/-- On the exact edge-rank stratum, the certificate's residual-rank implications
become residual-rank equalities. -/
theorem residualRanks_of_edgeRankStratum
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {rEdge : Fin N → ℕ} {x : α}
    (cert : PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x)
    (hrank : x ∈ paperEndpointFixedBaseEdgeRankStratum W Cedge rEdge) :
    paperEndpointFixedBaseContinuousEdgesRecursiveResidualRanks W B U₀ hU₀ Cedge rEdge x := by
  intro p
  exact cert.residualRankImplications p (hrank p)

set_option linter.unusedSectionVars false in
/-- Package the fixed-base certificate together with exact edge ranks, deriving the
residual-rank equalities. -/
theorem rankStratumCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {rEdge : Fin N → ℕ} {x : α}
    (cert : PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x)
    (hrank : x ∈ paperEndpointFixedBaseEdgeRankStratum W Cedge rEdge) :
    PaperEndpointFixedBaseProductReductionRankStratumCertificate W B U₀ hU₀ Cedge rEdge x where
  certificate := cert
  edgeRanks := hrank
  residualRanks :=
    PaperEndpointFixedBaseProductReductionCertificate.residualRanks_of_edgeRankStratum
      (W := W) (B := B) cert hrank

set_option linter.unusedSectionVars false in
/-- On Aoyagi's source-shaped rank stratum, the visited residual block has rank
`rEdge p - r`, where `r` is the fixed base product rank. -/
theorem residualBlock_rank_eq_sourceRankSubProductRank
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (base : PaperEndpointBasepointCertificate W B U₀ hU₀)
    (cert : PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x)
    (hrank : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (p : Fin N) :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    (ChartLocalSuffixState.residualBlock
      (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
      (Fin.last N) p p.succ.le_last).rank =
      rEdge p - r := by
  dsimp
  have hres := cert.residualRankImplications p (hrank.2.1 p)
  have hU : Module.finrank K U₀ = r := base.finrank_eq_range.trans hrank.1
  simpa [hU] using hres

end PaperEndpointFixedBaseProductReductionCertificate

set_option linter.unusedSectionVars false in
/-- The fixed-base product-reduction certificate exposes Aoyagi's triangular
left and right multipliers. -/
theorem PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {rEdge : Fin N → ℕ} {x : α}
    (cert : PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x) :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    ∃ F2 : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K,
      ∃ F3 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (Fin (Module.finrank K U₀)) K,
        ∃ Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K,
          ∃ D : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0) K,
            IsUnit
                (fromBlocks
                  (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                  0 F3
                  (1 : Matrix
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K)).det ∧
              IsUnit
                (fromBlocks
                  (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                  F2 0
                  (1 : Matrix
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ 0)
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ 0) K)).det ∧
              IsUnit Ctop.det ∧
              fromBlocks
                  (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                  0 F3
                  (1 : Matrix
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K) *
                paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E *
                fromBlocks
                  (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                  F2 0
                  (1 : Matrix
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ 0)
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
                fromBlocks Ctop 0 0 D := by
  classical
  dsimp
  let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
  let S := ChartLocalSuffixState.suffixState EMat
    (Fin.last N) 0 (Fin.zero_le (Fin.last N))
  rcases ChartLocalSuffixState.suffixState_L_eq_lowerUnitriangular
      (K := K) EMat (i := 0) (j := Fin.last N) (Fin.zero_le (Fin.last N)) with
    ⟨F3, hF3⟩
  have hblock :
      IsUnit S.L.det ∧ IsUnit S.Ctop.det ∧
        S.L * paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E *
            fromBlocks
              (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
              (-S.B) 0
              (1 : Matrix
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0)
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
          fromBlocks S.Ctop 0 0 S.D := by
    simpa [paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal, E, EMat, S] using
      cert.blockDiagonal
  rcases hblock with ⟨_, hCtop, hdiag⟩
  have hLeft : IsUnit
      (fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        0 F3
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K)).det := by
    exact (Matrix.isUnit_iff_isUnit_det
        (A := fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          0 F3
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K))).mp
      ((Matrix.isUnit_fromBlocks_zero₁₂).2 ⟨isUnit_one, isUnit_one⟩)
  have hRight : IsUnit
      (fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        (-S.B) 0
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0) K)).det := by
    exact (Matrix.isUnit_iff_isUnit_det
        (A := fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          (-S.B) 0
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0) K))).mp
      ((Matrix.isUnit_fromBlocks_zero₂₁).2 ⟨isUnit_one, isUnit_one⟩)
  refine ⟨-S.B, F3, S.Ctop, S.D, hLeft, hRight, hCtop, ?_⟩
  simpa [E, S, hF3] using hdiag

namespace PaperEndpointFixedBaseProductReductionCertificate

set_option linter.unusedSectionVars false in
/-- The fixed-base product-reduction certificate exposes Aoyagi's triangular
left and right multipliers with the deterministic lower-right residual product
named explicitly. -/
theorem exists_triangularBlockDiagonal_residualProduct
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {rEdge : Fin N → ℕ} {x : α}
    (cert : PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x) :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    ∃ F2 : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K,
      ∃ F3 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (Fin (Module.finrank K U₀)) K,
        ∃ Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K,
          IsUnit
              (fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                0 F3
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K)).det ∧
            IsUnit
              (fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                F2 0
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0)
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0) K)).det ∧
            IsUnit Ctop.det ∧
            fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                0 F3
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K) *
              paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E *
              fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                F2 0
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0)
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
              fromBlocks Ctop 0 0
                (ChartLocalSuffixState.residualProduct EMat (Fin.last N) 0
                  (Fin.zero_le (Fin.last N))) := by
  classical
  dsimp
  let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
  let S := ChartLocalSuffixState.suffixState EMat
    (Fin.last N) 0 (Fin.zero_le (Fin.last N))
  rcases ChartLocalSuffixState.suffixState_L_eq_lowerUnitriangular
      (K := K) EMat (i := 0) (j := Fin.last N) (Fin.zero_le (Fin.last N)) with
    ⟨F3, hF3⟩
  have hblock :
      IsUnit S.L.det ∧ IsUnit S.Ctop.det ∧
        S.L * paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E *
            fromBlocks
              (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
              (-S.B) 0
              (1 : Matrix
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0)
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
          fromBlocks S.Ctop 0 0 S.D := by
    simpa [paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal, E, EMat, S] using
      cert.blockDiagonal
  rcases hblock with ⟨_, hCtop, hdiag⟩
  have hLeft : IsUnit
      (fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        0 F3
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K)).det := by
    exact (Matrix.isUnit_iff_isUnit_det
        (A := fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          0 F3
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K))).mp
      ((Matrix.isUnit_fromBlocks_zero₁₂).2 ⟨isUnit_one, isUnit_one⟩)
  have hRight : IsUnit
      (fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        (-S.B) 0
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0) K)).det := by
    exact (Matrix.isUnit_iff_isUnit_det
        (A := fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          (-S.B) 0
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0) K))).mp
      ((Matrix.isUnit_fromBlocks_zero₂₁).2 ⟨isUnit_one, isUnit_one⟩)
  have hD : S.D =
      ChartLocalSuffixState.residualProduct EMat (Fin.last N) 0
        (Fin.zero_le (Fin.last N)) := by
    simpa [S] using
      ChartLocalSuffixState.suffixState_D_eq_residualProduct
        (K := K) EMat (Fin.zero_le (Fin.last N))
  refine ⟨-S.B, F3, S.Ctop, hLeft, hRight, hCtop, ?_⟩
  calc
    fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        0 F3
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K) *
      paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E *
      fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        (-S.B) 0
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
        fromBlocks S.Ctop 0 0 S.D := by
          simpa [E, S, hF3] using hdiag
    _ = fromBlocks S.Ctop 0 0
        (ChartLocalSuffixState.residualProduct EMat (Fin.last N) 0
          (Fin.zero_le (Fin.last N))) := by
          rw [hD]

set_option linter.unusedSectionVars false in
/-- On Aoyagi's source-shaped rank stratum, the fixed-base endpoint certificate
packages both the triangular residual-product form and the source residual-rank
formulas. -/
theorem exists_triangularBlockDiagonal_residualProduct_sourceRanks
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (base : PaperEndpointBasepointCertificate W B U₀ hU₀)
    (cert : PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x)
    (hsrc : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge) :
    PaperEndpointFixedBaseTriangularResidualProductSourceRanks
      W B U₀ hU₀ Cedge r rEdge x where
  triangularResidualProduct :=
    PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct
      (W := W) (B := B) cert
  sourceResidualRanks := by
    dsimp
    intro p
    simpa using
      residualBlock_rank_eq_sourceRankSubProductRank
        (W := W) (B := B) base cert hsrc p

end PaperEndpointFixedBaseProductReductionCertificate

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

/-- Near a continuous edge family based at the fixed paper chain `B`, the
rank-refined product-reduction certificate holds relative to the exact edge-rank
stratum.  This does not assert that the stratum itself is open. -/
theorem paperEndpointFixedBaseProductReductionRankStratumCertificate_selfBase_mem_nhdsWithin
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
      PaperEndpointFixedBaseProductReductionRankStratumCertificate
        W B U₀ hU₀ Cedge rEdge x} ∈
      nhdsWithin x₀ (paperEndpointFixedBaseEdgeRankStratum W Cedge rEdge) := by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine
    ⟨{x : α |
      PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x},
      paperEndpointFixedBaseProductReductionCertificate_selfBase_mem_nhds
        W B U₀ hU₀ Cedge rEdge hCedge hbase,
      ?_⟩
  intro x hx
  exact
    PaperEndpointFixedBaseProductReductionCertificate.rankStratumCertificate
      (W := W) (B := B) hx.1 hx.2

/-- Near a continuous edge family based at the fixed paper chain `B`, the
rank-refined product-reduction certificate holds relative to Aoyagi's
source-shaped rank stratum.  This does not assert exact-rank openness. -/
theorem paperEndpointFixedBaseProductReductionRankStratumCertificate_selfBase_mem_nhdsWithin_source
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    {x : α |
      PaperEndpointFixedBaseProductReductionRankStratumCertificate
        W B U₀ hU₀ Cedge rEdge x} ∈
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge) := by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine
    ⟨{x : α |
      PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x},
      paperEndpointFixedBaseProductReductionCertificate_selfBase_mem_nhds
        W B U₀ hU₀ Cedge rEdge hCedge hbase,
      ?_⟩
  intro x hx
  exact
    PaperEndpointFixedBaseProductReductionCertificate.rankStratumCertificate
      (W := W) (B := B) hx.1 hx.2.2.1

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- Near a continuous edge family based at `B`, the endpoint triangular
residual-product/source-rank conclusion holds relative to Aoyagi's source-shaped
rank stratum.  This is a relative statement, not exact-rank openness. -/
theorem paperEndpointFixedBaseTriangularSourceRanks_selfBase_mem_nhdsWithin_source
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    {x : α |
      PaperEndpointFixedBaseTriangularResidualProductSourceRanks
        W B U₀ hU₀ Cedge r rEdge x} ∈
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge) := by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine
    ⟨{x : α |
      PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x},
      paperEndpointFixedBaseProductReductionCertificate_selfBase_mem_nhds
        W B U₀ hU₀ Cedge rEdge hCedge hbase,
      ?_⟩
  intro x hx
  exact
    PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct_sourceRanks
      (W := W) (B := B)
      (base := paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀)
      (cert := hx.1)
      (hsrc := hx.2)

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

/-- A local fixed-base package for the product-reduction boundary restricted to the
exact edge-rank stratum. -/
structure PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ) : Prop where
  basepoint : PaperEndpointBasepointCertificate W B U₀ hU₀
  mem_nhdsWithin :
    {x : α |
      PaperEndpointFixedBaseProductReductionRankStratumCertificate
        W B U₀ hU₀ Cedge rEdge x} ∈
      nhdsWithin x₀ (paperEndpointFixedBaseEdgeRankStratum W Cedge rEdge)

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

/-- Any chosen total-kernel complement gives the local rank-stratum product-reduction
certificate near a continuous edge family based at `B`. -/
theorem paperEndpointFixedBaseProductReductionRankStratumLocalCertificate_of_isCompl
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate
      W B U₀ hU₀ x₀ Cedge rEdge where
  basepoint := paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀
  mem_nhdsWithin :=
    paperEndpointFixedBaseProductReductionRankStratumCertificate_selfBase_mem_nhdsWithin
      W B U₀ hU₀ Cedge rEdge hCedge hbase

namespace PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate

set_option linter.unusedSectionVars false in
/-- The rank-stratum local certificate also gives the same rank-refined
certificate relative to Aoyagi's source-shaped rank stratum. -/
theorem mem_nhdsWithin_source
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {rEdge : Fin N → ℕ}
    (certLocal :
      PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate
        W B U₀ hU₀ x₀ Cedge rEdge)
    (r : ℕ) :
    {x : α |
      PaperEndpointFixedBaseProductReductionRankStratumCertificate
        W B U₀ hU₀ Cedge rEdge x} ∈
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge) := by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  rcases (mem_nhdsWithin_iff_exists_mem_nhds_inter.mp certLocal.mem_nhdsWithin) with
    ⟨u, hu, hsubset⟩
  refine ⟨u, hu, ?_⟩
  intro x hx
  exact hsubset ⟨hx.1, hx.2.2.1⟩

end PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate

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

/-- A continuous reversed-edge family based at `B` admits a local product-reduction
certificate relative to the exact edge-rank stratum, after choosing endpoint bases
from a total-kernel complement. -/
def PaperEndpointProductReductionRankStratumLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ) : Prop :=
  ∃ U₀ : Submodule K (reverseVertex W 0),
    ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
      PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate
        W B U₀ hU₀ x₀ Cedge rEdge

/-- A continuous reversed-edge family based at `B` admits a local endpoint
triangular residual-product/source-rank package relative to Aoyagi's source rank
stratum, after choosing endpoint bases from a total-kernel complement. -/
def PaperEndpointTriangularSourceRanksLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) : Prop :=
  ∃ U₀ : Submodule K (reverseVertex W 0),
    ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
      {x : α |
        PaperEndpointFixedBaseTriangularResidualProductSourceRanks
          W B U₀ hU₀ Cedge r rEdge x} ∈
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)

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

/-- Finite-dimensional paper chains admit a local product-reduction certificate,
relative to the exact edge-rank stratum, near any continuous reversed-edge family
based at the chain. -/
theorem exists_paperEndpointProductReductionRankStratumLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    PaperEndpointProductReductionRankStratumLocalCertificate W B x₀ Cedge rEdge := by
  rcases exists_paperEndpointBasepointCertificate W B with ⟨U₀, hU₀, _⟩
  exact ⟨U₀, hU₀,
    paperEndpointFixedBaseProductReductionRankStratumLocalCertificate_of_isCompl
      W B U₀ hU₀ Cedge rEdge hCedge hbase⟩

/-- Finite-dimensional paper chains admit a local endpoint triangular
residual-product/source-rank package, relative to Aoyagi's source rank stratum,
near any continuous reversed-edge family based at the chain. -/
theorem exists_paperEndpointTriangularSourceRanksLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    PaperEndpointTriangularSourceRanksLocalCertificate W B x₀ Cedge r rEdge := by
  rcases exists_paperEndpointBasepointCertificate W B with ⟨U₀, hU₀, _⟩
  exact ⟨U₀, hU₀,
    paperEndpointFixedBaseTriangularSourceRanks_selfBase_mem_nhdsWithin_source
      W B U₀ hU₀ Cedge r rEdge hCedge hbase⟩

end FixedBaseProductReductionBoundary

end Aoyagi
end DLN
end DLNFibre
