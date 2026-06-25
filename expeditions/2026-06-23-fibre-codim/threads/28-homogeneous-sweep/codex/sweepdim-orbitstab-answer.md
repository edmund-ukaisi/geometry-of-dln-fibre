**Verdict:** Step B is **not reachable** from the existing single-orbit Voigt/orbit-pullback machinery with only small lemmas. It needs a genuine relative/product/fibre-dimension input, or the equivalent exact-rank chart trivialization plus flatness/height additivity. The repo already reflects this: the sweep identity is landed, but the dimension consequence is explicitly not proved and is carried as a named residual. See [EndBaseChangeSweep.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:15) and the cited bundle-shift interface in [RlctPayoffGeneral.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoffGeneral.lean:66).

**Q1.**
(a) No: `Σ^r = H·F` is not a single orbit closure unless `F` itself is a point/homogeneous in a compatible way. It is the associated bundle `H ×^S F`, where `S = Stab_H(E)`, not an orbit of one point. The existing chain applies to `μ_M : G_d → Rep_d`, not to a family domain `H × F`.

(b) For `α : H × F → Σ^r`, the needed theorem is not just “orbit-stabilizer”. You need:
`dim image(α) = dim(H × F) - dim S`
and
`dim(H × F) = dim H + dim F`.
That means product/tensor dimension plus a fibre-dimension theorem, or an associated-bundle/local-triviality theorem. The engine’s `trdeg_add_eq` is only tower additivity; it does not give `trdeg(A ⊗ₖ B) = trdeg A + trdeg B`. The local grep confirms no tensor/product trdeg or product Krull-dimension theorem at this pin; the only `trdeg_add_eq` use is the Noether-normalization tower in [AffineNoetherRank.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:37).

(c) The catenary route also does not close from homogeneity alone. It gives the easy inclusion/codim bound and base dimension bricks, but the hard inequality is exactly the no-jump/generic-flatness/local-triviality point. The repo says this directly in [FibreCodim.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:16) and [FibreDimFibration.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:17). Homogeneity only transports codimension between rank-`r` fibres; it does not compute the common value.

**Q2.**
The smallest honest theorem is an affine locally-trivial fibration/associated-bundle dimension theorem specialized to this situation:

`mult⁻¹(Mat^{=r}) ≃loc Mat^{=r} × F_E`, hence  
`varietyDim Σ^r = r(d₀+d_N-r) + varietyDim F_E`.

In codim form this is exactly the existing `cited_bundle_shift`:
`codimRepCanonical (fibre d B) = codimRepCanonical (productRankLocusLE d r) + δ`.

If building it, do **not** start with a general orbit-stabilizer theorem. The best build route is explicit exact-rank pivot charts, the Schur/endpoint normalization trivialization
`Rt ≃ Rb ⊗ₖ F_E`, then flatness and going-down. The API is present, but the chart object/trivializing `AlgEquiv` is absent; see [ChartFlatnessProbe.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:22). Rough cost: **8-12 modules**. A general tensor/Krull product-dimension theorem for reducible f.g. algebras would be at least comparable, likely **10-18 modules**, and still would not by itself handle the `Stab` quotient/image theorem.

Step-C closure/density is downstream-useful, but not the crux. It cannot replace the fibre-dimension theorem.

**Q3.**
Final adjudication: **Mathlib-absent / engine-absent.** Step B should remain a named Cited residual unless you are committing to the exact-rank chart-trivialization build. The biggest formalization risk is an off-by-`dim Stab_H(E)` mistake: treating `H × F → Σ^r` as generically finite would give `dim H + dim F`, which is wrong. A second risk is pretending `O(F)` is a domain/trdeg object; `F` can be reducible, so the theorem must be componentwise/max-dimension or height-based.