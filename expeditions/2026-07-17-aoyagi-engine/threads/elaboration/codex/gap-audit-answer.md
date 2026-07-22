## 1. CLAIM 1 verdict: PARTIAL

**OBSERVED:** `Deg1SupportedSlot` carries support-divisibility plus per-layer degree **≤ 1** from `supportLayerOf`; layers below that threshold are unconstrained, not specifically bounded by degree 2. Thus it encodes a prepared multi-affine residual, not literally “one factor in every active layer.”

**INFERENCE:** That prepared multi-affine/support-divisible form is the right invariant suggested by the Schur mechanism.

- **1a: TRUE.** **OBSERVED:** free paths contain unrestricted coordinate data, and the preservation leaves explicitly assume the carried `FoldStepInvAt` and `ShearGrades`. Arbitrary shears can destroy the grading.
- **1b: FALSE for the current files.** **OBSERVED:** [`IsRealBranch`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean:771) explicitly ignores `shearφ`; yet `foldResid` depends on it. The preservation theorems also remain `sorry`.
- **INFERENCE:** A strengthened real-branch predicate pinning the canonical shear and corrected center could make the invariant derivable by induction, but that result is not presently established. A layer-preserving/canonical flatten is also required; arbitrary linear coordinate mixing need not preserve layer degrees.

## 2. CLAIM 2 verdict: PARTIAL — a real boost does not descend

**OBSERVED:** Case11 keeps `cleared` unchanged, uses identity shear, and at `δ=1`, `foldResid` replaces only the pivot coordinate by `1` through `blockBlowupCoordQuot`; all other coordinates remain unchanged.

**INFERENCE:** When the pivot is the reused exceptional \(u_{s,k}\), this removes the old \(u\)-factor while retaining the current-layer factor. Hence the residual stays at layer \(S\), matching `supportAt(S,0)`. A free current-layer pivot can instead remove that layer’s factor.

The qualification is that pivot-pinning alone is insufficient: this conclusion also needs the cross-layer invariant and the correct boost center. The current canonical center does not provide that center.

## 3. CLAIM 3 verdict: DEFECT

**OBSERVED:** [`canonPivotOf`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean:741) uses the reused divisor’s birth corner:

> `let bc := s.divBirthCoord ...`  
> `cornerToFlat d bc.1 bc.2`

**OBSERVED:** [`canonCenterOf`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean:757) requires:

> `(q.1.1 : ℕ) = s.layer`

and contains only the current-layer residual block.

**INFERENCE:** A reused divisor was born either in an earlier layer, or earlier in the current layer with birth index `< cleared`; either way its birth corner fails the center filter. Thus `pivot ∉ center`, contradicting `TreeEdge.hpivot`.

The correct case-1 center is the reused birth-corner coordinate **union the run-length-sized current-layer block**, as in the template—not merely the full current residual block plus an afterthought pivot. The existing leaf hypothesis `center ⊆ blockCoords currentLayer` is consequently also wrong for boosts.

Strict nuance: raw `TreePath.IsRealBranch` alone remains satisfiable because it does not contain `hpivot`; what is impossible is a canonical boost represented by a `TreeEdge` and then extended into such a branch.

## 4. DESIGN: C

Choose **C**, after repairing it. **INFERENCE:** A correct construction-level predicate should pin the case-dependent center, pivot, child state, and canonical shear; then multi-affinity can be proved once by induction over genuine branches. Under P, the corrected boost hypotheses would have to reconstruct the cross-layer center and canonical transition case-by-case, effectively duplicating the oracle while retaining severance axes. As written, however, C is not ready: fix `canonCenterOf`, pin `shearφ`, and prove the canonical `hpivot` and grading lemmas first.