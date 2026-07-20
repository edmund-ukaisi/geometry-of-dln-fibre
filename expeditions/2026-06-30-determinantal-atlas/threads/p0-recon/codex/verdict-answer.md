1. **Mostly right, with one correction.**  
   The residue-field-rank bridge is detail-at-scale and already landed: [FibreRankBridge.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/det-atlas/lean/DLNFibre/Core/FibreRankBridge.lean:173) proves `P ∈ rankROpen ↔ rank over κ(P) = r`, using the expected `≤` minor-vanishing and `≥` nonzero pivot-minor arguments. De-DLN-ifying is mechanical if the general determinantal ring is set up with the universal matrix, `(r+1)`-minor quotient, and pivot minors.

   The correction: “putting topology on `Spec` is a category error” is too strong. `Spec` has a topology, and Mathlib’s `FiberBundle` is a topological notion requiring topological base/fiber/total-space data. The category error is treating that as the scheme-theoretic or affine-algebraic local-triviality statement. Mathlib’s `FiberBundle` file explicitly defines topological fiber bundles via local homeomorphic product trivializations, not algebraic/scheme trivializations. ([raw.githubusercontent.com](https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.29.0/Mathlib/Topology/FiberBundle/Basic.lean))

2. **I do not see a ready Mathlib v4.29 scheme-local-triviality class.**  
   A bespoke predicate is the right “bare bundle” target, but make it explicitly affine/Zariski/ring-level. A good target is closer to:

   `IsZariskiLocallyTrivialAffineProduct` = open cover by principal opens + per-chart named base map + `≃ₐ[BaseLoc] BaseLoc ⊗[k] Fibre` + overlap transition/cocycle.

   The current repo already has most of this shape: [FibreBundleHeadline.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/det-atlas/lean/DLNFibre/Core/FibreBundleHeadline.lean:144) packages rank-locus identity, cover, over-base trivializations, and flatness, while explicitly not claiming global `Flat π` / `FiberBundle` until target-side gluing is assembled.

3. **`AlgEquiv.trans_assoc` is a real API gap, but not a serious blocker.**  
   Mathlib v4.29’s `AlgEquiv` source has `trans`, `trans_apply`, `self_trans_symm`, and `symm_trans_self`, plus coercion to `RingEquiv`; it does not provide the associativity/refl lemmas in that namespace. ([raw.githubusercontent.com](https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.29.0/Mathlib/Algebra/Algebra/Equiv.lean))

   I would not route through `toRingEquiv` first unless it is immediately smooth. Add generic lemmas in a lightweight API file:

   ```lean
   @[simp] theorem AlgEquiv.trans_assoc ... :
     (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) := by
     ext x; rfl

   @[simp] theorem AlgEquiv.trans_refl (e : A ≃ₐ[R] B) :
     e.trans AlgEquiv.refl = e := by
     ext x; rfl

   @[simp] theorem AlgEquiv.refl_trans (e : A ≃ₐ[R] B) :
     (AlgEquiv.refl).trans e = e := by
     ext x; rfl
   ```

   Proving these generically avoids extensionality over the heavy double-localized target type. Then the target round-trip in [FibreTargetOverlap.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/det-atlas/lean/DLNFibre/Core/FibreTargetOverlap.lean:169) should be a structural cancellation proof. If it still times out, the next suspect is `@[reducible] targetChartLoc`, not the mathematics.

4. **Sharper kill-condition for “detail-at-scale.”**  
   The bridge stops being detail-at-scale only if the generalization requires something beyond residue fields plus field-level rank/minor API. Examples: rank over local rings instead of residue fields; scheme image/elimination to prove the rank bound is “baked in”; Fitting-ideal theory for arbitrary modules; or a non-affine/sheaf-level gluing theorem. If the setting remains “affine quotient by minors, evaluate universal matrix in κ(P), principal opens from pivot minors,” it is buildable library work, not a monument.