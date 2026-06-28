**1. The Fork**

Rank: **A first, B second**.

**A/FUSED** is the honest generalization of your only nontrivial K-core instance. From your summary, `phi3333` is not a clean fold, and its determinant proof already depends on the fused `Frame3333` Jacobian. So I would make the general chart `Q_M ∘ Frame_M ∘ Kparam_M`, with the determinant theorem for `Frame_M` as the main reusable object.

Biggest A risk: proving the general `DFrame_M` block-triangular determinant without relying on Fin-literal structure.

**B/FOLD** is better only if you first prove a small, explicit radial-extraction theorem for `3333`. Without that, B is betting that the banked factor API describes a chart you do not currently have.

Biggest B risk: the “free determinant” is illusory if the hard proof becomes `fusedFrame = cleanFoldFrame` through opaque `chartIdxEquiv` transports.

**2. The Radial-Fusion Question**

From your summary alone: **not decidable**. The factor `|z0|^5` strongly suggests the radial contribution may be separable at determinant level, but map-level separability is stronger.

ASSUMPTION: if every occurrence of `z0` in `Frame3333` is either the pivot itself, e.g. `z0 + bilinear`, or appears only as `z0 * y` for coordinates `y` in one radial-active set, then the fusion is probably incidental packaging. Then define `radial` to replace those `y` by `z0*y`, and make `Frame'` read the already-scaled variables.

You must verify: no coordinate appears sometimes scaled by `z0` and sometimes unscaled in a way that cannot be assigned a consistent radial weight; no bilinear term needs the radial scaling before an LDU/Schur substitution in a noncommuting way; and the active set is stable under the coordinate reshapes used by `Q_M`/`chartIdxEquiv`.

If those pass, B becomes viable. If any fail, fusion is mathematically structural.

**3. If A/Fused**

Mathlib’s `Matrix.BlockTriangular.det` is abstract enough for opaque widths: it works over an arbitrary finite index type `m` with a grading `b : m → α`, and gives the determinant as a product of determinants of the fiber blocks; it does not require Fin-literal block sizes. There is also a `det_fintype` version over all block labels. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Block.html))

The hard obstruction is not the theorem. It is proving that your opaque-width Jacobian’s off-block entries vanish and then identifying each `toSquareBlock b a` with the intended `Wext/Text k` block determinant. A cleaner route is likely a **layer filtration**: prove per-layer diagonal-block determinant lemmas and multiply them, using block triangularity only over the chain-layer grading rather than a finely engineered SCC grading.