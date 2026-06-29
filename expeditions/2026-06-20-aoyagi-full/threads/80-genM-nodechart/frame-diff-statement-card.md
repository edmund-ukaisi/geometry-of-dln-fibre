# Statement card — b-FrameM-2 toolkit (opaque-width differentiability atoms), `genm-detcomp`

> **Claim (b-FrameM-2 foundation).** The chart `phiFlatLiveR1` is differentiable over OPAQUE width
> tuples (it is a polynomial map: finite matrix products + linear reshape), so its Jacobian `DFrame_M`
> EXISTS — the existence the b-FrameM-3 keystone (`toMatrix_blockTriangular_of_locality`) needs to
> discharge the headline's `hbt`. This card banks the foundational differentiability ATOMS; the
> chain-telescope assembly is the named next step.
>
> - **Lean:** `DLNFibre.DLN.RLCT.{diffAt_entry, diffAt_matmul, diffAt_matadd, diffAt_smul, diffAt_read,
>   diffAt_constBlock}` (`lean/DLNFibre/DLN/RLCT/Validate/RouteMFrameDiff.lean` @
>   `<pending — off genm-detcomp 3dd596f9>`)
> - **Gloss.** Over the Pi function form `Fin a → Fin b → ℝ` (= the codebase's `Params` shape, Pi-normed):
>   matrix-entry, matrix-product (explicit-sum `= Matrix.mul_apply`), matrix-sum, radial-scalar-scaling,
>   decoder-block-read (`x ↦ x (rd i j)`), and constant-block are each `DifferentiableAt`.
> - **Proved (unconditional, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`):** the six
>   atoms + an in-file non-vacuity composing them into a one-layer chart fragment `(read·read) + (x p)·read`
>   (the `B·chainQ + u·R` shape).
> - **Assumed.** none.
> - **Cited.** none (Mathlib calculus over Pi types: `differentiableAt_pi`, `DifferentiableAt.fun_sum`,
>   `.mul`, `.add`, `.smul`, `differentiableAt_apply`, `differentiableAt_const`).
> - **THE KEY CAST-AVOIDING FINDING (load-bearing, validated empirically this tide):** the naive routes
>   FAIL — `fun_prop` does not discharge it (`Matrix.of` unregistered; abstract `Matrix.mul` whnf-times-out),
>   and `Matrix m n ℝ` carries NO norm instance (the abstract `Matrix` type, behind a norm CHOICE). The fix:
>   state everything over the **Pi function form** `Fin a → Fin b → ℝ` (which IS normed), NOT the abstract
>   `Matrix` type. This is exactly `Params`'s shape (`instNormedAddCommGroupParams`), so the atoms compose
>   directly into `chartParamsGen`. Each output coord is a `Finset.sum` of products of reads, differentiated
>   WITHOUT `fin_cases` on the opaque row index.
> - **Deferred (the chain-telescope ASSEMBLY — the named multi-tide next step):** thread the atoms through
>   the chain constructors `chainQ`/`chainA`/`Cgen`/`Agen` (the telescope `chainOfMt`) → `chartParamsGen`
>   (Params-valued, per-layer via `differentiableAt_pi`) → `phiFlatLiveR1 = paramsEquivFlat ∘ chartParamsGen`
>   (compose with the linear `paramsEquivFlatCLE`). Each chain constructor is a sub-piece (its own ≤4-cast
>   budget over the dependent widths). Output: `DifferentiableAt phiFlatLiveR1 u`, which + the b-FrameM-3
>   keystone discharges `hbt`.
> - **Status.** sorry-free, axiom-clean (forced `#print axioms`) — awaiting reviewer.
