# Statement card — Brick F2 `measurableEigendecomp` (decomposition tide)

> **Claim.** A measurable Hermitian (real-symmetric) matrix family `A : X → Matrix (Fin M₂) (Fin M₂) ℝ`
> (`Measurable A`, `∀ z, (A z).IsHermitian`) has (i) measurable sorted eigenvalues `eigenvalues₀`, and
> (ii) a MEASURABLE orthogonal `U` with `A z = U z · diagonal(λ↓(z)) · (U z)ᵀ`, `λ↓` the `eigenvalues₀`
> in decreasing order. (F1 / Brick-F contract; the last Mathlib gap of the `(□)` endgame.)
>
> - **Lean:** `DLNFibre.DLN.RLCT.measurableEigendecomp`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJMeasurableEigendecomp.lean` @ commit `<SHA>`)
> - **Gloss.** The exact F1 contract signature (verbatim): the eigenvalue-map is measurable, and there
>   exists a measurable `U` with `Uᵀ U = 1` and the sorted triple-product diagonalization, the diagonal
>   indexed `i ↦ eigenvalues₀ (finCongr (card_fin M₂).symm i)`.
> - **Proved (sorry-free, `[propext, Classical.choice, Quot.sound]`).**
>   - `frame_diagonalizes` — the linear-algebra reduction: `Uᵀ U = 1` and `A U = U · diagonal d` ⟹
>     `A = U · diagonal d · Uᵀ` (right-inverse from `mul_eq_one_comm`). Reusable bedrock.
>   - `measurableEigendecomp` — ASSEMBLED from the two primitives via `frame_diagonalizes`: the
>     packaging (conjunct (i) direct; conjunct (ii)'s per-column eigenvector condition → triple product)
>     is closed. The main theorem is sorry-free **modulo** the two named primitives below.
> - **Deferred (two isolated, correctly-typed sorries, each carrying its build recipe).**
>   - `measurableEigenvalues₀` (conjunct (i)) — Mathlib-absent. Recipe: Vieta coefficient embedding +
>     Lusin–Souslin measurable inverse (`Measurable.measurableEmbedding` + `measurable_comp_iff`,
>     `MeasurableSet.standardBorel`, `Multiset.prod_X_sub_C_coeff`, `charpoly_eq`) — all API verified
>     present at v4.29. ~450–950 LoC (its own sub-tide; ideally `Core/Matrix/OrderedRootsMeasurable`).
>   - `exists_measurableEigenframe` (conjunct (ii) core) — Mathlib-absent. Recipe: global zero-safe
>     Lagrange projector `∏ⱼ (1 + (λᵢ−λⱼ)⁻¹ • (A − λᵢ•1))` (Lean's total `0⁻¹=0` absorbs the multiplicity
>     stratification) + measurable first-nonzero-column pivot + finite frame fold. ~1350–2750 LoC.
> - **Cited.** none.
> - **Structure & ideas observed (pen-and-paper `brickF-measurable-frame-adjudication.md`, +
>   decorrelated Codex `codex/f2-leanroute-answer.md`).** Truth-value = LABOUR (a concrete Borel formula
>   exists; NO Kuratowski–Ryll-Nardzewski, NO contour integral). The `O(k)` degenerate-block ambiguity
>   collapses by a deterministic formula, not selection. The Lean realisation is a **multi-module
>   MOUNTAIN** (~2200–4500 LoC, 6 modules): every primitive is Mathlib-absent (no Weyl, no
>   root-continuity, no Ky-Fan max, no `unitaryGroup` compactness, `eigenvalues₀` is `Classical.choice`-
>   built with no measurability rider). Codex's two refinements landed here: (1) the Vieta+Lusin–Souslin
>   route dodges root-continuity for conjunct (i); (2) the global zero-safe Lagrange projector avoids
>   explicit multiplicity strata for conjunct (ii).
> - **Route (formaliser).** This tide: SPECIFY the exact contract (validated, builds) + close the glue
>   (`frame_diagonalizes`, assembly) + isolate the two analytic primitives with API-verified recipes.
>   Recommended sub-tide ladder: (1) `OrderedRootsMeasurable` (Vieta engine, Core, standalone) → (2)
>   `HermitianEigenvaluesMeasurable` (conjunct (i)) → (3) `MeasurablePivot` → (4)
>   `HermitianSpectralProjector` → (5) `MeasurableEigenframe` → (6) assembly (this file).
> - **Status.** decomposition skeleton — glue + assembly sorry-free; two analytic primitives isolated
>   (NOT sorry-free overall). Recalibration: F2 is a mountain, not a single tide.
