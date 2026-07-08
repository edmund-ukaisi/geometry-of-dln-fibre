# Statement card — general-`L` common (prefix) pivot (piece i of D1 ≥-leg chart data)

> **Claim.** At an optimal `v` (`prod H v = B`, `B.rank = r`) for a general `L`-layer network with
> widths `H : Fin (L+1) → ℕ`, there is a per-vertex family of injections
> `ι : (s : Fin (L+1)) → Fin r → Fin (H s)` such that every prefix-product minor at the shared row
> set `ι 0` is invertible: `(prodAux H v s).submatrix (ι 0) (ι s)` has nonzero determinant for all
> `s`. (General-`L` lift of `exists_common_pivot_L2_at`.)
>
> - **Lean:** `DLNFibre.DLN.RLCT.exists_common_pivot_gen`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1GeCommonPivot.lean` @ `82ec1990`)
> - **Gloss.** Given widths `H`, a rank `r`, a tuple `v : Params H`, a target `B` with `prod H v = B`
>   and `B.rank = r`, there exists a function `ι` assigning to each vertex `s ∈ {0,…,L}` an injective
>   index map `Fin r → Fin (H s)` (the pivot rows/cols at that vertex), such that for every `s` the
>   `r × r` submatrix of the length-`s` prefix product `prodAux H v s` — rows selected by `ι 0`,
>   columns by `ι s` — has determinant `≠ 0`. At `s = 0` the prefix product is the identity, so the
>   minor is the `r × r` identity; at `s = L` it is the full product `prod H v`.
> - **Proved.** The full statement, unconditionally, sorry-free. Over `ℝ`. `r = 0` included (empty
>   minor, det `1`). Axiom footprint (forced `#print axioms`): `[propext, Classical.choice,
>   Quot.sound]` — no `sorryAx`.
> - **Assumed.** `prod H v = B` and `B.rank = r` (optimality + rank), exactly the hypotheses of the
>   L = 2 template. No positivity `r < H s` needed (the L = 2 crux carried it; the pivot existence
>   does not).
> - **Cited.** none. (Proof is self-contained: `Core.exists_square_minor`,
>   `Core.rank_eq_of_det_ne_zero`, `Matrix.submatrix_mul`, `Matrix.rank_mul_le_left`,
>   `Matrix.det_permute`, `Matrix.submatrix_one` — all Mathlib/Core, reproved split inline.)
> - **Deferred.** The per-LAYER pivots `hLayer` — that `(v s).submatrix (ι s) (ι (s+1))` is
>   invertible for every layer `s` — are NOT delivered. They are the extra hypothesis the *symmetric*
>   `schur_product_ldu_rec` demands. They genuinely need Cauchy–Binet
>   (`det(A·B) = ∑_K det A[·,K]·det B[K,·]`, absent in Mathlib v4.29): the rank squeeze gives only one
>   side of a two-factor pivot, not both (a naive forward greedy fails ~10% numerically). The
>   general-`L` chart avoids them by iterating the *asymmetric* two-factor `schur_product_factor`
>   (each step `(prefix P_s)·(layer v_s)` needs only the two prefix pivots `P_s`, `P_{s+1}`, never an
>   interior layer's own minor) — so the prefix pivots delivered here suffice. The *simultaneous*
>   layer+prefix claim IS true (0/397 numeric fails); only its proof route is walled.
> - **Structure & ideas observed.** The construction is `exists_common_pivot_two_factor`'s rank
>   squeeze iterated with a FIXED row set `ι 0`: pick `ι 0` and a witness column set from a
>   full-product invertible minor; the split `prod H v = (prodAux H v s)·Y` forces
>   `(prodAux H v s).submatrix (ι 0) id` to rank `r` (via `rank_mul_le_left`), whence an invertible
>   `r`-column minor, transported back to the row set `ι 0` by a row permutation. The prefix-only
>   conditions are exactly the L = 2 template (its `v0`-minor = prefix-1, `prod`-minor = prefix-2).
> - **Route.** Cauchy–Binet-free iterated squeeze (Codex-decorrelated design,
>   `threads/genm-geleg1/codex/piece-i-statement-{prompt,answer}.md`).
> - **Status.** sorry-free + reviewed (reviewer verdict PASS-WITH-NITS: fidelity / non-vacuity /
>   scope-honesty / proof-soundness all PASS; the L = 2 specialization recovers the template exactly;
>   nits are marginal name-precision — `_gen` omits "prefix" but matches the prefix-only
>   `exists_common_pivot_L2_at` precedent — and the aggregator + `AxCheck` wiring, reserved for the
>   controller). Reviewer discarded a Codex hallucination of a nonexistent interior-layer condition.
