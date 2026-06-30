# genm-lduinj — statement card: LDU-product uniqueness

The foundational matrix-algebra atom for the R1-LOWER interior `injOn` leg (LEAF 1 of the L=2
headline). Standalone, reusable bedrock; consumed as `genm-r1lower`'s `injon-skeleton.md` atom #1.

> **Claim.** For `t × t` matrices over `ℝ`, the unit-lower · diagonal · unit-upper factorization is
> unique when the diagonal is nonzero: if
> `(1 + lowMatL l) · diag q · (1 + upMatL u) = (1 + lowMatL l') · diag q' · (1 + upMatL u')` and
> `∀ i, q i ≠ 0`, then `l = l'`, `q = q'`, `u = u'`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.RouteMLDUUniqueness.lduCore_unique`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMLDUUniqueness.lean` @ branch `genm-lduinj`)
> - **Gloss.** `l, l' : LowIdx t → ℝ` (strict-lower free entries), `q, q' : Fin t → ℝ` (diagonal),
>   `u, u' : UpIdx t → ℝ` (strict-upper free entries). `lowMatL`/`upMatL` embed the free entries as
>   strictly-lower/strictly-upper matrices (zero diagonal), so `1 + lowMatL l` is unit-lower-triangular
>   and `1 + upMatL u` unit-upper-triangular (`= 1` on the diagonal). The triple product is the LDU
>   matrix. Hypothesis: every diagonal pivot `q i` is nonzero. Conclusion: the three coordinate
>   functions coincide. Stated over **opaque width `t : ℕ`** — no concrete small `t`.
> - **Proved.** The full equality `l = l' ∧ q = q' ∧ u = u'`, unconditionally given `hq` and `hprod`.
>   Axiom-clean: `#print axioms lduCore_unique` (forced via `lake env lean`) reports
>   `[propext, Classical.choice, Quot.sound]` — the clean three.
> - **Assumed.** Only the two stated hypotheses (`hq : ∀ i, q i ≠ 0`; the product equality `hprod`).
>   No extra hypotheses.
> - **Cited.** none (Mathlib lemmas used are reproved-into-context, not assumed: `BlockTriangular`
>   machinery — `blockTriangular_inv_of_blockTriangular`, `BlockTriangular.mul`, `BlockTriangular.add`,
>   `det_of_lowerTriangular`/`det_of_upperTriangular` — plus `nonsing_inv` cancellation lemmas).
> - **Deferred.** none.
> - **Route.** Inverse/conjugation (Codex xhigh-confirmed over the entry-induction alternative).
>   Rearrange `hprod` to `P · diag q = diag q' · Q` with `P = (1+L')⁻¹·(1+L)` unit-lower and
>   `Q = (1+U')·(1+U)⁻¹` unit-upper (conjugate by `Ll'⁻¹ · _ · Uu⁻¹`, cancel via the `@[simp]`
>   inverse lemmas). The four unit factors are `BlockTriangular` with all diagonal entries `1`, hence
>   `det = 1` and invertible; the inverse of a block-triangular matrix is block-triangular. Diagonal
>   entries of `P, Q` are `1` (diagonal-of-product-of-same-handed-triangulars). Entry equation
>   `P i j · q j = q' i · Q i j`: diagonal ⟹ `q = q'`; `i < j` ⟹ `P i j = 0` (lower) ⟹ `Q i j = 0`
>   (`q' i = q i ≠ 0`); `j < i` ⟹ `Q i j = 0` (upper) ⟹ `P i j = 0` (`q j ≠ 0`). So `P = Q = 1`,
>   giving `1+L = 1+L'`, `1+U = 1+U'`; extract the coordinate functions on the strict index sets.
> - **Status.** sorry-free (pending reviewer fidelity check).

## Wire into genm-r1lower atom #1

The `injon-skeleton.md` atom #1 `example` closes with one application of `lduCore_unique` (verified,
scratch `/tmp/wire_check.lean`): after the skeleton's `hprod` is in hand,

    obtain ⟨hl, hqq, hu⟩ := lduCore_unique _ _ _ _ _ _ hq hprod
    exact matrixSplit.injective (Prod.ext hl (Prod.ext hqq hu))

closes `K = K'`. The statement was authored to match the skeleton's slot exactly (`lowMatL`/`upMatL`/
`Matrix.diagonal`/`matrixSplit` from `RouteMSchurFrameDet`), so the wire is a one-liner.

## Reusable lemmas in the file (bedrock)

All in `DLNFibre.DLN.RLCT.RouteMLDUUniqueness`:

- `lowMatL_blockTri` / `upMatL_blockTri` — the strict-triangular embeddings are block-triangular
  (`OrderDual.toDual` / `id`).
- `oneAddLow_blockTri` / `oneAddUp_blockTri` — the unit factors are block-triangular.
- `oneAddLow_diag` / `oneAddUp_diag` (`@[simp]`) — diagonal entries `= 1`.
- `oneAddLow_det` / `oneAddUp_det` (`= 1`) + `_isUnit_det`.
- `lowerTri_mul_diag` / `upperTri_mul_diag` — diagonal of a product of two same-handed triangulars is
  the product of the diagonals (triangularity given in `Fin t`-native `<` form).
- `lowerTri_of_blockTri` / `upperTri_of_blockTri` — `BlockTriangular` ⟺ the entrywise `<`-zero form.
