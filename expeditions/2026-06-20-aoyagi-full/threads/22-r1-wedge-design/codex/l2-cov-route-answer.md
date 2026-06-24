**Verdict:** Route 2 is mathematically sound and should be materially cheaper than Route 1. The opaque `equivFin` is not a soundness problem: you only need bijectivity and round-trips. `active := entryEquivFin '' activeEntries` has `card active = 8` by injectivity of the equivalence, and the pivot determinant lemma only cares about membership/cardinality, not numeric indices. The main Lean cost is not the determinant; it is proving a clean inverse-coordinate lemma for `paramsEquivFlat.symm` and keeping the polynomial factorization from getting buried under opaque index transports. That is still much smaller than rebuilding an explicit `e334` stack.

**Recommended route: Route 2, with Route 3 as fallback.**

1. Define source-level entry indices:
   `FlatIdx M := Σ s, Matrix-entry-index-for-layer-s`, then define `activeEntries : Finset (FlatIdx M)` and `pivotEntry : FlatIdx M`.

2. Define flat active set by transport:
   `active := activeEntries.map equivFin.toEmbedding` or equivalent, and `pivot := equivFin pivotEntry`.

3. Prove bookkeeping once:
   `pivot_mem_active`,
   `active.card = activeEntries.card = 8`,
   and membership reflection:
   `equivFin e ∈ active ↔ e ∈ activeEntries`.

4. Prove the inverse-coordinate lemma from the proven forward coordinate theorem:
   ```lean
   ((paramsEquivFlat M).symm x) s i j = x (equivFin ⟨s,i,j⟩)
   ```
   This should use only `(paramsEquivFlat M ((paramsEquivFlat M).symm x)) = x` plus `equivFin.symm_apply_apply`.

5. Run COV entirely on `Fin 21 → ℝ` using existing project lemmas:
   `pivotBlowupOn` injOn/fderiv/det lemma,
   Mathlib `lintegral_image_eq_lintegral_abs_det_fderiv_mul`,
   and the proven `monomialIntegrand_lintegral_box_eq_top`.

6. Prove factorization after rewriting entries through step 4:
   `routeMCore M (pivotBlowupOn active pivot x) = x pivot ^ 2 * U x`.
   Treat `equivFin` as an uninterpreted bijection; all algebra should happen after rewriting each relevant flat coordinate back to its named matrix entry.

If Route 2 founders, Route 1 is the only clean fully-honest finish, but I would not treat it as a single-scratch-file deliverable. Inference: given the prior `(2,2,2)` footprint, `(3,3,4)` explicit enumeration plus algebra will likely become another mini-library, not a compact terminal lemma.

For one scratch file and finite effort, the most valuable honest deliverable is Route 3 only if Route 2’s inverse-coordinate/factorization rewriting becomes unstable. The exact cut-point should be:

Proven above the sorry:
`transport + box-pullback + active/pivot bookkeeping + inverse-coordinate lemma + exact Params/flat wedge factorization + U ≥ 1/4 on positive-measure slice`.

Single labelled sorry asserts:
the COV/leaf bridge on `Fin 21 → ℝ`, namely that the integral over the flat image of the wedge diverges because `pivotBlowupOn` contributes Jacobian `u^7` and the loss contributes `u^(-8)`, reducing to the proven monomial atom `(k,h)=(1,7)`.

Biggest trap in Route 2: accidentally proving factorization for a flat chart whose active set is definitionally different from the one used by the determinant/COV lemma. Cheapest test: before any ring proof, prove eight concrete rewrite lemmas saying each intended Params entry of `(paramsEquivFlat.symm (pivotBlowupOn active pivot x))` is exactly either `x pivot * x (equivFin e)` or unchanged, and prove one inactive-entry sanity lemma.