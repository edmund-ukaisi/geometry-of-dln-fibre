# Scoping note — the `det DΦ(v) ≠ 0` MINOR route (the bounded f'-invertibility build)

**Verdict: BOUNDED, general-`v`, NO stratum case-split.** Decorrelated pen-and-paper (obstruction
seat, exact sympy) + Codex xhigh, both machine-confirmed. This supersedes the vaguer "exhibit `nReg`
independent gradients" phrasing of [[hindep-scope]] with the precise Lean-ready route, and flags the
one operational trap.

## The category-error correction (load-bearing)

The worry "an independent set of `nReg` gradient functionals may NOT extend to a basis via
*coordinate* functionals" is a **category error**. Extending an independent covector family to a
basis using the standard coordinate covectors is **Steinitz exchange / matroid basis-extension** —
true for EVERY independent family (the coordinate covectors span `(ℝ^N)*`), with NOTHING depending on
the gradient structure `δ¹A²_v + A¹_v δ²`. It is NOT the (genuinely-false-in-general) statement "an
arbitrary subspace has a coordinate complement."

## The route to BUILD (Q3, minor-first — the clean Lean phrasing)

`DΦ(v)` invertibility ⟺ `Dg(v)` has a nonzero `nReg × nReg` minor. Concretely:

1. `Dg(v) : ℝ^N → Mat_{H0×H2}`, `δ ↦ δ¹ A²_v + A¹_v δ²`; the `H0·H2` component functionals are the
   `∇g_ij(v)`. **`rank Dg(v) = H0·b + a·H2 − a·b` where `a = rk A¹_v`, `b = rk A²_v`.**
2. **`rank Dg(v) ≥ nReg` at EVERY optimal `v`** (slack `= H0·b + a·H2 − a·b − r(H0+H2−r) ≥ 0`,
   `= 0` iff `a=b=r` the deepest full-rank factorization; exhaustively verified over all widths ≤ 6).
3. `rank ≥ nReg ⟹ ∃ nReg×nReg invertible submatrix` (rows `S` = selected entries, cols `W`) — standard
   determinantal rank. **Mathlib-bounded: this is exactly
   `RankLocusClosed.exists_submatrix_det_ne_zero_of_le_rank` (`nReg ≤ A.rank ⟹ some minor ≠ 0`), the
   `←` engine of `rank_le_iff_forall_submatrix_det_eq_zero`.**
4. `Φ = (g_S − g_S(0), P)`, `P = projection onto Wᶜ` (the complement of the invertible minor's
   columns). `DΦ(v) = [[Dg|_W, Dg|_{W'}], [0, I]]` block-triangular ⟹ `det DΦ(v) = ±det(Dg(v)[S,W]) ≠ 0`.
5. `f' := DΦ(v).toContinuousLinearEquivOfDetNeZero hdet` — its CLM-coe is DEFINITIONALLY `DΦ(v)`
   (`coe_toContinuousLinearEquivOfDetNeZero`), so `hΦ' : HasFDerivAt Φ (f' : E →L E) 0` is free once
   `HasFDerivAt Φ DΦ(v) 0`.

## ★ THE OPERATIONAL TRAP (the only place a naive build trips)

For a **FIXED** coordinate complement `Q`, independence does NOT imply invertibility — smallest
counterexample: `N=2`, grad `= e₁*`, fix `Q={1}` ⟹ `DΦ` rows `(e₁*, e₁*)`, `det = 0`; `Q={2}` ⟹
`det = 1`. So the build must **existentially CHOOSE** `Q = Wᶜ` for `W` the columns of an invertible
minor — NEVER fix the complement coords a priori. The Q3 phrasing handles this: choose `W` from
"rank ≥ nReg ⟹ nonzero minor", `P := proj Wᶜ`. This is an `∃`-extraction inside ONE proof, NOT a
stratum case-split across separate proofs. (This is the gate-4 trap's true shape: not "deepest-only
family" but "fixed-complement". The general-`v` family is fine; the complement must be chosen.)

## (3,3,3)/r=1 middle-stratum witness (machine-checked)

`A¹_v=diag(1,1,0)`, `A²_v=diag(1,0,0)`, `prod=diag(1,0,0)=B` rank 1; `rk A¹_v=2, rk A²_v=1`,
`nReg=5` but **`rank Dg(v)=nReg_v=7`** (strictly larger). Invertible 5-minor: rows `{0,1,2,3,4}`,
cols `{d1[0,0],d1[1,0],d2[0,1],d2[0,2],d2[1,1]}`, `det=1`. All 21 independent 5-subsets admit a
coordinate complement. No middle-stratum break.

## What this does NOT cover (residual D1 risk is downstream)

This closes f'-invertibility (the H_indep core). The residual D1-at-general-`v` content is the
post-chart RESIDUAL FORM `F = ∑_{k∈S} s² + ‖q‖²` + the germ `lossFlatShift =ᶠ F∘Φ` (Codex route (3):
`F := f∘Ψsymm`, germ auto, RLCT germ-local) + the global-C¹ `q` (bump cutoff) + the `ℝ^N ≅ ℝ^nReg×Y`
MP reindex (permutation tracking). See [[step3-construction-answer]] for the Codex design pass.

Artefacts: `codex/dln_{chart,q123,theory,slack}.py` (exact sympy), `codex/detne0-minor-route-codex.md`
(decorrelated Codex), `codex/step3-construction-answer.md` (the chart-construction design pass).

## BUILD STATE (live)

Banked clean-three this tide (branch `genm-d1hchart`, pushed origin):
- **`S1IFTChart.rlctAtOn_eq_of_contDiff_chart_inv`** (`@5e6b596e`) — the route-(3) interface: exposes
  the IFT inverse `Ψsymm` (total `E→E`, locally inverts `Φ` on open `V∋wstar`) with
  `rlctAtOn f wstar = rlctAtOn (f∘Ψsymm) wstar` for ANY `f`. Germ automatic. This UNBLOCKS the germ
  step — the DLN site reads off the selected-coordinate structure of `f∘Ψsymm` rather than supplying
  `F` + re-proving the germ.

SPECIFY validated (UNCOMMITTED working file `lean/DLNFibre/DLN/RLCT/Validate/D1HChartRank.lean`,
signature builds green, single isolated `sorry` = the rank lower bound):
- **`jointDiffL2 H v : Params H →ₗ[ℝ] Mat (H 0) (H 2)`**, `δ ↦ layer0 δ * layer1 v + layer0 v * layer1 δ`
  (`= δ⁰A²_v + A¹_v δ²`). The `layer0`/`layer1` ascriptions (`@[reducible]`, `A 0`/`A 1` re-typed to
  `Mat (H 0) (H 1)`/`Mat (H 1) (H 2)`) dodge the `Fin.castSucc`/`Fin.succ` `HMul`-unification block;
  `layer{0,1}_{add,smul}` `@[simp] rfl` lemmas discharge `map_add'`/`map_smul'`. Codomain `Mat (H 0) (H 2)`.
  The clean foundation — REUSE it.
- open `sorry` = `nReg_le_finrank_range_jointDiffL2`: `r*(H0+H2−r) ≤ finrank ℝ (range (jointDiffL2 H v))`.

Remaining sequence (each its own clean-three commit):
1. **`Dg(v)` joint differential** — DONE as `jointDiffL2` (the `LinearMap`). The `HasFDerivAt`-from-loss
   tie (`δ↦δ¹A²_v+A¹_v δ²` = the loss-entry gradients, from `prodAuxEntryDeriv` at `k=L=2`) is a
   separate small lemma the assembly needs; the rank bound is stated directly on `jointDiffL2`.
2. **`rank Dg(v) ≥ nReg`** (the OPEN sorry). ROUTE C, Codex xhigh endorsed (`codex/rank-lowerbound-{prompt,answer}.md`):
   embed the EXACTLY-rank-`r` **deep tangent space** `deep(δ₀,δ₁) = δ₀·Q + P·δ₁` (`P : Mat (H0)(r)`,
   `Q : Mat (r)(H2)`, `B = P·Q` rank-`r` factorization) into `range (jointDiffL2 H v)` — sidesteps the
   pivot-sensitive explicit family AND the intersection-dim. The embed: `col(B) ⊆ col(A¹) ⟹ P = A¹·S`,
   `row(B) ⊆ row(A²) ⟹ Q = T·A²`, so `deep(δ₀,δ₁) = (δ₀ T)A² + A¹(S δ₁) ∈ range`. Then
   `finrank(range deep) = nReg` (rank-nullity, `ker deep ≃ Mat (r)(r)` via `δ₀=−PX, δ₁=XQ`) and
   `Submodule.finrank_le` gives `nReg ≤ finrank(range jointDiffL2)`.
   **Verify-first findings (gate the build):** the Codex-named Mathlib lemmas `Matrix.rank_factorization`,
   `range_mul_le_left/right`, `exists_mul_of_mul_subset_range` are ALL ABSENT in v4.29 (only
   `Matrix.range_mulVecLin` exists). BUT the repo has `Skeleton.rank_factor_left/right` (private — takes an
   EXISTING `B=U·V`, proves `U,V` full-rank `r`); the rank-`r` factorization EXISTENCE `∃ P Q, B=P·Q ∧
   rk P = rk Q = r` must still be built (or found elsewhere), and the column-containment factor-extraction
   (`col(P) ⊆ col(A¹) ⟹ ∃ S, P = A¹·S`) too. So step 2 is a ~4-6-lemma sub-build with 2 from-scratch
   foundational lemmas — a genuine multi-tide, NOT a single fill. The kernel `≃ Mat (r)(r)` dimension count
   is Codex's flagged trickiest-coercion spot (3-attempt watch). Alternative if factorization stalls: the
   explicit matrix-unit basis `{Eᵢⱼ·Q} ∪ {P·Eⱼₖ}` minus the `r²` overlap (`{P·Eⱼₗ·Q}`) — `nReg` independent
   by full-rank `P,Q` injectivity; heavier enumeration but no kernel-iso.
3. **invertible `nReg`-minor** via `Core.RankLocusClosed.exists_submatrix_det_ne_zero_of_le_rank`
   (banked); choose `W` = its columns (the ∃-extraction — NEVER fix the complement, the trap).
4. **`Φ = (g_S − g_S(0), proj Wᶜ)`**, `det DΦ(v) ≠ 0` (block-triangular), `f' :=
   `DΦ(v).toContinuousLinearEquivOfDetNeZero` (coe def-eq `DΦ(v)` ⟹ `hΦ'` free); `ContDiff ℝ 2 Φ`.
5. **wire**: `dln_hchart_flat` (or the `_inv` corollary directly) → `F = f∘Ψsymm` is `∑s²+∑q²` form
   via `g_k∘Ψsymm=π_k` (selected) + `q = χ·(g_nonSel∘Ψsymm)` global C¹ (bump cutoff) → the
   `ℝ^N≅ℝ^nReg×Y` MP reindex → `deepest_le_of_optimal_of_iftResidual`'s `hchart` slot.
