# Statement card — `RouteMSchur` (general-M R1 hfin Schur/radial ladder): N1, N2a, N2b, N3a, N3b PROVED; N4 skeleton

> **Module.** `DLNFibre.DLN.RLCT.Validate.RouteMSchur`
> (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchur.lean` @ `<uncommitted — controller pins SHA>`;
> base `origin/expedition/aoyagi-full`). **Two NEW helper modules** carry the N2b infrastructure:
> `RouteMSchurShear.lean` (the Cramer minor-ratio shear bounds) and `RouteMSchurAlg.lean` (the frobSq
> algebra + the abstract key identity + the abstract comparison + the `Fin r` block split). NOT yet
> wired into `DLNFibre.lean` (single-writer aggregator — controller adds the three imports
> `RouteMSchurShear`, `RouteMSchurAlg`, `RouteMSchur`).
>
> **Scope.** The four NEW targets of the `L32a-cover-cert.md` §4 build-ready design for the general-`M`
> R1 hfin (upper-bound finiteness) ladder, validated toward the smallest binding corank-2 case `(3,3,4)`.
> N1, N2a, **N2b (general `r`)**, N3a, N3b PROVED axiom-clean; one honest skeleton (N4, the multi-tide
> measure-theoretic endpoint).

## Proved (axiom-clean `[propext, Classical.choice, Quot.sound]`, no `monomial_rlct`, no new axiom)

- **N1 `radialDelta_loss_factor`** — `frobSq ((a•R)·S) = a²·frobSq (R·S)` (degree-2 homogeneity of the
  determinantal core under the radial blow-up scale `Δ = a·R`). The integrand identity the per-chart
  change-of-variables consumes. Proof: `ring` (via the helper `rmatMul_smul_left`: `(a•R)·S = a·(R·S)`).
  LOW risk as predicted.
- **N2a `rankOne_outerProduct_split`** — the `r = 2` rank-1 outer-product split
  `frobSq (R·S) = (∑ col²)·frobSq (row·S)` for `R i k = col i · row k` (outer product `col⊗row`),
  `row·S` the single residual linear form (corank-1 reduced core). The `(3,3,4)` corank-2 recursion's
  terminal rank-drop leaf; the `c₀=c₁` scalar-`M11` special case of N2b. Proof: `ring`. Sympy-pinned
  (`L32a_schur_r3.py`, the `r=2` rank-1 identity).
- **N3a `radial_aAxis_divisor_lt_top`** — the radial a-axis divisor `∫_{[−T,T]} |a|^{(r²−1)−2c'} da < ⊤`
  for `c' < r²/2` (the radial Jacobian `|a|^{r²−1}` against the N1 degree-2 scale). The exponent
  `(r²−1)−2c' > −1 ⟺ c' < r²/2` is the a-axis threshold of the per-chart MIN. Proof: the existing 1-D
  monomial atom `abs_rpow_lintegral_Icc_lt_top` + `linarith`. S2-FREE.
- **N3b `radial_loss_chart_lt_top`** — the per-chart finiteness (faithful form): for the corank-`r` core
  with `Δ = a·R` (radial scale `a ∈ [−T,T]`, angular `R` over `matBox r r T`, free block `S` fixed), the
  radial-Jacobian-weighted integral `∫_a ∫_R |a|^{r²−1}·frobSq((a•R)·S)^{−c'}` is finite for `c' < r²/2`,
  GIVEN the inner R-integral `∫_R frobSq(R·S)^{−c'} < ⊤` (`hSfin`, supplied by the N2 Schur recursion).
  Proof: N1 factors the integrand `|a|^{(r²−1)−2c'}·frobSq(R·S)^{−c'}` (a.e. off the null `{a=0}`);
  Tonelli (`lintegral_const_mul'`/`lintegral_mul_const'`) separates the a-axis (N3a) from the inner
  R-integral (`hSfin`); `ENNReal.mul_lt_top` of two finites. **Closed in full** (the cert rated N3 MEDIUM
  risk; the a-axis/inner Tonelli split went through cleanly given the inner hypothesis). S2-FREE.
- **N2b `schur_minorPivot_split` (general `r`, PROVED)** — on the **bounded complete-pivoting cell**
  (`|R a b| ≤ 1` AND `M11` = a max-modulus `j×j` minor, `det M11 ≠ 0`), the two-sided UNIFORM-constant
  comparison `c₀·(frobSq (R·S)_top + frobSq (Sc·S_bot)) ≤ frobSq (R·S) ≤ c₁·(...)` with explicit
  `(c₀, c₁) = (1/(2+2·j·(r−j)), 2+2·j·(r−j))` (quantified BEFORE `∀ R S` — uniform), the structural Schur
  complement `Sc = M22 − M21·M11⁻¹·M12`, and the Schur det identity `R.det = M11.det · Sc.det`. NON-VACUITY
  GATE PASSED (exhaustive + adversarial + det→0-edge, `L32a_N2b_{exact_lean,adversarial}.py`): the ratio
  `frobSq(R·S)/D ∈ [0.245, 3.39]` across `r=2,3,4` all `j` ON the cell, UNbounded (spread up to 2e8) OFF
  the cell. **The de-risking finding** (`L32a_N2b_{rawvsQ,keyident}.py`, residual `< 1.6e-12` up to `r=5`):
  the whole `L⁻¹·diag·U⁻¹` block-Gauss machinery is UNNECESSARY — one algebraic identity collapses it:
  `(R·S)_bot = (M21·M11⁻¹)·(R·S)_top + Sc·S_bot` (needs only `M11·M11⁻¹ = 1`). Importantly the statement's
  raw blocks `(R·S)_top` and `Sc·S_bot` ARE the natural normal-form blocks (`Q = S_bot` and
  `(R·S)_top = M11·P` exactly), so no fidelity gap. **Proof route (Codex route ii, raw-frobSq, no opNorm):**
  `schur_key_identity` (the collapse) + `rowShear_entry_le_one` (the Cramer minor-ratio `|A entry| ≤ 1`,
  the documented long-pole) + `frobSq_add_le` + `frobSq_rmatMul_entryBound_le` (Cauchy-Schwarz) +
  `frobSq_fin_block_split` + the Schur det identity (`det_fromBlocks₁₁` + a `Fin r ≃ Fin j ⊕ Fin (r−j)`
  reindex). S2-FREE. The `r=2` rank-1 case is the clean N2a (subsumed).

### N2b supporting lemmas (all PROVED axiom-clean, in the two helper modules)
- `RouteMSchurShear.colShear_entry_le_one` / `rowShear_entry_le_one` — `|(M11⁻¹·M12) entry| ≤ 1` and
  `|(M21·M11⁻¹) entry| ≤ 1` on the max-modulus-minor cell (via `inv_def` + `cramer_apply` +
  `updateCol_submatrix_eq` + `hpivot`; the row version is the transpose dual). The cert's "main
  formalisation cost."
- `RouteMSchurAlg.schur_key_identity` — the abstract algebraic collapse.
- `RouteMSchurAlg.schur_abstract_comparison` — the abstract two-sided frobSq comparison, explicit constants.
- `RouteMSchurAlg.frobSq_add_le`, `frobSq_rmatMul_entryBound_le`, `fin_sum_block_split`,
  `frobSq_fin_block_split` — the elementary frobSq algebra + the `Fin r` block reindex.

## Skeleton (correct, faithful statement + `sorry` — building blocks, NOT committed)

- **N4 `routeMCore_threshold_lt_top` (the hfin conclusion)** — for `c' < ½·minAdm M`,
  `∫_{routeMBaseNbhd M} |routeMCore M x|^{−c'} < ⊤`. The general-`M` analog of
  `routeMCore_M4422_threshold_lt_top`. Discharges the `hfin` field of `routeMLayerCover_of_atoms` (given
  the leaf-sum ⟹ `c' < ½·minAdm` premise reduction). **GAP:** the depth-`r` WellFounded-on-corank
  measure-theoretic cover assembly (`recStep` over the `r²` radial-`Δ` charts → N3b per-chart → N2b Schur
  split → Morse-block peel `radial_morse_dominates_lt_top` → recurse on the corank-`(r−j)` core →
  Morse/monomial leaves). HIGH risk — the long pole. Validate on `(3,3,4)` (corank-2, ONE nested level)
  first; the hfin chart bundle for `(3,3,4)` does not yet exist (the existing `NodeAchieverChart` is the
  GE/divergence side).

## S2-hygiene
The hfin CONCLUSION is proven S2-FREE (Morse leaves, the a-divisor 1-D monomial, Tonelli, Schur splits,
radial Jacobian dets). `monomial_rlct` (S2) enters ONLY the leaf-sum hypothesis side of `hfin` — the same
S2 use the headline already rides. All N1/N2a/N2b/N3a/N3b lemmas + the N2b supporting lemmas are each
`[propext, Classical.choice, Quot.sound]` (verified by FORCED `#print axioms` after a force-rebuild — no
`sorryAx`, no `monomial_rlct`, no new axiom). When N4 is filled, its `#print axioms` must stay within
`[propext, Classical.choice, Quot.sound, monomial_rlct]`.

## Status
- `RouteMSchurShear.lean` builds green (`scripts/lb`, 8248 jobs); `RouteMSchurAlg.lean` green (2682 jobs);
  `RouteMSchur.lean` green (8281 jobs, force-rebuilt after olean delete). The full base `scripts/lb
  DLNFibre` still builds green (8494 jobs) post-edits.
- **N2b PROVED sorry-free + axiom-clean** (`#print axioms schur_minorPivot_split` →
  `[propext, Classical.choice, Quot.sound]`, forced). The ONLY remaining `sorry` in `RouteMSchur.lean` is
  N4 (the multi-tide measure-theoretic endpoint, out of this leg's scope).
- Name-clash gate: `rg` of all new top-level names (`schur_minorPivot_split`, `schur_key_identity`,
  `schur_abstract_comparison`, `colShear/rowShear_entry_le_one`, `frobSq_add_le`,
  `frobSq_rmatMul_entryBound_le`, `fin_sum_block_split`, `frobSq_fin_block_split`,
  `inv_mulVec_eq_cramer_ratio`, `inv_mul_eq_inv_mulVec_col`, `updateCol_submatrix_eq`) against the whole
  `DLNFibre/` tree — NO clashes.
- No `axiom`/`native_decide`/`#exit`. Awaiting reviewer fidelity re-confirmation + controller aggregator
  wiring (the three imports are NOT yet in `DLNFibre.lean` — single-writer).
