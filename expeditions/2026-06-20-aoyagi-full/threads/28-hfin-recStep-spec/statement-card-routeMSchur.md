# Statement card — `RouteMSchur` (general-M R1 hfin Schur/radial ladder): N1, N2a, N3a, N3b PROVED; N2b, N4 skeleton

> **Module.** `DLNFibre.DLN.RLCT.Validate.RouteMSchur`
> (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchur.lean` @ `<uncommitted — controller pins SHA>`;
> base merge of `origin/expedition/aoyagi-full` @ `8161f79e`). NOT yet wired into `DLNFibre.lean`
> (single-writer aggregator — controller adds the import).
>
> **Scope.** The four NEW targets of the `L32a-cover-cert.md` §4 build-ready design for the general-`M`
> R1 hfin (upper-bound finiteness) ladder, validated toward the smallest binding corank-2 case `(3,3,4)`.
> Five lemmas PROVED axiom-clean; two honest skeletons (correct, faithful statements + `sorry`).

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

## Skeleton (correct, faithful statement + `sorry` — building blocks, NOT committed)

- **N2b `schur_minorPivot_split` (general `r`)** — on the **bounded complete-pivoting cell**
  (`|R a b| ≤ 1` AND `M11` = a max-modulus `j×j` minor), the **two-sided UNIFORM-constant comparison**
  `c₀·(frobSq (R·S)_top + frobSq (Sc·S_bot)) ≤ frobSq (R·S) ≤ c₁·(...)`. Three soundness pins
  (reviewer/Codex-checked, after the first draft was found VACUOUS): (1) `c₀,c₁` quantified BEFORE `∀ R S`
  (uniform) — the cell hypotheses are REQUIRED, not decorative: numerically the ratio `‖R·S‖²/D` is
  UNbounded over all `{det M11 ≠ 0}` (range 0.0025–26) but tight `≈[0.47, 2.5]` on the cell across
  `r=2,3,4`; (2) Morse block `P := (R·S)_top` (the sheared block `M11·S'_top`), NOT raw `S_top` (which
  is FALSE); `Q := S_bot`; (3) `Sc` STRUCTURALLY pinned to `M22 − M21·M11⁻¹·M12` (not merely by det) +
  the Schur det identity `R.det = M11.det · Sc.det`. The `r=2` rank-1 case is the clean equality N2a.
  **GAP:** the general `r ≥ 3` block-Gauss det-1 normal form `L·R·U = diag(M11, Sc)` (positive-definite
  rank-`j` coupling Gram). De-risked in `minorpivot-cert.md` (R1–R4: comparison-not-equality, Cramer
  minor-ratio shear ≤1, deterministic tie-break, per-level re-pinning). MEDIUM risk.
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
S2 use the headline already rides. The five proved lemmas are each `[propext, Classical.choice, Quot.sound]`
(verified by `#print axioms`). No NEW axiom. When N4 is filled, its `#print axioms` must stay within
`[propext, Classical.choice, Quot.sound, monomial_rlct]`.

## Status
Module builds green via `scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSchur` (286 LoC). Two `sorry`
(N2b, N4), both faithful non-vacuous statements (N2b repaired after a reviewer/Codex vacuity finding —
the first draft re-chose constants per `(R,S)`). No `axiom`/`native_decide`/`#exit`. The base headline
gate (`DLNFibre.DLN.RLCT.AxCheck`) still builds green post-merge. Awaiting reviewer re-confirmation +
controller aggregator wiring (NOT yet imported in `DLNFibre.lean`).
