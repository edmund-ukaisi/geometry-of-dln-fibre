# Statement card — general-`L` R1-UPPER `(S,J)` resolution SKELETON (`sjfound` foundation tide)

**Status:** sorry-free for the CLOSED pieces + the recursion wrapper; the genuinely-new analytic
content is confined to clearly-named sorries. Green in the full import closure of
`RouteMSJResolution` (8295 jobs). On `origin/genm-sjresolution` (base
`origin/expedition/aoyagi-full @3d533215`), module commit `d74066a1`. **NOT yet wired into
`DLNFibre.lean`** (single-writer aggregator) — controller to add the import.

> **UPDATE (`genm-sjbase` tide, base `origin/expedition/aoyagi-full @3cb51997`).** The two
> foundational/base sorries (next-tide order #1 and #2) are now **CLOSED sorry-free**:
> - **`sjBase1_freeMatrix`** (the `L = 1` free-matrix Morse base) — reduced the `Params M` box integral
>   through the measure-preserving flattening `paramsEquivFlat M` to the `Fin (M₀M₁)` Morse box, finite by
>   the banked `sumSqND_box_lt_top` (threshold `M₀M₁/2 = ½·minAdm M`); the degenerate `M₀M₁ = 0` case is
>   vacuous. New helpers: `frobSq_prod_eq_flatSum` (`= ∑ flat²` via `prod_one_layer` + `FlatIdx` collapse),
>   `morseBox_sumSq_lt_top` (the `Fin N`-form of the `Fin (m+1)` Morse endpoint), `minAdm_two_eq`.
> - **`minAdm_leadWidth_mono`** (piece-6 residual) — arity induction on the layer-peeling recursion
>   `minAdm_cons_eq` (= `sjChargeBudget_recursion` in `cons` form): the reduced chains `cons t (tail rest)`
>   are shared between the `p`/`q` sides (`redChain_cons`), so the two `inf'`s differ only in the pivot
>   range and the block factor; range-widening handled by the `t = p` zero-charge cut + the IH on
>   `tail rest`. New helpers: `cons_one_eq`, `redChain_cons`, `minAdm_cons_eq`.
>
> Both **force-`#print axioms` clean-three** `[propext, Classical.choice, Quot.sound]` (no `sorryAx`);
> `sjSubordination` and `minAdm_le_minAdm_tailChain` (which rode the piece-6 residual) are now clean-three
> too. The module's remaining sorries are **exactly** `sjBoundaryPeel` + `sjJointResolution` (the two
> LOAD-BEARING analytic pieces); `routeMBoxThresholdFinite_sjResolution` carries `sorryAx` via only those.
> Full `scripts/lb DLNFibre` green. On `origin/genm-sjbase`.

> **UPDATE (`genm-sjpeel` tide, base `origin/genm-sjbase @7d5dadc1`).** The **OUTER measure-preserving
> reduction** of `sjBoundaryPeel` (piece 3) is now CLOSED sorry-free and reusable. `sjBoundaryPeel` ITSELF
> remains a named sorry (its statement UNCHANGED) — the residual analytic content is the per-tail-parameter
> fibre bound. New sorry-free plumbing (all force-`#print axioms` **clean-three** `[propext,
> Classical.choice, Quot.sound]`):
> - **`eFront`** — the general-`L` `eParamsRRP`: MP front-split `Params M ≃ᵐ (M₀×M₁ matrix) ×
>   Params (tailChain M)` peeling layer `0` (`piFinSuccAbove` at `0`; tail widths `tailChain M i = M i.succ`
>   make the reindexed factor family defeq to `Params (tailChain M)`). `measurePreserving_eFront` (banked
>   `volume_preserving_piFinSuccAbove`), `eFront_fst`/`_snd_apply`/`_snd_eq_Atail`, `eFront_preimage_box`.
> - **`frobSq_prod_front`** — the `prod_front_peel` integrand identity in raw-product form
>   `frobSq (prod M A) = frobSq (rmatMul (A 0) (prod (tailChain M) (tail A)))` (reindex-over-`rfl`-widths
>   collapse via `finCongr_refl` + `reindex_refl_refl`; `Matrix.mul` ≡ `rmatMul`).
> - **`routeMLayerBoxIntegral_front_split`** — `routeMLayerBoxIntegral M c' 1 = ∫_{A'∈box(tail)}∫_{A₀∈box}`
>   `frobSq(A₀·prod(tailChain M)A')^{−c'}` (transport via `eFront` + `eFront_preimage_box` +
>   `frobSq_prod_front`, then `setLIntegral_prod_symm` puts the tail integral outermost).
> - Support: `continuous_frontLoss`, `measurable_frontIntegrand`, `measurable_jointPeelIntegrand`, and the
>   `Params` Pi-instances `instBorelSpaceParams` / `instSecondCountableParams` / `instSigmaFiniteParams`
>   (expose the Pi `BorelSpace`/`SecondCountable`/`SigmaFinite volume` through the `Params` def so
>   `Continuous.measurable` and the product-measure Tonelli lemmas fire).
>
> The module's remaining sorries are **exactly** `sjBoundaryPeel` + `sjJointResolution` (same names/count
> as `genm-sjbase`); `sjBoundaryPeel`'s OUTER half is now banked as the CLOSED lemmas above. Full
> `scripts/lb DLNFibre` green (8720 jobs). On `origin/genm-sjpeel`.
>
> **FIDELITY-REVIEW FINDING (why `sjBoundaryPeel` was NOT discharged this tide).** An interim attempt to
> discharge `sjBoundaryPeel` via a FIXED-`Q` pointwise residual `sjFrontFactorPeel`
> (`∫_{A₀∈matBox} frobSq(A₀·Q)^{−c'} ≤ ∑ₜ C · frobSqTopRows t Q^{−(c'−a/2)} · frobSq Q^{−a/2}`) was found
> **FALSE** by the fidelity reviewer + decorrelated Codex (Lean-checked counterexample: `M=(1,2,1)`,
> `c'=1/4`, `Q=[[0],[1]]` — LHS `= 8`, RHS `= 0`). Root cause: `P_tail = frobSqTopRows t Q` is raised via
> `Real.rpow` inside `ofReal`, and `Real.zero_rpow` gives `0^{neg} = 0` (not `+∞`), so on the degenerate
> locus `{P_tail = 0}` (top-`t` rows vanish; and the identically-empty `t=0` top-rows) the RHS collapses to
> `0`. For a FIXED `Q` this locus is a real counterexample; under the OUTER `A'`-integral it is null
> (harmless to `jointPeelIntegral`'s value), so the INTEGRATED `sjBoundaryPeel` conclusion is still sound.
> The false lemma was **REMOVED** (not laundered). **Correct discharge (next tide):** use
> `lintegral_mono_ae` with the degenerate tail-product locus shown null, OR reformulate `jointPeelIntegral`'s
> singular factor via `ENNReal.rpow` (`0^{neg} = ⊤`) — a `jointPeelIntegral` signature change to escalate.
> Reviewer verdict on this tide's output: the CLOSED front-split plumbing PASSES (clean-three, faithful);
> the FAIL was localized to the removed pointwise residual.

One new module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJResolution.lean`. This is the FIRST tide of
the R1-UPPER `(S,J)` mountain (design cert:
`threads/genm-r1upper-design/design-cert.md`, its 7-piece build spec). It lays the honest 7-piece
contract, CLOSES the pieces that reuse banked machinery, and pre-stages the genuinely-new analytic
pieces as named sorries.

> **UPDATE (`genm-sjpeel-cov` tide, base `origin/genm-sjpeel @300fe28d`).** The **inner change-of-variables
> base** of `sjBoundaryPeel` (piece 3) — **Aoyagi Lemma 2** (the unit-triangular Jacobian-`1` reduction) —
> is now built sorry-free in a NEW standalone module `DLNFibre/DLN/RLCT/Validate/RouteMSJPivotChart.lean`
> (namespace `DLNFibre.DLN.RLCT`). `sjBoundaryPeel` ITSELF is UNCHANGED (still a named sorry); this is the
> reusable c.o.v. base its eventual discharge consumes. **NOT yet imported by `RouteMSJResolution`** and
> **NOT yet wired into `DLNFibre.lean`** (single-writer aggregator) — controller to add the imports. On
> `origin/genm-sjpeel-cov @8e8ce87e`. All seven lemmas force-`#print axioms` **clean-three**
> `[propext, Classical.choice, Quot.sound]`; `scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJPivotChart`
> green.
>
> **Deliverable 2 — the c.o.v. (the heart).** Front factor in blocks `A₀ = [[A, B], [C, D]]`, `A` the
> invertible `t×t` pivot:
> - **`schur_cov`** — `Q₁ · fromBlocks A B C D · Q₂ = fromBlocks A 0 0 Γ`, `Γ = D − C A⁻¹ B` the Schur
>   complement (corank block), `Q₁ = schurLeft = [[1,0],[−CA⁻¹,1]]` (unit lower-tri),
>   `Q₂ = schurRight = [[1,−A⁻¹B],[0,1]]` (unit upper-tri). Proof: two `Matrix.fromBlocks_multiply` + the
>   pivot cancellations `⅟A·A = 1`, `A·⅟A = 1` (mirrors Mathlib's `fromBlocks_eq_of_invertible₁₁`).
> - **`det_schurLeft` / `det_schurRight`** — `det Q₁ = det Q₂ = 1` (the **Jacobian-`1`** property, via
>   `det_fromBlocks_zero₁₂`/`_zero₂₁`).
> - **`det_fromBlocks_cov`** (square front factor) — `det [[A,B],[C,D]] = det A · det Γ`
>   (`Matrix.det_fromBlocks₁₁`): the singular locus of the peeled factor is cut out by `Γ`.
>
> **Deliverable 1 — the pivot chart** (`schur_cov` on an actual front factor via a block-split reindex;
> the chart is a block-splitting `e₀ : m ≃ t⊕a`, `e₁ : n ≃ t⊕b` on which the reindexed top-left block is
> invertible):
> - **`schur_cov_toBlocks`** — block-indexed c.o.v.: for any `M' : Matrix (t⊕a) (t⊕b) ℝ` with
>   `[Invertible M'.toBlocks₁₁]`, `Q₁·M'·Q₂ = fromBlocks M'₁₁ 0 0 Γ` (via `fromBlocks_toBlocks`); apply at
>   `M' = A₀.reindex e₀ e₁`.
> - **`pivotBlock_reindex_eq_submatrix`** — the reindexed top-left block IS the chosen pivot minor
>   `A₀.submatrix (e₀⁻¹∘inl) (e₁⁻¹∘inl)`, so "top-left invertible" = "chosen `t×t` minor nonsingular"
>   (`Matrix.invertibleOfIsUnitDet` turns `det ≠ 0` into the `Invertible` instance).
> - **`det_toBlocks_cov`** — `det M' = det(pivot)·det Γ` on a square block-indexed matrix.
>
> **HONEST SCOPE (documented in the module header).** The a.e. COVERING property — every rank-`t` front
> factor lies in some rank-`t` chart (the classical `rank ⟹ nonzero minor of that size`, NOT in Mathlib
> v4.29) — and the measure-theoretic finite-sum assembly (radial blow-up `Γ = zV` + finite-cutoff
> `z`-integral + `Beta` fibre bound + `lintegral_mono_ae` over the null degenerate locus) remain the
> `sjBoundaryPeel` residual (LATER tides). This tide delivers exactly the `Q₁, Q₂` unit-triangular
> reduction and its Jacobian-`1` / Schur-complement facts — the piece the peel's internal "general-`L`
> pivot-Schur chart = Aoyagi Lemma 2" reduction (piece-3 next-tide item) names.
>
> **Status: sorry-free + reviewed.** Fidelity audit (reviewer + decorrelated Codex xhigh, module SHA
> verified, all 7 lemmas `#print axioms` clean-three independently reproduced): **PASS-WITH-NITS**. All six
> substantive checks PASS — `schur_cov` is the faithful Aoyagi-Lemma-2 statement (signs / `⅟A` placement
> confirmed by hand + a concrete ℚ instance `diag(2,−1/2)`); `det_schurLeft`/`det_schurRight` non-vacuous;
> `det_fromBlocks_cov` faithful + square-honestly-scoped; the three lift lemmas faithful; `[Invertible A]`
> is the correct/weakest chart hypothesis; the honest-scope docstring accurate (rectangular-honest, no
> hidden squareness). The one LOW nit — "Jacobian-`1`" named the *algebraic* `det Q = 1` (volume-preserving
> elementary ops), the underpinning of but distinct from the integral c.o.v. substitution `D ↦ Γ` (deferred
> to the assembly) — was folded into the docstrings (`det Q = 1` + a header clause; module SHA `eb761d29`,
> no statement/proof change).

> **UPDATE (`genm-sjpeel-cov` CONSOLIDATION tide, module SHA `4d2cb58a`).** A controller mis-diagnosis
> had produced TWO parallel c.o.v.-base implementations (`genm-sjpeel-cov`'s `schur_cov` conjugation
> algebra + reindex bridge, and `genm-sjpeel-cov-alt`'s `aoyagi_ldu` LDU algebra + a pivot-chart cover +
> a measure shear). This tide MERGES them into ONE base module `RouteMSJPivotChart.lean`: the base's
> `schur_cov` conjugation form is the single Aoyagi-Lemma-2 algebra, and the DUPLICATE LDU form
> (`aoyagi_ldu`/`aoyagiLower`/`aoyagiUpper`) was DROPPED. The unified c.o.v. base now has FOUR parts, all
> sorry-free, force-`#print axioms` **clean-three** `[propext, Classical.choice, Quot.sound]`:
> - **§A the unit-triangular algebra** — `schur_cov` + `det_schurLeft`/`det_schurRight` (`det Q = 1`) +
>   `det_fromBlocks_cov` (unchanged; the base tide's).
> - **§B the reindex → pivot-minor bridge** — `pivotBlock_reindex_eq_submatrix`, `schur_cov_toBlocks`,
>   `det_toBlocks_cov` (unchanged).
> - **§C the pivot-chart COVER (NEW, ported from `origin/genm-sjpeel-cov-alt @985e102c`).**
>   `pivotLocus_eq_iUnion : {A | t ≤ A.rank} = ⋃ (ρ, κ) pivotChart ρ κ` — the finite cover of the
>   rank-`≥ t` front-factor locus by the charts where some `t×t` minor is a unit. Reverse direction
>   `exists_nonsingular_submatrix_of_le_rank` from the banked `Core.exists_pivot_cols_of_rank` (via the
>   size-`t` column selection `exists_indep_cols_of_le_rank`); forward `isUnit_submatrix_le_rank` from
>   submatrix-rank monotonicity `rank_submatrix_le'`/`rank_submatrix_id_col_le`/`_row_le`. **CLOSES the
>   "a.e. COVERING property"** the base tide flagged as residual.
> - **§D the Jacobian-`1` (measure) c.o.v. (NEW, same alt branch).** `measurePreserving_shearSub` — the
>   block shear `(x, D) ↦ (x, D − K x)` (`K = C A⁻¹ B`, exposing `Γ = D − K`) is measure-preserving (a
>   det-`1` `skew_product` fibre translation). This is the MEASURE form of the `D ↦ Γ` substitution —
>   **facet (ii) of "Jacobian `1`" that the base tide had DEFERRED, now in-file.** The banked
>   function-space instance `measurePreserving_coreShear` is pinned as the peel's ready tool.
>
> New imports: `Core.Matrix.RankNormalForm` (§C) + `Foundations.CoreShearMP` (§D). **No FQN clash** — all
> §C/§D declaration names verified globally unique across `DLNFibre/` (rg), and the module builds green in
> its own import closure (a large subset of the aggregator's `DLN.RLCT` namespace). Still **NOT wired into
> `DLNFibre.lean`** (orphan; controller to add the import). `sjBoundaryPeel`/`sjJointResolution` UNCHANGED
> (their honest sorries untouched). Preserves the reviewer's `det Q = 1`-vs-integral-Jacobian precision
> fixes (§A docstrings). On `origin/genm-sjpeel-cov`.
>
> **NEXT peel sub-piece (the `sjBoundaryPeel` residual, built on THIS base).** Radial blow-up `Γ = z·V`
> (`z ∈ [0, ∞)`, `V` on the unit sphere; Jacobian `z^{a−1}`, `a = (M₀−t)(M₁−t)`) reducing the corank-block
> `Γ`-integral to a 1-D `z`-integral → the finite-cutoff `Beta` fibre bound (`∫₀ᵀ z^{a−1}·(z²)^{−(c'−…)} dz`
> finite for `c'` below the per-chart threshold) → the a.e. finite-sum assembly over the §C chart cover
> (`lintegral_mono_ae` on the null degenerate locus) into `sjBoundaryPeel`. §A `schur_cov` exposes `Γ`; §C
> `pivotLocus_eq_iUnion` indexes the sum; §D `measurePreserving_shearSub` is the `D ↦ Γ` c.o.v. the
> blow-up rides on.

## The target

> **Claim.** For an arbitrary width vector `M : Fin (L+1) → ℕ`, the layer-product box integral
> `∫_{A ∈ paramsBoxM M 1} frobSq(prod M A)^{−c'}` is finite for every `c' < ½·minAdm M`
> (`RouteMBoxThresholdFinite M`). This is R1-UPPER (`rlct ≥ ½·minAdm`); it discharges the bare sorry
> `routeMCore_threshold_lt_top` (`RouteMSchur.lean:426`) via `routeMCore_threshold_lt_top_of_box`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMBoxThresholdFinite_sjResolution`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJResolution.lean` @ `d74066a1`)
> - **Gloss.** For all `M`, `RouteMBoxThresholdFinite M` holds — the box integral is `< ⊤` below the
>   geometric threshold.
> - **Proved.** The **recursion spine**: the strong-induction-on-arity wrapper
>   `routeMBoxThresholdFinite_of_step` (axiom-clean `[propext, Classical.choice, Quot.sound]`, NO
>   `sorryAx`) reduces the ∀L target to two contracts — the `(S,J)` inductive step (`SJStepHyp`) and
>   the `L = 1` base (`SJBaseHyp`) — and the step `sjResolutionStep_proof` genuinely composes piece 3
>   (`sjBoundaryPeel`) with pieces 4/5/7 (`sjJointResolution`). The `L = 0` base is closed vacuously
>   (`minAdm = 0`).
> - **Assumed.** none (the target is unconditional; the open content is inside the named sorries).
> - **Cited.** the banked `RouteMLayerSplit` recursion (`LayerSplit_value_eq_minAdm`,
>   `minAdmRec_eq_minAdm`, `Mval_decompose`), the L=2 `(r,r,p)` box-finiteness
>   `routeMBoxThresholdFinite_rrp`, the free-matrix Morse endpoint `sumSqND_box_lt_top`, the L=2
>   fibre engine `fibre_lintegral_mul_le`, the corank recursion `core_schurGen_lt_top`.
> - **Deferred (named sorries — the genuinely-new analytic content).** (Post-`genm-sjbase`: only these
>   two remain; the `L = 1` base is now closed.)
>   - `sjBoundaryPeel` (**piece 3**, LOAD-BEARING) — the boundary-0 blow-up peel: the `M` box integral
>     `≤` finite const × Σ over pivot charts of the joint peeled integral (the cert's exact identity
>     `J ≍ P_tail^{−(c'−a/2)}·P_full^{−a/2}`).
>   - `sjJointResolution` (**pieces 4/5/7**, LOAD-BEARING) — the joint peeled integral is `< ⊤` given
>     the strong IH; the simultaneous `(S,J)` double induction + monomial integrability endpoint.
> - **Closed (`genm-sjbase`).** `sjBase1_freeMatrix` (**L = 1 base**) — the single-free-matrix Morse
>   integral, reduced through `paramsEquivFlat` to the `Fin (M₀M₁)` Morse box, finite by
>   `sumSqND_box_lt_top`.
> - **Status.** sorry-free spine + closed base + closed piece-6 residual; two LOAD-BEARING analytic
>   sorries remain (`sjBoundaryPeel`, `sjJointResolution`).

## What is CLOSED (sorry-free) — the reusable base

| Piece | Declaration(s) | How |
|---|---|---|
| 1 (comparability) | `sjLocalComparability`, `paramsBoxM_volume_lt_top` | pure measure theory + box compactness |
| 2 (pivot-Schur, L=2) | `sjPivotSchurChart_rrp` | banked `routeMBoxThresholdFinite_rrp` |
| 4 (invariant block-dim) | `sjRunMin_antitone` | running-min corank `M(S)` monotone (coarse consequence) |
| 5 (charge accounting) | `sjChargeUpdate_accum` | banked `Mval_decompose` |
| 6 (charge budget) | `sjChargeBudget_recursion`/`_le`/`_binding`, `minAdm_le_minAdm_redChain_min`, `minAdm_le_minAdm_tailChain`, `sjSubordination`, `minAdm_leadWidth_mono` (`genm-sjbase`), `minAdm_cons_eq`/`redChain_cons`/`cons_one_eq`/`minAdm_two_eq` | banked `LayerSplit_value_eq_minAdm` + `minAdmRec_eq_minAdm`; the residual `minAdm_leadWidth_mono` closed by arity induction (fully sorry-free) |
| L=1 base (`genm-sjbase`) | `sjBase1_freeMatrix`, `frobSq_prod_eq_flatSum`, `morseBox_sumSq_lt_top` | `paramsEquivFlat` MP flatten → `Fin (M₀M₁)` Morse box, banked `sumSqND_box_lt_top` |
| spine | `routeMBoxThresholdFinite_of_step` (axiom-clean), `sjResolutionStep_proof`, `routeMBoxThresholdFinite_base0` | strong induction on arity; step = peel ∘ joint |
| defs | `tailChain` (+`_zero`/`_succ`/`_eq_redChain`), `peelExp`, `frobSqTopRows` (+`_nonneg`), `jointPeelIntegral`, `SJState`, `sjRunMin` | the objects the pieces are stated over |

`sjChargeBudget_recursion`, `sjRunMin_antitone`, `sjLocalComparability` are axiom-clean
`[propext, Classical.choice, Quot.sound]` (forced `#print axioms`).

## The named-sorry stubs (open, for subsequent tides)

| Piece | Declaration | Kind |
|---|---|---|
| 3 (peel) | `sjBoundaryPeel` | genuinely-new analytic (LOAD-BEARING) — the per-tail-parameter inner fibre bound; its OUTER front-split is now CLOSED (`genm-sjpeel`) |
| 4/5/7 (joint resolution) | `sjJointResolution` | genuinely-new analytic (LOAD-BEARING) |
| ~~3 outer (front-split)~~ | ~~`routeMLayerBoxIntegral_front_split`/`eFront`/`frobSq_prod_front`~~ | **CLOSED** (`genm-sjpeel`) — MP front-split + `prod_front_peel` identity + Tonelli; banked reusable for `sjBoundaryPeel`'s eventual discharge |
| ~~6 residual~~ | ~~`minAdm_leadWidth_mono`~~ | **CLOSED** (`genm-sjbase`) — arity induction on `minAdm_cons_eq` |
| ~~L=1 base~~ | ~~`sjBase1_freeMatrix`~~ | **CLOSED** (`genm-sjbase`) — free-matrix Morse via `paramsEquivFlat` |

**Two** sorries remain (post-`genm-sjpeel`, same names/count as `genm-sjbase`), both genuinely hard
LOAD-BEARING analytic pieces feeding the final `routeMBoxThresholdFinite_sjResolution`: `sjBoundaryPeel`
(3) and `sjJointResolution` (4/5/7). `sjBoundaryPeel`'s OUTER measure-preserving front-split is now
CLOSED clean-three and banked (the reusable lemmas above); its residual is the per-tail-parameter inner
fibre bound. An interim fixed-`Q` pointwise residual was found FALSE and REMOVED (see the UPDATE banner's
FIDELITY-REVIEW FINDING). The `L=1` base and the piece-6 residual are closed sorry-free (see the UPDATE
banners); `sjSubordination` / `minAdm_le_minAdm_tailChain` no longer carry `sorryAx`.

**Fidelity note (self-caught, corrected).** Two candidate stubs were dropped as misleading: a
`sjNormalFormInvariant` sorry stated as `sjRunMin (S+1) ≤ sjRunMin S` is *trivially true* (inf over a
growing set), so it is CLOSED and renamed `sjRunMin_antitone` (the honest coarse consequence, NOT the
matrix-valued invariant, which is deferred with no fake stub); and a general-`L` `sjPivotSchurChart`
stub was dropped because its statement was identical to `SJStepHyp` (redundant with the closed
`sjResolutionStep_proof`) — the general-`L` chart is the internal c.o.v. of piece 3, stated in
`sjBoundaryPeel`'s docstring.

### On the piece-6 residual `minAdm_leadWidth_mono` (CLOSED, `genm-sjbase`)
`p ≤ q → minAdm (Fin.cons p rest) ≤ minAdm (Fin.cons q rest)`. Numerically verified (0 violations,
`/tmp/sj_check.py`, L ≤ 3, widths 1..5). It is NOT termwise: growing the leading width both raises the
block terms `(p−t)(rest₀−t)` AND widens the admissible pivot range `min(p,rest₀)`, so the
monotone-selection argument does not chain (checked). **Proved** by strong induction on the chain arity
via `minAdm_cons_eq` (the layer-peeling recursion `sjChargeBudget_recursion` rewritten in `Fin.cons`
form, with `redChain t (cons p rest) = cons t (tail rest)` = `redChain_cons` making the reduced chains
`p`-independent): for a `q`-cut `t` inside the `p`-pivot range the shared cell is monotone in the leading
width; for `min(p,rest₀) < t ≤ rest₀` the `p`-cut `t = p` has zero block charge and the induction
hypothesis on `tail rest` gives `minAdm (cons p (tail rest)) ≤ minAdm (cons t (tail rest))`. This closes
the last residual, so `sjSubordination` / `minAdm_le_minAdm_tailChain` are now clean-three.

## The key statement shapes (fidelity anchors against the cert)

- **`jointPeelIntegral M t c'`** (piece 3's object): `∫_{A ∈ paramsBoxM (tailChain M) 1}`
  `(frobSqTopRows t (prod (tailChain M) A))^{−(c'−a/2)} · (frobSq (prod (tailChain M) A))^{−a/2}`,
  `a = (M₀−t)(M₁−t)`. Both factors read the SAME tail parameters `A` — the object is **joint**, NOT
  the (cert-proven-unsound) product of independent single-chain integrals. `P_tail` = top-`t`-rows loss
  (`frobSqTopRows` = the reduced tail chain `(t,M₂,…)` loss), `P_full` = the full remaining product
  `(M₁,…,M_L)` loss (`tailChain M = redChain (M 1) M`, proven).
- **`sjBoundaryPeel`**: `∃ C ≠ ⊤, routeMLayerBoxIntegral M c' 1 ≤ Σ_{t ≤ min(M₀,M₁)} C · jointPeelIntegral M t c'`.
- **`sjJointResolution`**: `(∀ M' : Fin (L+1+1)→ℕ, RouteMBoxThresholdFinite M') → c' < ½·minAdm M → jointPeelIntegral M t c' < ⊤` (strong IH → per-chart finiteness).
- **`SJStepHyp`**: for a `≥3`-width `M`, box-finiteness for every one-shorter chain ⟹ box-finiteness for `M`.

## Recommended next-tide order (the mountain, from here)

1. ~~**`sjBase1_freeMatrix`** (L=1 Morse)~~ — **DONE** (`genm-sjbase`; the reduction went through
   `paramsEquivFlat`, not a bespoke `matBox ≃ᵐ morseBox` reindex).
2. ~~**`minAdm_leadWidth_mono`**~~ — **DONE** (`genm-sjbase`; piece 6 now clean-three, subordination
   axiom-clean).
3. **`sjBoundaryPeel`** (piece 3) — OUTER front-split now CLOSED (`genm-sjpeel`;
   `routeMLayerBoxIntegral_front_split` + `eFront` + `frobSq_prod_front`, clean-three, banked reusable).
   REMAINING = the per-tail-parameter inner fibre bound: the load-bearing peel/exponent-shift (general-`L`
   pivot-Schur chart = Aoyagi Lemma 2, internal + radial blow-up). Consumes piece 1 comparability + banked
   `radial_morse_residual_power_le`/`Cresid` (exponent-shift) + `SchurRecStep_p` (corank recursion). **DO
   NOT** lift to a fixed-`Q` POINTWISE bound (`genm-sjpeel` found this FALSE — `Real.rpow` `0^{neg}=0` on
   the degenerate top-rows locus): discharge via `lintegral_mono_ae` (degenerate tail-product locus null,
   using `routeMLayerBoxIntegral_front_split`'s tail-outer form), OR reformulate `jointPeelIntegral`'s
   singular factor via `ENNReal.rpow` (`0^{neg}=⊤`) — a `jointPeelIntegral` signature change to escalate.
4. **`sjJointResolution`** (pieces 4/5/7) — the standing L≥3 wall: the `(S,J)` double induction (piece 4
   invariant over the `[E_J|D_J]` carrier — block-dim `sjRunMin_antitone` closed; piece 5 charge-update
   `sjChargeUpdate_accum`) + monomial assembly (piece 7), with subordination (`sjSubordination`) keeping
   coupling exponents at or below threshold. Consumes the strong IH. **Gentle-cut caveat (reviewer +
   decorrelated Codex):** subordination is `≤` (NON-strict); strict fails at some `a>0` binding cuts
   (84/3875: `a = minAdm(tail)` exactly, e.g. `M=(1,1,1)` cut `t=0`), so this tide must select a favorable
   minimal-`a` ("gentle") binding cut or exhibit slack elsewhere — it cannot assume strict slack from the
   arbitrary minimiser `sjChargeBudget_binding` returns.

With 1 and 2 landed (`genm-sjbase`), only 3 and 4 remain; once they land,
`routeMBoxThresholdFinite_sjResolution` is sorry-free and discharges `routeMCore_threshold_lt_top`.

## Reviewer verdict
Fidelity audit (reviewer + decorrelated Codex, `d74066a1`): **PASS-WITH-NITS**. The skeleton faithfully
encodes the cert's 7-piece spec + Aoyagi §5; `jointPeelIntegral` is a correct JOINT encoding (not the
cert-proven-unsound independent-chain product); the recursion spine is sound and gap-free (`L=0` vacuous,
`L=1` base, `L≥2` step, arity drops by one); the four sorries are all genuinely-new content under correct
non-vacuous statements, final footprint exactly `{sjBoundaryPeel, sjJointResolution, sjBase1_freeMatrix}`.
`minAdm_leadWidth_mono` confirmed a genuine non-trivial residual (0/5418; 318 cases where the range-
widening beats termwise selection — so it does not chain). The one substantive nit (strict-subordination
prose overclaim) is corrected above and in the module docstrings; the Lean statement was already sound
(`≤`). `sjRunMin_antitone` confirmed honestly caveated (coarse consequence, not the matrix invariant).

## Instrument caveat
The statements transcribe the design cert's 7-piece spec (3 decorrelated passes + Codex xhigh) and
Aoyagi §5; the numeric grounding of the charge budget / subordination / leading-width monotonicity is
`/tmp/sj_check.py` (exact, `minAdmRec == brute-force minAdm` 0/3000; `a(t*) ≤ minAdm M ≤ minAdm(tail)`
0 violations, non-strict — strict fails at 84/3875 `a>0` cuts). The analytic pieces (3, 4/5/7) are the
box-integral-level contracts; their internal `(S,J)` carrier (`diag(b)·[E_J|D_J]·∏C^{(s)}`) is the
mountain's core definitional work, deferred — `SJState`/`sjRunMin` are the minimal stubs the invariant
is stated over.
