# recon-map — Lane 2 (native product-corank engine) banked-substrate map

**Seat:** self-recon (read-only INTERNAL reconnaissance), aoyagi-full endgame, `genm-l2recon`.
**Date:** 2026-07-17. **NO Lean edits, NO build.** Docs read on `origin/expedition/aoyagi-full`; Lean read
via `git show origin/genm-integration:<path>` (canonical @4c2eb5779). Purpose: so the Lane-2 engine spec
names banked pieces, not blind.

**What Lane 2 is.** The operator has commissioned a dedicated engine to build the **NATIVE analytic
resolution** that fills the socket `cited_aoyagi_product_corank` — the min-corank ≥ 2 product-corank /
joint-Vandermonde box-finiteness. This is Aoyagi's WORKED-OUT DLN log-resolution (Entropy 2013, App. C,
Step 1 (i)–(v)) to be **TRANSCRIBED**, not re-invented. It goes BEYOND the current mint footprint: the
endgame (LATE-101) ships `(□)` with `cited_aoyagi_product_corank` carried as a box-level `Prop` hypothesis
(`RouteMSJDecoratedPeelStep`); Lane 2 replaces that carried cite with a native proof, so the terminal
statement of the engine must **BE** that Prop.

**Head:** the OUTER recursion, the free-block C-integration, the two wings, and min-corank ≤ 1 are
richly banked and clean-three (§A–§G, class (i)/(iii)). The NATIVE min ≥ 2 engine's genuinely-new heart
— the recursive branch-selected chart family + the transverse-Jacobian `> −1` sign repair across
shared-tail rank strata — is **NOT banked** and is what the engine must construct (§H). The pointwise
inner-peel atoms EXIST but are SCOPED to the PosDef-Gram stratum and must be lifted to measure-level on the
rank-deficient locus (§iv, the atom trap). Do NOT route min ≥ 2 through any single-factor / cornerComparator
/ corank-Gram path (§DEAD).

---

## 0. The socket — the engine's terminal statement (VERBATIM)

`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDecoratedPeelStep.lean:70`, `#print axioms`-visible in the type
(not a global axiom; the mint stays `[propext, Classical.choice, Quot.sound]`):

```
def cited_aoyagi_product_corank : Prop :=
  ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (_ht : 1 ≤ t) (_ht2 : t ≤ min (M 0) (M 1))
    (_hcork : 2 ≤ min (M 0 - t) (M 1 - t))                 -- ★ the min-corank ≥ 2 joint stratum
    (κ : Fin t ↪ Fin (M 1)) (c' : NNReal)
    (_hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (_hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M'),
    (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
            ENNReal.ofReal ((freedSchurLoss x Γ
              ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-(c' : ℝ)))) < ⊤
```

Read: the **freed-Γ triple integral** (outer tail `A'` × outer front `x = (P,B₁₂,C)` × free corank block
`Γ`) is finite below the geometric threshold `c' < ½·minAdm M`, at a cut whose corank block is `a×b` with
`a = M₀−t ≥ 2` and `b = M₁−t ≥ 2` (both factors drop ⟹ genuine joint incidence). `ρ` was DROPPED
(precision.md 1.1.3 — the freed integrand uses only `κ`, via `blockSplitEquiv κ`). `hIH` is the one-shorter
PLAIN box-IH: the engine cites ONLY the product-corank step; deeper reduced chains stay native.

**How it plugs in** (all banked, sorry-free at genm-integration):
`innerCorankDescent_lt_top` (`:75`, `by_cases 2 ≤ min(M₀−t,M₁−t)`: min≥2 → `exact hcited …`; min≤1 → native
sorry, satred's dispatch) → `gammaPeelIntegral_lt_top_of_descent` (`:118`) → `decoratedPeelStep_proof`
(`:143`) : `DecoratedPeelStep` → banked driver `routeMBoxThresholdFinite_of_decoratedPeel`
(`RouteMSJDecoratedRec:99`) → `(□) = ∀M, RouteMBoxThresholdFinite M` → mint. **The engine's job is to
DISCHARGE `cited_aoyagi_product_corank` natively** (or, equivalently, to fill the min≥2 arm of
`innerCorankDescent_lt_top` directly with a native proof in place of `exact hcited …`).

---

## 1. The resolution structure the engine must CONSTRUCT (from prodcorank-cert + decstep-cert)

Both certs (`threads/genm-prodcorank/prodcorank-cert.md`, `threads/genm-decstep/decstep-cert.md`, 8 rounds)
converge: the min≥2 atom is (the DLN specialisation of) Aoyagi's **recursive blow-up with branch-selection**.
The engine must build four coupled pieces:

1. **Recursive branch-selected chart family.** Aoyagi App. C Step 1 is a recursive blow-up inductive over
   `s`, with a branch-selector `k(s) ∈ {1,…,N}` and coordinate changes via his Thm 2 (deepest singular
   point) + Thm 3 (add variables). The DLN specialisation: per outer cut `t`, stratify the shared-tail rank
   `r` (and the deeper-product rank `k`), select the branch, and recurse. The residual `frobSq([C|Γ]·Q)`
   after Schur-weld is a genuine DLN sub-chain `(a, t+b, q)` (free front `[C|Γ]`) — self-similar, an instance
   the arity-IH `hIH` handles ONE LEVEL DOWN (decstep round-2 §2; sub-chain cut-soundness
   `minAdm(a,b,n') ≤ (a−s)(b−s) + minAdm(s,n')` verified 324/324, round-4 §1).
   **Lexicographic termination** `(chain arity, corank c)`: outer peel shortens the chain; inner rank
   resolution shrinks the Gram (`c → r < c`); bottoms at the width-2 leaf.

2. **Monomial normal forms.** Resolve the `c×c` corank Gram to a monomial × unit via a FULL multi-singular-
   value (SVD) determinantal blow-up — `d = c` exceptional coordinates, NOT a single radial coordinate
   (which resolves only `Γ=0`, not the rank-`1..c−1` cone — decstep round-3 §3, PROVEN gap). The terminal is
   the weighted-monomial integral closed by `sjLoss_terminal_lintegral_lt_top` (§G).

3. **Finite-cover glue.** Front-block determinantal atlas (per-minor charts) + shared-tail rank-sector cover,
   glued by `lintegral_lt_top_of_finite_cover` / `_finset_cover` (§A). Index-completeness (every point in some
   chart) is Lean labor over banked math.

4. **Threshold invariance (the crux).** The per-stratum threshold must be `≥ c* = ½·minAdm` at EVERY stratum,
   with no smaller-ratio divisor. **Arithmetic side: AIRTIGHT and banked** — `T_m ≥ c*` all strata via the
   `minAdm` recursion (QIP family, §F; verified n=3..15). **Analytic side: the surfaced sub-gap** — the
   transverse-Jacobian must EQUAL the stratum codim `A_r` and REPAIR the naive `k−n` exceptional exponent to
   `> −1` uniformly across shared-tail rank strata (decstep round-4/5, `GAP-IN-RELATIVE-JACOBIAN`). Because
   `Q̃ₚ, Q_b` are shared deeper PRODUCTS, the free-matrix determinantal resolution pulls back NON-submersively,
   so the naive `m²` (submersive) codim is not automatically preserved — establishing that the iterated peels
   principalize the joint incidence (discrepancies genuinely `≥ c*`) IS the transcription's hard content. The
   circularity guard: one CANNOT use "rlct = c* (Aoyagi) ⟹ no smaller-ratio divisor" inside the native proof.

**The kill-guards the engine must honor** (§DEAD): single-factor peels do NOT close min≥2; carry the PIVOT
Gram not the corank Gram; never integrate Γ free at min≥2 (overshoot); always carry `|det J|`; the pivot-Gram
gate is top-stratum only.

---

## 2. Substrate survey — the seven classes

Legend for classification:
(i) **reusable-as-is** · (ii) **needs generalization** (says what) · (iii) **staged-for-exactly-this**
(banked in anticipation of the resolution engine) · (iv) **DEAD/ruled-out to AVOID**.
Axiom status: **clean-three** = `[propext, Classical.choice, Quot.sound]`; confirmed for the AxCheck-emitted
set (`AxCheck.lean`; its header note: docstrings claiming a "cited axiom" are SUPERSEDED — trust the emitted
`#print axioms`). `∀-general` vs `scoped` per the signature.

### §A. Measure bedrock (Core / Foundations: lintegral, Fubini, cover, measurable-set, pushforward)

| lemma | file:line | signature core | axiom | generality | class |
|---|---|---|---|---|---|
| `lintegral_lt_top_of_finite_cover` | `Validate/RouteMSJIncidenceGluing.lean:28` | `[Fintype ι] (C : ι→Set α)(D)(f) (hcover: μ(D\⋃C i)=0)(hfin: ∀i, ∫⁻_{C i} f <⊤) → ∫⁻_D f <⊤` | clean-three | ∀-general (any `α`,`μ`,`f`) | (i) — THE finite-cover glue |
| `lintegral_lt_top_of_finset_cover` | `…Gluing.lean:42` | `Finset`-indexed variant (charts = a finite set of minors) | clean-three | ∀-general | (i) — the per-minor atlas glue |
| `cover_integral_lt_top_iff` | `Foundations/S1Cover.lean:32` | Finset-cover ⟺ each cell finite | clean-three | ∀-general | (i) |
| Fubini/Tonelli + MP wrappers | `Foundations/S1Fubini.lean` | `finPeel_mp` (:101), `chartN_mp` (:113), `core_int_of_joint_int` (:401), `joint_admissible_of_split` (:445), `rlctAtOn_comp_homeomorph` (:54) | clean-three | ∀-general | (i) — the joint↔iterated + MP-homeomorph plumbing |
| polynomial-zero-set null | `Core/MeasureTheory/PolynomialZeroSet.lean` | a.e. genericity discharge (nonvanishing poly ⟹ null complement) | clean-three | ∀-general | (i) — for the a.e. rank/energy hyps |

Note: the socket integral is a TRIPLE `∫⁻ A' ∫⁻ x ∫⁻ Γ`; the engine reorders/peels these with the S1Fubini
MP wrappers. `paramsBoxM` (`RouteMBoxReduction:56`), `genBox` (`RouteMSJBlockReindex:140`), `outerDom`
(`RouteMSJChartShear:185`), `matBox` (`MatMulFibre:46`), `SJOuter`/`schurShift` (`RouteMSJChartShear`),
`blockSplitEquiv` (`RouteMSJBlockReindex:236`) are the box/measure-space defs the socket names.

### §B. Change-of-variables (matrix-space CoV, MeasurePreserving .comp, the rightMulₚ kit)

| lemma | file:line | signature core | axiom | generality | class |
|---|---|---|---|---|---|
| `rightMulₚ` (def) | `Validate/RouteMSJGammaAtom.lean:39` | `(p)(M : Matrix (Fin q)(Fin q) ℝ) : (Fin p→Fin q→ℝ) →ₗ (Fin p→Fin q→ℝ)`, row-wise `Γ i ↦ Γ i ᵥ* M` | clean-three | ∀-general | (i) |
| `det_rightMulₚ` | `…GammaAtom.lean:54` | `LinearMap.det (rightMulₚ p M) = (det M)^p` | clean-three | ∀-general | (i) — the CoV Jacobian |
| `lintegral_comp_rightMulₚ` | `…GammaAtom.lean:74` | `det M≠0 → ∫⁻ Γ, g(Γ·M) = ofReal(|det M|^p)⁻¹ · ∫⁻ Γ, g Γ` | clean-three | ∀-general (any measurable `g`) | (i) — right-mult CoV (Haar) |
| `sjGoodChartLoss_pivotRows_translate_eq` | `Validate/RouteMSJPivotTranslate.lean` | translation-shear MP (`measurePreserving_add_right` + `setLIntegral_comp_preimage_emb`) | clean-three | scoped to the goodChart loss | (i) |
| `rightMulLin` + rank/range kit | `Core/Matrix/…` / `RouteMSJ…` (see grep) | `rightMulLin_injective_of_rank_eq_height`, `range_rightMul_eq_of_factor`, `finrank_range_rightMul` | clean-three | ∀-general | (i) — for the injective-block CoV |
| big-cell shear CoV | `Validate/RouteMSJIncidenceChart5BigCell.lean:110` `chart5_bigcell_cov` | `W₂₂↦E`-shear Lebesgue-preserving (Jac ≡ 1); `chart5_rank_le_iff_reassembled` (:145) puts rank-drop at `{E=0}` | clean-three | scoped (front block) | (iii) — the unit-Jacobian Schur chart |

The "dbuild rightMulₚ kit" the commission named IS `rightMulₚ` + `det_rightMulₚ` + `lintegral_comp_rightMulₚ`
(GammaAtom) — the invertible right-multiplication CoV for the free corank block, with the exact reciprocal
Jacobian. No LQ/QR CoV as a named theorem was found; the eigen/SVD frame (§E) plays that role.

### §C. Monomial thresholds / radial (critical-power, ball-integrability, log-boundary)

| lemma | file:line | signature core | axiom | generality | class |
|---|---|---|---|---|---|
| `radial_ball_iff` | `Foundations/S1SmoothBlock.lean:78` | `IntegrableOn (‖x‖^s) (ball 0 R) ⟺ −(m+1) < s` (the critical-power dichotomy) | clean-three | ∀-general (`EuclideanSpace (Fin (m+1))`) | (i) — the radial threshold |
| `euclidND_ball_integrable` | `Foundations/S1RadialMorse.lean:46` | `c' < (m+1)/2 → IntegrableOn (‖y‖^{−2c'}) (ball 0 R)` | clean-three | ∀-general | (i) |
| `sumSqND_box_lt_top` | `…S1RadialMorse.lean:67` | `c' < (m+1)/2 → ∫⁻_{morseBox} (∑xᵢ²)^{−c'} <⊤` (the FreeBilinear leaf) | clean-three | ∀-general | (i) |
| `radial_morse_dominates_lt_top` | `…S1RadialMorse.lean:127` | Morse residual domination, `c' < (m+1)/2` | clean-three | ∀-general | (i) |
| `radial_morse_residual_power_le` / `_absZ_le` | `…S1RadialMorse.lean:157` / `RouteMSJ…` | the ABOVE-critical `(m+1)/2 < c'` regime (residual power) | clean-three | ∀-general | (i) — the other regime |
| `corner_block_cube_lintegral_lt_top` | `Validate/RouteMSJRadialPolar.lean:257` | `g` deg-2-homog + `hlb` unit-sphere floor `a>0` + `c' < n/2` → `∫⁻_{[-1,1]ⁿ} (g z)^{−c'} <⊤` (+ `_of_pos`, `_of_injective`) | clean-three | ∀-general (`g` abstract) | (iii) — `rlct = codim/2` realized; the radial engine |
| `lintegral_Ioc_rpow_lt_top`, `lintegral_ball_radial_polar_factor`, `corner_block_lintegral_le` | `…RouteMSJRadialPolar.lean:157/112/…` | 1-D `∫₀^δ r^{…}dr` + polar factorization + EuclideanSpace form | clean-three | ∀-general | (i) |
| `twoBlock_radial_le` / `twoBlock_radial_scale_le` | `Validate/RouteMSJTwoBlockRadial.lean:235` (AxCheck :1071) | two-radius corner (retains `‖Y·W‖²` coupling) | clean-three | scoped (2-block) | (i) — the bilinear corner |
| `monomialThreshold` (def) + `monomialIntegrand`, `unitBox`, `monomialOrder`, `axisRatio` | `RLCT/Skeleton.lean:88` | `sSup` of integrable-exponent down-set of `(∏|uⱼ|^{hⱼ})·(∏|uⱼ|^{2kⱼ})^{−c}` | clean-three | ∀-general | (i) — the β-clause threshold (NOT a radial; separate object). `monomial_rlct` axiom RETIRED 2026-07-09 |

**Key note:** there is NO general `monomial_rlct` theorem and none is needed for FINITENESS — finiteness is
native via the radial blow-up. `monomialThreshold` is the decorated comparator's β/axisRatio admissibility
clause, a distinct object.

### §D. Gamma / Wishart atoms (det-Gram lintegral, qbox finiteness, rectCore ∀T)

| lemma | file:line | signature core | axiom | generality | class |
|---|---|---|---|---|---|
| `qbox_lintegral_lt_top` | `Validate/RouteMSJQBoxCore.lean:113` | `b≤q → a < q−b+1 → ∫⁻_{Q∈ball^b} (gram Q).det^{−a/2} <⊤` (induction on `b`) | clean-three | ∀-general | (i) — the Wishart one-shot |
| `detGram_lintegral_lt_top` | `Validate/RouteMSJProductTube.lean:322` | `r≤n → a < n−r+1 → ∫⁻_{X∈matBox r n 1} (X·Xᵀ).det^{−a/2} <⊤` | clean-three | ∀-general | (i) |
| `detGram_lintegral_box_lt_top` | `Validate/RouteMSJOffSectorBPos.lean:68` | box form, `r≤n` | clean-three | ∀-general | (i) |
| `det_gram_cons`, `gramDet_eq_prod`, `detGram_eq_prod_rows`, `borderedGram_det` | `RouteMSJ…` (AxCheck :1046/1221/1227/1217) | Gram determinant recursion / product identities | clean-three | ∀-general | (i) — the det-Gram algebra |
| `rectCore_schurGen_lt_top` | `Validate/RouteMSchurRect.lean:115` | `RectSchurThreshold p lam → RectSchurRecStep p lam → ∀m n c'<lam m n, RectSchurCore m n p c' T` (strong induction on `min m n`) | clean-three | ∀-general (∀T) | (iii) — the rectangular rank-stratified Schur recursion driver |
| `corankBlock_morsePeel_setLE` | `Validate/RouteMSJCorankPeel.lean:88` | `(Qb·Qbᵀ).PosDef → pq/2<c' → w>0 → ∫⁻_{Γ∈s}(w+frobSq Apiv+frobSq(Ccross+Γ·Qb))^{−c'} ≤ det(Qb·Qbᵀ)^{−p/2}·Cresid·(…)^{−(c'−pq/2)}` | clean-three | **scoped: `PosDef` Gram** | (ii)/(iv) — full-rank stratum only; see atom trap §DEAD |
| `corankOffSector_*`, `corankWeight_*` | `Validate/RouteMSJOffSector*` (AxCheck :1195–1206) | b=1 / b>0 / borderline off-sector corank bounds | clean-three | scoped (per-b) | (i) |
| `corank_survival_ae`, `posDef_gram_of_rank_eq`, `exists_gram_sub_smul_one_posSemidef_of_rank_eq` | `RouteMSJCorankGeneric` / `RouteMSJRayleigh` (AxCheck :1150/1157/1156) | a.e. Gram PosDef from threaded rank; PosDef from rank-eq | clean-three | ∀-general | (i) — the a.e. genericity discharge |
| `Cresid` (def) | `Validate/RadialResidualPower.lean:39` | the corank-peel residual constant | clean-three | ∀-general | (i) |

### §E. Eigendecomposition / SVD (Mathlib + our layer)

| lemma | file:line | signature core | axiom | generality | class |
|---|---|---|---|---|---|
| `measurableEigendecomp` | `Validate/RouteMSJMeasurableEigendecomp.lean:88` | `Measurable A → (∀z,(A z).IsHermitian) → Measurable eigenvalues₀ ∧ ∃ U measurable, Uᵀ U=1, A z = U·diag(λ)·Uᵀ` | clean-three | ∀-general (any measurable Hermitian family) | (iii) — the SVD/spectral frame, banked for the determinantal blow-up |
| `measurableEigenvalues₀`, `exists_measurableEigenframe`, `frame_diagonalizes` | `RouteMSJMeasurableEigenframe.lean` (AxCheck :1269/1272) | measurable ordered eigenvalues + orthonormal frame | clean-three | ∀-general | (iii) |
| ordered-roots measurable | `Validate/RouteMSJOrderedRootsMeasurable.lean` | measurable ordered roots of char. poly | clean-three | ∀-general | (iii) |
| `frobSq_mul_eq_sum_eigenvalues` | `Validate/RouteMSJFrontSpectral.lean:94` | `frobSq(A₀·P) = ∑ⱼ eig(P·Pᵀ)ⱼ·∑ᵢ((A₀·eigvec)ᵢⱼ)²` | clean-three | ∀-general | (i) — Rayleigh expansion of the loss |
| `sigMin_sq_eq_iInf_eigenvalues` | `…RouteMSJFrontSpectral.lean:141` | `sigMin P² = ⨅ᵢ eig(P·Pᵀ)ᵢ` | clean-three | ∀-general | (i) — the σ_min floor |
| `gram_rayleigh_lb` | `Validate/RouteMSJRayleigh.lean:37` | Gram Rayleigh lower bound | clean-three | ∀-general | (i) — the `hlb` unit-sphere floor tool |
| `rayleigh_expansion`, `pivotBlock_radial_blowup`, `transverseSchurGram` | `RouteMSJKyFan`/`RouteMSJ…` (AxCheck :1259/1262/1283) | Hermitian Rayleigh + pivot-block blow-up + transverse Schur Gram | clean-three | ∀-general | (i)/(iii) |

**This is the SVD substrate the min≥2 engine's determinantal (multi-singular-value) blow-up rests on** — the
measurable eigenframe is banked; what is NOT banked is the `c`-coordinate exceptional-divisor CoV built ON it
(§H). Mathlib supplies the spectral theorem for Hermitian matrices; our layer adds MEASURABILITY of the frame
(the load-bearing addition for the measure-level resolution).

### §F. The QIP family (minAdm recursion — arithmetic backbone)

| lemma | file:line | signature core | axiom | generality | class |
|---|---|---|---|---|---|
| `minAdm_le_inf_pivot_qip` | `Validate/RouteMSJCorankRec.lean:239` | `minAdm M ≤ inf'_{u'≤min(M₀,M₁)}[(M₀−u')(M₁−u') + u'·deepTailMin M]` | clean-three | ∀-general (`Fin(L+1+1+1)`) | (i) — the interior QIP bound |
| `minAdm_le_head_mul_min_deepTailMin` | `…RouteMSJCorankRec.lean:159` | `minAdm M ≤ M₀·min(M₁, deepTailMin M)` | clean-three | ∀-general | (i) |
| `minAdm_le_u_deepTailMin_add_peelCharge` (the `u·M₂+(M₁−u)M₀` interior bound) | `…RouteMSJCorankRec.lean` | interior coupled-∫ᵖ load-bearing arithmetic (3-banked-lemma composition, decorrelated 0 fails) | clean-three | ∀-general | (i) |
| `minAdm_le_peelCharge_add_redChain` | AxCheck :659; `RouteMSJ…` | `minAdm M ≤ (M₀−u)(M₁−u) + minAdm(redChain u M)` (the outer peel) | clean-three | ∀-general | (i) — the recursion step |
| `half_minAdm_sub_half_peelCharge_le`, `exists_binding_cut` | AxCheck :247/248 | the `½·peelCharge` threshold shift + binding-cut existence | clean-three | ∀-general | (i) |
| `minAdm_eq_frontPeel`, `frontCharge_ge_minAdm`, `twoVar_min_eq` | AxCheck :256/257/258 | front-peel identity + charge bound | clean-three | ∀-general | (i) |
| `minAdm_eq_cCodim`, `minAdm_comp_perm`, `minAdm_comp_sort` | AxCheck :1178/1172/1173 | `minAdm = cCodim`; permutation invariance | clean-three | ∀-general | (i) — links to the codim (C,θ) engine |
| `minAdm_mnp_eq_inf` | `Validate/RouteMSchurRect.lean:~135` | `minAdm ![m,n,p] = inf'_{t≤min(m,n)}[(m−t)(n−t)+t·p]` | clean-three | ∀-general (3-width) | (i) |
| `minAdm_redChain_succ_ge`, `minAdm_backPeel_cominimizer_ge`, `corankLeaf_rpow_lt_top` | AxCheck :1124/1143/1139 | reduced-chain monotone + back-peel cominimizer + corank leaf | clean-three | ∀-general | (i) |

**The arithmetic is airtight and complete** — every `T_m ≥ c*` threshold-invariance fact the engine needs is
a `minAdm`-recursion consequence, banked and clean-three. Verified exhaustively (decstep n=3..15; satred
0/4039). The engine's threshold-invariance PIECE #4 (§1) is arithmetic-done; only the ANALYTIC sign repair
(§H) is open.

### §G. Schur-weld / shear / freed-Γ machinery

| lemma | file:line | signature core | axiom | generality | class |
|---|---|---|---|---|---|
| `freedSchurLoss` (def) | `Validate/RouteMSJChartShear.lean:146` | `= frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b)`, `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b`; Γ INDEPENDENT | clean-three | ∀-general | (i) — the socket integrand |
| `chartInner_schurWeld_eq_of_emb` | `Validate/RouteMSJChartWeld.lean` (AxCheck :610) | pivot chart `∫⁻ frobSq(A₀·Q)^{−c'}` ⟶ Schur-block loss on `{IsUnit toBlocks₁₁}` | clean-three | ∀-general | (i) — measure-preserving weld |
| `chartInner_schurShearFree_eq` | `Validate/RouteMSJChartShear.lean` (AxCheck :630) | Schur-block loss ⟶ `∫⁻ x ∫⁻ Γ freedSchurLoss^{−c'}` (the Γ-freeing shear) | clean-three | ∀-general | (i) |
| `gammaPeelIntegral_schurShearFree_eq` | `Validate/RouteMSJFreedPeel.lean:78` | `gammaPeelIntegral M t ρ κ c' = [the freed-Γ triple integral]` (rewrites the peel into the socket form) | clean-three | ∀-general | (i) — the entry rewrite |
| `schurLoss_of_blockSplitD_symm_shift` | `Validate/RouteMSJChartShear.lean:~160` | pointwise: `schurLoss(reconstruct) = freedSchurLoss x Γ Q` | clean-three | ∀-general | (i) |
| `freedSchurLoss_inner_peel_lt_top` | `Validate/RouteMSJFreedPeel.lean` (AxCheck :640) | `ab/2<c' ∧ (Q_b·Q_bᵀ).PosDef ∧ pivotEnergy>0 → ∫⁻_{Γ∈s} freedSchurLoss^{−c'} <⊤` | clean-three | **scoped: 3 pointwise hyps** | (ii)/(iv) — see atom trap |
| `freedSchurLoss_inner_bounded_lt_top` | `…RouteMSJFreedPeel.lean` (AxCheck :641) | `0≤c' ∧ pivotEnergy>0 ∧ vol s<⊤ → ∫⁻_{Γ∈s} … <⊤` (the `c'≤a/2` bounded branch) | clean-three | scoped (bounded integrand) | (i) — the bounded arm |
| `freedSchurLoss_absorption`, `freedSchurLoss_smul` | `Validate/RouteMSJDecoratedPeelCore.lean:41/64` | scaling/absorption identities | clean-three | ∀-general | (i) |
| `gammaAtom_aniso_shifted_eq` | `Validate/RouteMSJGammaAtom.lean:142` | `(R·Rᵀ).PosDef ∧ pq/2<c' ∧ w>0 → ∫⁻ Γ (w+frobSq(Γ·R+S))^{−c'} = det(R·Rᵀ)^{−p/2}·Cresid·(w+frobSq(S·Π))^{−(c'−pq/2)}`, `Π = 1−Rᵀ(R Rᵀ)⁻¹R` | clean-three (consumed by AxCheck'd peel) | **scoped: `PosDef` Gram** | (ii)/(iii) — the C-integration → PIVOT Gram (c-agnostic: `S` general shift) |
| `SJLinGenState` (carrier) | `Validate/RouteMSJLinGen.lean:100` | `structure (ζ ν ι)(d)`; `residual`/`gen`/`loss`/`ofMatrix`/`radialStep`/`rowMix` + `gen_radialStep`, `loss_rowMix`, `gen_rowMix_const` | clean-three | ∀-general | (iii) — the non-terminal linear-generator carrier for the descent |
| `sjLoss_terminal_lintegral_lt_top` | `Validate/RouteMSJLedger.lean:234` | `0<c' ∧ (support = sharedDivisorExp) ∧ c' < monomialThreshold d k h → ∫⁻_{unitBox} (sjLoss e u)^{−c'}·∏|uℓ|^{hℓ} <⊤` | clean-three | ∀-general | (iii) — the MONOMIAL terminal the resolution descends to |

**This class is the spine of the engine's plumbing** — the weld, the shear, the entry rewrite, the carrier,
and the monomial terminal are ALL banked and clean-three. The freed integral, its box domains, and the
descent-to-terminal machinery exist. What is missing is the min≥2 descent CONTENT (§H), and the scoped atoms
(`freedSchurLoss_inner_peel_lt_top`, `gammaAtom_aniso_shifted_eq`) apply only where the Gram is PosDef.

---

## 3. §DEAD — ruled-out routes the engine must AVOID (each with its refuter)

- **(iv) The ATOM TRAP — carry the PIVOT Gram, NEVER the corank Gram.** Integrating Γ free after C to get
  `det(Q_b·Q_bᵀ)^{−a/2}` needs `(Q_b·Q_bᵀ).PosDef`, which FAILS on the rank-deficient corank locus — the
  very min≥2 joint incidence. Gate `a < q−b+1` becomes `a < a` = FALSE at edge dims ⟹ divergent. The correct
  jac is the PIVOT Gram `det(Q̃ₚ·Q̃ₚᵀ)` (full rank `u`, `qbox`-disposable), via `gammaAtom_aniso_shifted_eq`
  + `qbox_lintegral_lt_top`. (decstep round-3 §Q2-correction; `RouteMSJDecorated` docstring "atom trap".)
  ⟹ `corankBlock_morsePeel_setLE` / `freedSchurLoss_inner_peel_lt_top` are SCOPED to the PosDef stratum only;
  the rank-deficient strata are the genuinely-new content, NOT these atoms.

- **(iv) Single-factor / naive-`m²` transversality at min≥2 — UNSOUND.** A single-factor peel (resolve Γ's
  rank, or the tail `S = Q_b(I−P)` alone) does NOT principalize the JOINT ideal `Γ·S`: the joint center
  `{Γ·S=0}` (the `(x,y,b)` Vandermonde alignment center) SURVIVES, product codim `C_k = k²−⌊k²/4⌋ < k²`.
  The naive `m²` per-stratum threshold PASSES the arithmetic but is NOT the established discrepancy; paired
  with the product `C_m` it UNDERSHOOTS (`(4,4,4,4)`, m=2: `3/2+7/2 = 5 < 11/2 = c*`). (prodcorank-cert §3/§4,
  Gröbner-verified `I(PZ)=(x,y,b)` at n=2,k=2; decstep round-5 discriminator n=4..7.)

- **(iv) Single radial coordinate for a `c×c` corank block, `c≥2` — resolves only `Γ=0`.** One radial
  coordinate does NOT resolve the rank-`1..c−1` cone; the angular quadratic on the exceptional divisor is
  NON-coercive. Need the FULL multi-singular-value (SVD) blow-up, `d=c` exceptional coords. (decstep
  round-1 §3 / round-3 §3, Codex `GAP-AT-CORANK-2` PROVEN for a single radial blow-up.)

- **(iv) Pointwise inner-peel — must be a MEASURE statement.** The three interface hyps of
  `freedSchurLoss_inner_peel_lt_top` (`ab/2<c'`, `Q_b·Q_bᵀ` PosDef, pivotEnergy `>0`) FAIL pointwise on the
  corank locus and must be supplied a.e. / measure-level by the outer descent, not pointwise. A.e. positivity
  is NOT integrability (arch1probe Q-A correction) — integrability rides the DESCENT onto the shorter-chain
  IH. (socket docstring; RouteMSJFreedPeel.)

- **(iv) `cornerComparator` flat domination — L≥1-UNSOUND.** The `Z=t·Z₀` static single-product comparator
  cannot dominate the sum-form weld `C'·B₀ + Γ·Q_b`; unsound for L≥1. (decstep round-1 §4(a): "NOT the flat
  `cornerComparator` domination which is L≥1-UNSOUND".) NOTE: `cornerComparator` itself is a banked
  admissible-reduced-comparator witness (`RouteMSJCornerComparator`, clean-three) for the OLD decorated route
  — but it is NOT a min≥2 domination tool; the decoration route it served was SIMPLIFIED AWAY (decstep
  round-6/7). Do not revive it for the min≥2 atom.

- **(iv) Radialize-and-drop the Jacobian.** The odd-cycle "deficit" is a coordinate artifact of a
  non-unit-Jacobian radialising chart that dropped `|det J|`. Keep the Schur charts atomic (unit-Jac,
  `chart5_bigcell_cov`); if a radialising chart is unavoidable, carry its `|det J|` weight. The transverse
  Jacobian `|det J| = A_r` codim IS the sign repair — dropping it is the divergent route. (seamrlct §10;
  decstep round-4 §4 KILL-guard 3.)

- **(iv) `shellSpine_le_hsQ_box`, headSplit route-B (`deeperFlag_shell_le` via `headSplit_pivotDom`).** FALSE
  on narrow tail (routefork refuter `(3,3,3)`, t=j=1, c'=4); the route-B `shell_corankOffSector_le_unif` fill
  is a genuine type error (no `A_cor`-free lower bound). (tideDrecon §6 DEAD list.) Not the min≥2 route.

- **NOTE (superseded, not dead): the DECORATION apparatus.** `DecoratedStepHyp` / `DecoratedDescent` /
  FaithfulSJAt flag-`γ'` were the pre-round-6 vehicle for carrying the min≥2 Gram weight; the cite made them
  UNNECESSARY and they are DEAD vocab (decstep round-6/7, LATE-79/98). The PLAIN route
  (`DecoratedPeelStep` → `routeMBoxThresholdFinite_of_decoratedPeel`) is the live driver. The engine fills
  the socket's min≥2 arm; it does NOT revive the decoration. (Only `decoratedBoxThresholdFinite_trivial_iff`,
  the π=∅ recovery = plain box, survives.)

---

## 4. Net gaps — what the engine must BUILD (not banked)

Everything below the socket-level Prop that is NOT in §A–§G:

1. **§H (the heart) — the recursive branch-selected chart family for the `c×c` (c≥2) corank block + its
   monomial normal form + the transverse-Jacobian `> −1` sign repair, UNIFORM across shared-tail rank
   strata.** This is `GAP-IN-RELATIVE-JACOBIAN` (decstep round-5): proving the transverse (SVD-determinantal)
   Jacobian EQUALS the stratum codim `A_r = (corank-at-deepened-cut)²` and raises the naive `k−n` exceptional
   exponent above `−1`, for the shared DEEPER-PRODUCT (non-submersive) `Q̃ₚ, Q_b` — not free matrices. This
   is the DLN transcription of Aoyagi App. C Step 1 (i)–(v). Builds ON the banked measurable eigenframe (§E)
   and the radial engine (§C), but the `c`-coordinate exceptional-divisor CoV + its Jacobian bookkeeping are
   NEW. Care-point (decstep round-5 §4): charge = `(corank at the deepened cut)² = peelCharge(M,u')`, NOT the
   mislabeled `(b−r)²` — bake as a kill-condition.

2. **The relative principalization of `(Q̃ₚ, Γ·Q_b)`.** The residual `Q_b^⊥ = Q_b·(I−P_{Q̃ₚ})` is COUPLED to
   the pivot tail (`Q_b^⊥·Q̃ₚᵀ = 0` identically) — a RELATIVE, not absolute, principalization. Its pushforward
   must be a finite sum of shifted PLAIN reduced-chain integrals (closed by `hIH`), with exceptional powers
   checked `> −1`. (decstep round-4 §3 `GAP-AT-PROJECTED-TAIL-PRINCIPALIZATION`.)

3. **The finite-cover index-completeness** (every point of the corank locus in some branch chart) — Lean
   labor over the banked `lintegral_lt_top_of_finite_cover` (§A).

4. **The measure-level supply of the three inner-peel hyps** on the PosDef stratum + the recursion into the
   rank-deficient strata (the `{rank Q_b<c}` cells drop to lower-`r` terms of the stratification). This is the
   bridge from the pointwise atoms (§G, scoped) to the measure statement.

**Everything else the engine touches is banked and clean-three:** the outer peel + weld + shear + entry
rewrite (§G), the free-block C-integration on the PosDef stratum (§B/§G `gammaAtom_aniso_shifted_eq`), the
pivot-Gram disposal (`qbox`, §D), the radial/monomial terminals (§C/§G), the whole `minAdm` arithmetic
backbone (§F), the measurable eigenframe (§E), and the finite-cover glue (§A). The min≤1 native arm and the
two wings (satred's dispatch) are separate and also mostly banked.

---

## 5. Close (reflection)

- **Most likely to ADVANCE the engine:** the banked **measurable eigenframe** (§E, `measurableEigendecomp`)
  + the abstract **radial engine** (§C, `corner_block_cube_lintegral_lt_top`, `g`/`hom`/`hlb`) + the
  **monomial terminal** (§G, `sjLoss_terminal_lintegral_lt_top`) + the **finite-cover glue** (§A). These are
  exactly the pieces the SVD-determinantal blow-up + normal-form + glue want; the engine's real work is the
  `c`-coordinate exceptional-divisor CoV that connects the eigenframe to the radial/monomial terminal.
- **Most likely to BREAK the build:** the §H transverse-Jacobian `> −1` sign repair under the NON-submersive
  pullback (shared deeper products, not free matrices). The arithmetic (`min = minAdm`, all strata ≥ c*) is
  airtight; the ANALYTIC transversality is the deep heart, and it is where every prior round surfaced a gap.
  The atom trap (§DEAD) is the recurring failure mode — any spec that carries the corank Gram, or treats
  `freedSchurLoss_inner_peel_lt_top` / `gammaAtom_aniso_shifted_eq` as applicable off the PosDef stratum, is
  unsound.
- **The one framing correction the engine spec must carry:** the certs (prodcorank + decstep round-6)
  ADJUDICATED this atom as a CITE (Aoyagi's wall, research-grade, "a multi-tide monument, not a peel — scope
  it as its own expedition"). Lane 2 is precisely that expedition: a NATIVE TRANSCRIPTION of Aoyagi's
  worked-out resolution. The engine is not detail-at-scale; the spec should treat §H as the genuinely-new
  theorem and concentrate the soundness review there, with the banked substrate (§A–§G) as consume-not-derive.

**Files (absolute):**
- this map: `/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/genm-l2recon/recon-map.md`
- socket: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDecoratedPeelStep.lean:70` (`cited_aoyagi_product_corank`), `:75` (`innerCorankDescent_lt_top`)
- certs: `…/threads/genm-prodcorank/prodcorank-cert.md`, `…/threads/genm-decstep/decstep-cert.md` (8 rounds)
- axiom ledger: `lean/DLNFibre/DLN/RLCT/AxCheck.lean` (emitted `#print axioms` for the load-bearing set)
- prior recon (superseded route, still useful for radial/chart substrate): `…/threads/genm-tideD-recon/recon-map.md`, `…/threads/genm-arch1probe/arch1-cert.md`
- Aoyagi source: `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/entropy-15-03714.pdf` (recursive blow-up App. C Step 1 (i)–(v))
