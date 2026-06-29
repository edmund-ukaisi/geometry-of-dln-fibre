# D1 IFT-chart producer — BUILD-READY SPEC (obligation (i), L = 2)

**For: a fresh worktree-isolated `lean-formaliser`.** This is the SINGLE remaining D1 (★) obligation.
Everything upstream (the engine, the wiring, the residual-core interface, the kill-condition + design
adjudications) is BANKED clean-three. Your job: construct the constant-`nReg` chart at a **general**
optimal `v` and supply its outputs to the banked consumers, landing the D1 per-point `≥` leg
`rlctAt_deepest_le_of_optimal` (Skeleton:1172) at L = 2.

**★ READ §SEL FIRST — the CHOSEN ROUTE is the SELECTED-MINOR IFT quasi-split (the LIGHTER existing-engine
path; `hcmp` HOLDS, directed-exact verified, NO new Mathlib lemma, NO Morse-Bott S4).** Route history (do
NOT re-explore): the exact clean-square chart is WALLED (§★ Test 1) and the per-layer-Schur squeeze FAILED
the kill-condition (§★ Test 2) — but the SELECTED-MINOR quasi-split (full coupled residual, NOT per-layer
Schur) PASSES because `R=Q(0,·)` is definitionally `F`'s own residual slice (§SEL). The Morse-Bott design
(§MB) is the FALLBACK, kept build-ready but NOT needed. The banked-consumer routing (§2) + reductions
(§4–6) stand.

---

## §SEL. ★ CHOSEN ROUTE — selected-minor IFT quasi-split (the LIGHTER path; hcmp HOLDS, directed-exact)

The verify-first-the-cheaper-route check (aa5395, DIRECTED-EXACT on the squeeze's exact failure locus +
decorrelated Codex hypothesis-withheld) came back **hcmp HOLDS** — D1's chart is the existing
`rlct_quasiSplit_ge` path, NO new Mathlib lemma, NO Morse-Bott operator recursion.

**The chart:** pick the `nReg` independent gradient minors of `F = dlnLoss` at `v` (the 5 regular
directions at L=2), IFT-straighten them to coords `s` (so the 5 selected residuals `g_E = s` exactly),
and set `Q(s,t) := ∑_{remaining ij} g_ij(chart(s,t))²` — the FULL coupled residual (NOT the per-layer
Schur). Then `F = ∑ s² + Q`, `R(t) := Q(0,t)`.

**Why it beats the squeeze (the structural reason, not coincidence):** `R(t) = Q(0,t)` is DEFINITIONALLY
the slice of `Q` (the Lean `hR : ∀ t, R t = Q(0,t)`), and `Q` KEEPS the inter-layer coupling
`(T₂)₂₁·Y₁·Z₁` the per-layer Schur DROPPED. So as `s→0`, `Q(s,t) → Q(0,t) = R(t)` by continuity ⟹
`R/(∑s²+Q) → 1`, NOT ∞. The Schur-vs-full-quartic zero-set mismatch that killed the squeeze
STRUCTURALLY CANNOT recur (the comparison object IS `F`'s own residual, same quartic).

**hcmp certificate (directed-exact at (3,3,3)/r=1 MIDDLE stratum, the squeeze's failure locus):**
- On `{E=0}` (the old λ-arc): `hcmp` is `R ≤ C·R` — TRIVIAL (the Schur's λ=1/λ=2 blow-up cannot recur).
- OFF `{E=0}`: every numerator monomial of `q(s,t) − q(0,t)` is divisible by some `s_j` (verified
  `(q−q(0,t))|_{s=0}=0`), `D(0)=1` bounded away from 0 ⟹ `(q_a(s,t)−q_a(0,t))² ≤ L²·∑s²` — exactly
  `coupled_controls_slice`'s `hlip` shape. Explicit on the `1/10` box: `L ≤ 0.425`, `C = 2L²+2 ≤ 2.36`.
- WORST-CASE ARC (constructed DIRECTLY, not sampled): full cancellation `q(s,t)=0` forces `s0 → −1` —
  i.e. `‖s‖ ~ 1` (ORDER ONE), OUTSIDE any small nbhd of `v`. No arc drives `Q(s,t)→0` by nonzero SMALL
  `s` while `Q(0,t)` stays positive. Codex (hypothesis-withheld) confirmed via the cleaner vector
  triangle `‖q(0,t)‖ ≤ ‖q(s,t)‖ + L‖s‖ ⟹ R ≤ 2Q + 2L²∑s² ⟹ (∑s²)+R ≤ max(2,1+2L²)(∑s²+Q)`.

**Producer obligation (the build):** build the selected-minor IFT chart (5 minors straightened via the
C^r IFT `ContDiffAt.toOpenPartialHomeomorph`), supply `hcmp` via `coupled_controls_slice` per inactive
square (or Codex's cleaner vector-triangle route); the Lipschitz `L` from
`Convex.norm_image_sub_le_of_norm_fderiv_le` on the box where `D` is bounded away from 0 (`q` is `C^∞`,
rational with nonvanishing denominator). Then `rlct_quasiSplit_ge` + the banked reductions (§4–6) close.

**FIDELITY CAVEAT for the formaliser (verify-first):** the directed check used a sympy selected-minor
chart with denominator `D = (X2+1)·(1−Y1·Z2)`. Confirm the ACTUAL Lean chart's denominator matches (or
that the producer's own IFT chart has `D` bounded away from 0 near `v`) — a mismatch between this sympy
chart and the Lean `regStraighten`/`coreAbsorb` (if reused) is the one place it could bite. The cleaner
build is the producer's OWN selected-minor IFT chart (not reusing the gauge-slice `regStraighten`), so
the denominator is whatever that IFT produces — verify it's `C¹` with nonvanishing det near `v`.

**SCOPE:** L=2, (3,3,3)/r=1 middle (the squeeze's failure locus) certified. The structural reason
(`R=Q(0,·)` is the slice ⟹ continuity ⟹ ratio→1) is stratum- and dimension-INDEPENDENT, so it should
extend to the general L=2 optimal `v` — that generalization is NOT certified here (the formaliser
confirms it builds at general `v`). General-L = #120.

---

## ★ RIGHT-SIZING — TWO decisive tests; the SQUEEZE route FAILS at general v (do NOT charge it)

**Test 1 (a4ef57): the exact clean-square chart is WALLED at general v.** The `nReg=5` deepest-aligned
directions are NOT literal clean squares of `F`: a rank-1 regular×regular coupling sits inside the
quadratic core residuals, forcing a t-DEPENDENT (nonlinear) shift — the parametrized Morse–Bott
completion a constant-linear relabel cannot achieve. So `hF : F = ∑s² + Q` with the `s` literally the
chart coords (the `ofExactGerm` route) is IMPOSSIBLE at a general middle-stratum `v`.

**Test 2 (a9bfa7, the BINDING KILL-CONDITION check) — the SQUEEZE route also FAILS. ★ KILL-CONDITION
FIRED.** The hoped-for cheap escape — the two-sided squeeze `c₁·Φ ≤ F ≤ c₂·Φ` with the EXISTING
per-layer Schur `Φ = ∑E² + ‖∏S_s‖²` (`S_s = T_s − Z_s(I+X_s)⁻¹Y_s`) — does **NOT** hold at a general
middle-stratum `v`. EXACT + decorrelated Codex found a positive-dimensional family of curved arcs
(param `λ`) through the (3,3,3)/r=1 middle stratum (`T₁ = diag(1,0) ≠ 0` at `v`) on which, with all 5
regular residuals `E = 0`:

    F = (λ−1)²·p²b²w²,   Φ = (λ−2)²·p²b²w²,   F/Φ = (λ−1)²/(λ−2)²  (scale-independent).

`λ=1`: `F=0` but `Φ>0` ⟹ the LOWER bound `c₁·Φ ≤ F` fails (`c₁→0`). `λ=2`: `Φ=0` but `F>0` ⟹ the UPPER
bound `F ≤ c₂·Φ` fails (`c₂→∞`). **Root cause:** on `{E=0}`, `F = ‖R₂₂‖²` (the FULL lower-right product
residual) while `Φ`'s core is `‖S₁S₂‖²` (PER-LAYER Schur) — different quartics, different zero loci. The
surviving discrepancy is the inter-layer coupling `(T₂)₂₁·Y1_1·Z1_0` (a deep-kernel core direction ×
deep-kernel × regular), which lives in `F` but is DROPPED by the per-layer Schur factorization in `Φ`. At
the DEEPEST point `T₁=0` kills it (`leak ≤ t²∑E²`, the #54 bound holds); at a MIDDLE stratum `T₁≠0` it is
ORDER-1 and breaks both bounds. The leak is NOT charge-able to `∑E²`.

This is verified faithful to the Lean `Φ`: `deepestCoreF`'s core-output is TYPE-FORCED to the per-layer
Schur `∏S_s` (`coreAbsorb` reads only reg+spec; the full `R` depends on `E` so CANNOT be the core slot),
and `R − ∏S_s` is exactly the leak `#54` charges to `∑E²` (DeepestGaugeChart docstring §60-73). So the
escape "redefine the core as the full `‖R₂₂‖²`" is type-FORBIDDEN in the current per-layer structure —
and it IS the Morse-Bott reduction anyway (straightening the inter-layer coupling into the core).

**TRAP NOTE (why earlier checks looked clean):** the degree-3 leak DOES charge cleanly, and undirected
Monte-Carlo gave `eta(τ) → 0` across all four test strata — both FALSE POSITIVES. The failure lives on a
measure-zero curved subvariety random sampling never hits and the degree-3 jet does not see (a
quartic-vs-quartic zero-set mismatch). The decorrelated Codex found the arc independently; exact algebra
confirmed it. The verify-first gate did its job — it caught a wrong "cheap route" BEFORE a wasted build.

**VERDICT: D1's general-v chart genuinely needs the INTER-LAYER-STRAIGHTENING reduction** (straighten
`R₂₂ = S₁S₂ + Z₁Y₁T₂ + …` into the core, not compare to the per-layer Schur core) — i.e. the
parametrized Morse-Bott / partial splitting lemma (the ~1k-line classical lemma Mathlib v4.29 lacks),
NOT the cheap per-layer squeeze. Per the ambition mandate this is a CHARGEABLE classical build (no new
math), not a research wall (unlike #120). Do NOT charge the squeeze chart; scope the inter-layer
straightening / partial splitting lemma instead.

**SOUNDNESS NOTE (verified 2026-06-29, forced `#print axioms`):** the D1 producer reductions
(`deepest_le_of_optimal_middle_stratum`, `hCore_middle_stratum_of_interface`,
`extra_half_add_lambdaCore_Mprime_ge_square`, `deepest_le_of_optimal_of_chart_certificate`) take
`hDeepest`/`hcoreDeepest`/the chart data ALL as HYPOTHESES — so they do NOT transitively carry the
vestigial `deepest_gauge_squeeze_exists` sorry (DeepestGaugeChart:357, consumed only by
`deepest_regular_core_reduces`, which the D1 chain does NOT use). The live L=2 deepest constant is the
clean-three `deepest_gauge_construction_L2` (`[propext, Classical.choice, Quot.sound]`, AxCheck-guarded).
The producer must discharge `hDeepest` via the CLEAN L=2 route (`deepest_gauge_construction_L2` /
`deepest_regular_core_reduces_frontPivot` — front-pivot, sorry modulo the threaded `hJfront`/`htop`),
NOT via the vestigial `deepest_regular_core_reduces`.

**CORRECTNESS (general-H extension):** the banked `extraCount m a b = m(a+b)−ab` (D1ChartProducerL2Build:72)
is SQUARE-ONLY (231 violations off-square); the case-B reductions are correctly scoped to `squareWidths`
(no live bug). The CORRECT general-H formula is `extra = a·M₂ + b·M₀ − ab` (zero violations,
chain-symmetric, from `nReg_v = q·H₀ + p·H₂ − p·q`). Use it for the general-H leg; the producer's
identity lifts verbatim with it.

Scope **L = 2 only** (`H : Fin 3 → ℕ`, `prod = A⁽¹⁾·A⁽²⁾`). General-L is the named wall **#120** — do NOT
attempt. Branch off `origin/expedition/aoyagi-full`. Commit + push your OWN feature branch; isolation:
worktree; edit ONLY your worktree (a prior leg leaked into the main checkout — be strict).

---

## §MB. The parametrized Morse–Bott (inter-layer-straightening) lemma — DESIGN (af6bf2, 2026-06-29)

The SETTLED chart route. Decorrelated design pass (DIRECTED-EXACT + Codex xhigh), all Mathlib anchors
NAME-VERIFIED in the shared store. This is a STANDALONE network-free real-analysis lemma (its own file,
e.g. `Foundations/MorseBottSplit.lean`); the DLN chart instantiates it (§MB.4).

### §MB.1 The statement (cleanest Lean-v4.29 form)

`F : E × P → ℝ` (`E` = split directions, `[InnerProductSpace ℝ E] [FiniteDimensional]`; `P` = parameters,
`[NormedSpace ℝ P] [FiniteDimensional]`), `ContDiff ℝ n F` (`2 ≤ n`; `∞` free for the polynomial `dlnLoss`),
with (H1) `fderiv ℝ (fun e => F (e,0)) 0 = 0` and (H2) the E-Hessian STRICTLY positive-definite in the
**minimal-cast coercivity form** (NOT `ContinuousLinearMap.IsPositive` — VERIFIED PSD-only,
`Positive.lean:60` `IsSymmetric ∧ ∀x, 0 ≤ re⟪Tx,x⟫`; the wrong tool):

    hPD : ∃ c > 0, ∀ e : E, c * ‖e‖^2 ≤ (iteratedFDeriv ℝ 2 (fun e => F (e, 0)) 0) ![e, e]

CONCLUSION: a parameter-PRESERVING local diffeo `Φ` (raw-data form: `Φ, Φsymm, DΦ, DΦsymm, V` + the
inverse identities + `HasFDerivAt` + bounded-unit `|det|` bounds — a SUPERSET of exactly what
`rlctAtOn_boundedUnit_localHomeomorph` consumes), with `(Φ w).2 = w.2`,
`F (Φ w) = ‖(Φ w).1‖² + R w.2`, and `R t = F (σ t, t)` (`σ` the critical E-graph). After an orthonormal
`E ≃L (Fin m → ℝ)` flattening (`‖e‖² = ∑ sᵢ²` exact, `m = finrank ℝ E`), this IS the `rlct_quasiSplit_ge`
`hF : F = ∑ s² + Q` form with `Q = R ∘ snd`.

### §MB.2 Proof skeleton (6 sub-lemmas; 5/6 banked-PRESENT, names verified)

- **S1 `criticalGraph_exists`** — `σ : P → E`, `σ(0)=0`, `∂_E F(σ t,t)=0`, by the C^r IFT on
  `g(e,t) := fderiv_E F (e,t)` (E-derivative at 0 = `D²_EE F(0,0)`, coercive ⟹ `≃L`). Anchor:
  `ContDiffAt.toOpenPartialHomeomorph`/`.localInverse`/`.to_localInverse` (ContDiff.lean:31/55/66). BANKED.
- **S2 `recenter`** — `G(u,t) := F(u+σ t, t)`, so `∂_E G(0,t)=0`, `G(0,t)=R(t)`. Chain rule. BANKED.
- **S3 `hadamard_secondOrder`** — `G(u,t) − R(t) = ⟨u, A(u,t)·u⟩`, `A` symmetric ContDiff, `A(0,0) =
  ½ D²_EE F(0,0)` coercive. For the POLYNOMIAL `dlnLoss`, `A` is the EXACT polynomial s-integral computed
  coefficient-wise (do NOT route through `ParametricIntegral` — that's the general-smooth trap). Symmetry:
  `ContDiffAt.isSymmSndFDerivAt` (Symmetric.lean:544) + `isSymmSndFDerivAt_iff_iteratedFDeriv` (:170),
  both BANKED. The `A`-construction is HAND-ROLL (polynomial, cheap).
- **S4 ⚑ `morse_changeOfVars`** — `u ↦ u'(u,t)` with `‖u'‖² = ⟨u,A u⟩`, a parameter-preserving in-u local
  diffeo. **The operator-√ gap is ELIMINATED** (§MB.3): recursive completing-the-squares — pivot on
  `A₀₀(u,t) > 0`, peel `A₀₀·(u₀ + (row/A₀₀)·u_rest)²`, recurse on the SPD `(n−1)`-Schur complement. ONE
  scalar `Real.sqrt` per pivot via `contDiffAt_sqrt (hx : x ≠ 0)` (Sqrt.lean:65, BANKED). No operator √.
- **S5 `assemble_Φ`** — `Φ := recenter⁻¹ ∘ changeOfVars⁻¹`, extract raw fields from the
  `OpenPartialHomeomorph`. BANKED API.
- **S6 `boundedUnit_det`** — `|det DΦ|` bounded above + below by positives on a shrunk `V`
  (`ContinuousAt.eventually_ne` + `eventually_gt_nhds`; `(DΦ w).det` is the consumer's own
  `ContinuousLinearMap.det`). BANKED.

THE ONE HARDEST = S4; the design pass RETIRED its feared operator-√ via §MB.3. Secondary risk: the S3
`iteratedFDeriv 2` ↔ polynomial-coefficient cast for `A(0,0)`.

### §MB.3 √-avoidance (DIRECTED-EXACT confirmed) — use recursive completing-the-squares, NOT an LDL library

`A = LDLᵀ` has `L,D` RATIONAL in `A`'s entries (denominators = leading principal minors, `>0` on the SPD
cone). `⟨u,Au⟩ = ∑_k D_kk·(Lᵀu)_k²`; set `u'_k := √(D_kk)·(Lᵀu)_k` — the ONLY √ is the scalar `Real.sqrt`
of one positive function. Mathlib v4.29 has NO `PosSemidef.sqrt`/Cholesky/Sylvester API (`LDL.lean`
deprecated-empty), so realize S4 as the FIXED-`m` recursive normal-form proof (per-pivot scalar √), NOT a
reusable LDL theorem. Directed-exact: the in-u Jacobian at 0 is `diag(√D_kk)·L₀ᵀ`, `det = √(det A₀) > 0`
⟹ local diffeo.

### §MB.4 DLN instantiation (L=2) — Gauss–Newton makes hPD automatic at EVERY optimal v

The E/P partition is FORCED by the optimal point: `E := (ker Dg(v))⊥` (dim = `nReg_v = rank Dg(v)`),
`P := ker Dg(v)`, `g(A) := prod A − B`. **hPD is automatic** (Gauss–Newton): at an optimum `g(v)=0`, the
`g·D²g` term of `D²F` VANISHES, leaving `D²F(v) = 2(Dg(v))ᵀ(Dg(v))` — PSD with kernel exactly `ker Dg(v)`,
hence strictly PD on `E`. Verified DIRECTED-EXACT (sympy rational, NOT sampling) at 5 strata: (3,3,3)/r=1
middle (`nReg_v=7`), (3,3,3)/r=1 deepest (`nReg_v=5`), (4,4,4)/r=2 middle, (3,4,3)/r=1 rectangular, and a
GAUGED (non-diagonal) v. `R(t) = F(σ t, t)` is the degraded core the D1 second-peel consumes; the
inter-layer coupling `(T₂)₂₁·Y1·Z1` that killed the squeeze is ABSORBED into `A(u,t)` and straightened
away (directed-exact: a planted analogous coupling lands as higher-order-in-`u`, leaving `A(0,t)` clean).

### §MB.5 ★ TWO REFINEMENTS for the CONTROLLER (consume-path + a lighter alternative) — decide before build

1. **SINGLE-PASS vs TWO-PEEL + the `nReg_v` citation-tension.** Morse–Bott naturally outputs `m = nReg_v`
   (stratum-dependent). The design pass proposes wiring DIRECTLY through `rlct_quasiSplit_ge` (free `{m}`):
   `nReg_v/2 + rlctAtOn R t0 ≤ rlctAt … v`, then the banked arithmetic with `extra = nReg_v − nReg` closes
   `hCore` — REPLACING the current two-peel (`nReg`-peel + `extra`-Morse-peel). Fewer moving parts, same
   arithmetic identity. ★ BUT: the controller earlier flagged peeling `nReg_v` (the maximal/stratum count)
   as the FORBIDDEN Aoyagi-Thm-2 maximal Morse split (the hero-constraint citation concern). RESOLUTION
   (controller to confirm): the Morse–Bott lemma is a CLASSICAL splitting lemma we BUILD ourselves (not a
   citation of Aoyagi Thm 2), so peeling `nReg_v` of OUR-built clean quadratic directions is citation-safe
   — the "forbidden" concern was about CITING Aoyagi's maximal-split RESULT, not about a self-built chart
   that happens to peel `nReg_v`. If the controller concurs, single-pass is cleaner; else keep the
   two-peel (constant `nReg` + `extra`), which the banked reductions already encode.
2. **A LIGHTER ALTERNATIVE (INFERENCE, flag).** The SELECTED-MINOR IFT quasi-split `F∘Ψ⁻¹ = ‖s‖² +
   ‖q(s,t)‖²` (which `rlct_quasiSplit_ge` ALREADY accepts — it does NOT require clean squares, only the
   `∑s²+Q` shape with `Q≥0`) MIGHT avoid the full Morse–Bott S4 recursion: pick the `nReg` independent
   gradient minors, IFT-straighten them to `s`, leave the rest as `q(s,t)` (the residual, NOT decoupled),
   and let `rlct_quasiSplit_ge`'s constant-comparison `hcmp` absorb the coupling. The earlier kill-condition
   showed the per-layer SCHUR `Φ` fails — but the selected-minor `‖q(s,t)‖²` residual is the FULL coupled
   residual, NOT the per-layer Schur, so it may dodge the inter-layer-drop that killed the squeeze. Worth a
   DIRECTED-EXACT check (does `hcmp : ∑s² + ‖q(0,t)‖² ≤ C·(∑s² + ‖q(s,t)‖²)` hold at the (3,3,3) middle
   stratum with the SELECTED-MINOR `q`, not the Schur core?) BEFORE committing the full Morse–Bott build —
   it could be materially cheaper. (This is the af6bf2 closing flag; INFERENCE, unverified.)

---

## 0. The target

`rlctAt_deepest_le_of_optimal` (Skeleton:1172) concludes, for any `v ∈ optimalSet H B`:

    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) ≤ rlctAt H (dlnLoss H B) v.

The BANKED `deepest_le_of_optimal_chart` (Validate/D1ChartProducer.lean) discharges this MODULO three
inputs: `hDeepest` (= #44, the existing Skeleton sorry `deepest_regular_core_normal_form`), the chart
data, and `hCore`. Your deliverable is a producer theorem `GeneralVChartL2` (new file
`Validate/D1ChartProducerL2.lean`) that, for general `v` at L = 2, supplies those inputs and calls
`deepest_le_of_optimal_chart`. So D1's per-point `≥` lands at L = 2.

---

## 1. The mathematics (already adjudicated — DO NOT re-derive, just formalise)

`dlnLoss H B A = ∑ᵢⱼ ((prod A − B)ᵢⱼ)²` — a sum of squares of the smooth product-difference entries
`g_{ij}(A) = (prod A − B)_{ij}`. At an optimal `v` (`prod v = B`), all `g_{ij}(v) = 0`.

Let `m = M_s` the reduced width (`M = H − r`), `a = rank(A₁ at v) − r ≥ 0`, `b = rank(A₂ at v) − r ≥ 0`.
**Peel exactly the CONSTANT `nReg = r(H₀+H₂−r)` independent gradient directions** (the DEEPEST count,
constant on the fibre — NOT the maximal Hessian rank `nReg_v` at `v`; peeling `nReg_v` is the FORBIDDEN
Aoyagi-Thm-2 maximal Morse split and breaks constancy). The slice residual `R` then factors as
(adjudications a97332 / a9a2cf, EXACT, 164-strata exhaustive sweep + Codex):

  * **Deepest-type `v` (`nReg_v = nReg`, i.e. `a = b = 0`):** `R = ‖T₁·(I+G)·T₂‖²_F` with `G` gauge-only,
    `G(0) = 0`, so `R = (core ∘ fst) ∘ Φ` for the bounded-unit local diffeo
    `Φ : (T,g) ↦ ((T₁, (I+G(g))·T₂), g)`, `det DΦ(0) = (det(I+G(0)))^{M₂} = 1`. ⟹ `rlctAtOn R 0 =
    rlctAtOn core 0 = coreDeepest`. (`core = dlnLoss M 0`, `M = H−r`.)

  * **Middle-stratum `v` (`nReg_v > nReg`):** `R ~ (∑_{extra} w_k²) + (degraded core)` via a
    Morse-with-parameters local diffeo, where `extra = m(a+b) − ab` and the degraded core is the deepest
    DLN core of widths `M' = (m−a, m−a−b, m−b)`. ⟹ `rlctAtOn R 0 = extra/2 + lambdaCore(M')` and
    `extra/2 + lambdaCore(M') ≥ coreDeepest` (self-contained `Mval`/`Adm` arithmetic).

Both cases give `hCore : coreDeepest ≤ rlctAtOn R 0`. The deepest-type uses the banked
`hCore_slice_residual_eq` directly; the middle-stratum uses the second-peel route (§4).

---

## 2. Banked consumers (your call targets — exact signatures)

All in `Validate/D1ChartProducer.lean` (+ `Foundations.*`); already clean-three, axiom-clean
`[propext, Classical.choice, Quot.sound]`:

- **`deepest_le_of_optimal_chart`** — the headline wiring. Takes `H r B deepest v F Q R t0 coreDeepest`,
  `hDeepest`, `hchart`, `hF`, `hQ0`, `hFmeas`, `hR`, `hRmeas`, `hRne`, `C`, `hC`, `hcmp`, `hCore`;
  concludes `rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v`. THIS is your final call.
- **`rlctAt_ge_nReg_add_slice`** — the `hAtV` half (if you want it standalone): `hchart` + the engine ⟹
  `nReg/2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v`.
- **`hCore_slice_residual_eq`** — the deepest-type `hCore` discharge: bounded-unit local diffeo `Φ` +
  `hRform : R = (core₀ ∘ fst) ∘ Φ` + a positive-finite gauge nbhd ⟹ `rlctAtOn R (t0,g0) = rlctAtOn core₀ t0`.
- **`rlct_quasiSplit_ge`** (Foundations.S1QuasiSplit) — `F = ∑s² + Q`, `Q ≥ 0`, `R = Q(0,·)` measurable
  a.e.-nonzero, `hcmp : ∑s² + R ≤ C·F` ⟹ `nReg/2 + rlctAtOn R t0 ≤ rlctAtOn F (0,t0)`.
- **`coupled_controls_slice`** (S1QuasiSplit) — `(a−b)² ≤ L²·∑s² ⟹ ∑s² + b² ≤ (2L²+2)(∑s² + a²)`. Build
  `hcmp` by summing this over the inactive index, with `L` from the mean-value bound on the coupled part.
- **`rlctAtOn_boundedUnit_localHomeomorph`** (S1NonMPTransport:292) — strips the chart `Φ` (raw-data
  form: `Φ`, `Φsymm`, `DΦ`, `DΦsymm`, the inverse identities, derivs, bounded-unit det bounds on `V`).
- **`rlctAtOn_spectator_peel`** (S1Spectator:82) — drops the gauge factor (positive-finite gauge nbhd).
- **`rlctAtOn_comp_homeomorph`** (S1Fubini:54) — MP-homeo RLCT transport (for the `Params↔flat` bridge).

---

## 3. The chart-space machinery to REUSE (the deepest-point template to GENERALIZE off `deepestPoint`)

The deepest-point construction is the EXACT template; the producer generalizes it off `deepestPoint`/
`IsDeepLayers` to a GENERAL optimal `v`. Reuse:

- **`paramsEquivFlat H`** (Foundations.ParamsFlat:80) — `Params H ≃ᵐ (Fin (flatDim H) → ℝ)`, with
  `measurePreserving_paramsEquivFlat`, `continuous_paramsEquivFlat(_symm)`. The `Params ↔ flat` bridge
  (so the chart lives on `Fin (flatDim H) → ℝ`, a normed/Haar space for `rlctAtOn_boundedUnit_localHomeomorph`).
- **`DeepestGaugeChart` structure** (DeepestGaugeChart:143) + **`DeepestGaugeChart.ofExactGerm`** (:251) —
  the smart constructor for the deepest chart; build the general-`v` analog.
- **`deepest_regular_core_reduces`** (DeepestGaugeChart:524) — the deepest-point EXACT template producing
  `rlctAt(deepest) = nReg/2 + rlctAtOn(reduced core) 0`. Your producer is its analog at `v`, but EXPOSES
  the post-chart `F = ∑s² + Q` form (so `rlctAt_ge_nReg_add_slice` consumes it) rather than the
  already-reduced equality.
- **`deepest_regular_smooth_split`** (:434), **`deepest_reduced_core_identification`** (:385) — the
  smooth-block split + the `Params↔flat` reduced-core identification (reuse with `M = H−r`).
- The **gauge slice** `C_s = [[I_r+X_s, Y_s],[Z_s, T_s]]` (per-layer `block_elimination` units `P_s, Q_s`)
  — the chart at `v`. The regular coords are the `nReg` directions `P₁₁−I_r, P₁₂, P₂₁`; the reduced core is
  `‖∏ C'_s‖² = dlnLoss M 0`.
- **Mathlib C^r IFT**: `ContDiffAt.toOpenPartialHomeomorph` / `.localInverse` / `.to_localInverse`
  (VERIFIED present); **`Convex.norm_image_sub_le_of_norm_fderiv_le`** (mean-value Lipschitz, for `hcmp`).

`dlnLoss`/`prod` are polynomial ⟹ `ContDiff ℝ ⊤` (by `fun_prop`); `measurable_dlnLoss` /
`continuous_dlnLoss` are banked.

---

## 4. The two-case `hCore` discharge

`deepest_le_of_optimal_chart` takes `hCore : coreDeepest ≤ rlctAtOn R t0` as a hypothesis. Discharge it
by dispatching on `v`'s rank pattern:

**(A) Deepest-type (`a = b = 0`):** build the bounded-unit diffeo `Φ : (T,g) ↦ ((T₁, (I+G(g))·T₂), g)`
(`G` gauge-only from the gauge slice, `G(0)=0`, so `det DΦ(0)=1` by block-triangularity), verify
`hRform : R = (core₀ ∘ fst) ∘ Φ`, and call **`hCore_slice_residual_eq`** ⟹ `rlctAtOn R t0 = coreDeepest`
(so `hCore` with equality). `core₀ = dlnLoss M 0` on the reduced widths.

**(B) Middle-stratum (`nReg_v > nReg`) — the SECOND-PEEL route (design-pass a9a2cf):** the direct
domination route is DEAD (proven: any `rlctAtOn_mono` dominator must vanish on the Schur zero-set
`{(P+X)Y=0}`, so it already encodes the degraded core). The forced route:
  1. `R ~ (∑_{extra} w²) + (degraded core M')` via a Morse-with-parameters local diffeo (the inner
     straightening `rlctAtOn_boundedUnit_localHomeomorph` + `rlctAtOn_spectator_peel`).
  2. `rlctAtOn R 0 = extra/2 + rlctAtOn(degraded core M') 0` via a SECOND `rlct_quasiSplit_ge` application
     (peel the `extra` Morse squares off the degraded core).
  3. `rlctAtOn(degraded core M') 0 = lambdaCore(M')` — **the R1-resolution-at-`M'` INTERFACE (§5).**
  4. `extra/2 + lambdaCore(M') ≥ coreDeepest` — **the self-contained arithmetic lemma (§6).**
  Chain (2)+(3)+(4) ⟹ `hCore`.

You may bank (A) NOW (it uses only banked machinery). (B) is conditional on the §5 interface (which is
itself a Skeleton obligation — see §5) — so structure (B) to take the interface as a HYPOTHESIS.

---

## 5. The R1-resolution-at-`M'` INTERFACE (named hypothesis — interface-banking pattern)

★ **CONTROLLER PRECISION (bake this in):** the middle-stratum `hCore` consumes R1's resolution THEOREM
at the rectangular `M'`, NOT R1's closed-form value and NOT #44. Structure the producer to take

    hResolveM' : ∀ (M' : Fin 3 → ℕ), (∀ s, 0 < M' s) →
        rlctAtOn (fun A : Params M' => dlnLoss M' 0 A) (fun _ => 0) = ENNReal.ofReal (lambdaCore M')

(or the per-`M'` instance you need) as a **NAMED INTERFACE/HYPOTHESIS**. Then the producer builds + lands
CONDITIONALLY NOW (R1's `resolution_charts` is itself a Skeleton sorry), and `hResolveM'` discharges when
R1's general resolution closes. So the producer is NOT hard-sequenced behind R1 — it builds independently.

The interface is dischargeable from the BANKED `resolution_value_of_atlas` (ResolutionAtlas:197,
`⨅ monomialThreshold = ofReal(lambdaCore M)` for arbitrary `M`) + `resolution_charts` (Skeleton:1228,
the chart family for arbitrary `M`, only `hMid : ∀ s, 0 < M s`). Both are stated for ARBITRARY width `M`
(VERIFIED — NOT square-only), so `M'` is covered.

★ **BINDING CONSTRAINT to state in the spec docstring:** `resolution_charts` (Skeleton:1228) MUST stay
general-width (`hMid` only, NOT narrowed to square-only) so it covers the rectangular `M'`. Record this
as an explicit dependency. (No one is building `resolution_charts` yet — it's gated; this is a constraint
on the future R1 cover-assembly, not a live-front message.)

---

## 6. The self-contained arithmetic lemma (build this — pure `ℚ`/`Mval`/`Adm`, no R1, no analysis)

    extra/2 + lambdaCore(M') ≥ coreDeepest,   where coreDeepest = lambdaCore(M),
    extra = m(a+b) − ab,  M' = (m−a, m−a−b, m−b),  M the deepest reduced widths.

Self-contained over `ℚ`, from the symbolic identity `extra + D_{a,b}(t) = F_m(a+t)`, `F_m(s)=(m−s)²+sm`
(`D` the degraded `Mval`). Reduces to `Mval`/`Adm` algebra (Lambda.lean: `Mval`, `Adm`, `lambdaCore`,
`Mval_nonneg_of_adm`, `zero_mem_Adm`). At L=2 (`M : Fin 3 → ℕ`) `Adm M` is small — `decide +kernel` may
close the per-case inequality, or an explicit `Finset.inf'` bound. This is the cleanest piece to land
first (no chart, no analysis). Verified ZERO violations across 164 strata (`m ≤ 8`); D1 needs only `≥`.

---

## 7. Suggested build order (≤4-attempts-then-bank per piece; clean-three, forced #print axioms)

1. **The arithmetic lemma (§6)** — pure `ℚ`/`Mval`/`Adm`, no dependencies. Land first.
2. **The deepest-type producer (A)** — the chart `Φ` + `hRform` + `hcmp` (via `coupled_controls_slice`)
   + `hchart` (via `rlctAtOn_boundedUnit_localHomeomorph` + the `Params↔flat` bridge), feeding
   `rlctAt_ge_nReg_add_slice` + `hCore_slice_residual_eq` + `deepest_le_of_optimal_chart`. Lands D1 `≥` on
   the deepest-type sub-locus. CLEAN-THREE banked (banked machinery only).
3. **The middle-stratum producer (B)** — the second-peel (§4) + the §5 `hResolveM'` interface hypothesis
   + the §6 arithmetic. Conditional clean-three (the interface is the only open hypothesis).
4. **`GeneralVChartL2`** — dispatch on `v`'s rank pattern (A vs B) ⟹ `rlctAt_deepest_le_of_optimal` at L=2.

DISCIPLINE: at a wall on the chart construction (the gauge slice at general `v` / the Morse-with-params
diffeo for (B)), bank what's clean + surface the PRECISE residual — the controller brings a decorrelated
pen-and-paper. Do NOT grind the whole chart blind. The truth-value is BANKED (adjudications a97332/a9a2cf,
EXACT); your job is the formalisation, not re-deriving the math.

---

## 8. Hand-off checklist for the spawned formaliser

- [ ] New file `Validate/D1ChartProducerL2.lean` (DISJOINT from `D1ChartProducer.lean` — additive).
- [ ] Imports: `D1ChartProducer`, `DeepestGaugeChart`, `DeepestL2Wiring`, `S1QuasiSplit`, `S1Spectator`.
- [ ] NOT wired into `DLNFibre.lean` (single-writer aggregator — the controller wires + AxCheck).
- [ ] Zero `sorry`/`axiom`/`native_decide`/`#exit`; `scripts/sorries` clean; forced `#print axioms` on the
      producer theorems = `[propext, Classical.choice, Quot.sound]` (the §5 interface enters as a
      hypothesis, NOT a sorry).
- [ ] Statement card per `docs/policies/statement-cards.md`.
- [ ] Report: the deepest-type producer (banked unconditionally) + the middle-stratum producer (conditional
      on `hResolveM'`) + the arithmetic lemma; or a precise wall.
