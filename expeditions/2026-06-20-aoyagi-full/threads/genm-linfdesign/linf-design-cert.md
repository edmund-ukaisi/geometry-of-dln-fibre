# ∀-L unified Aoyagi-blow-up build — DESIGN certificate (genm-linfdesign)

Explore/scout thread (aoyagi-full endgame design). Read-only reconnaissance of the canonical Lean at
`origin/expedition/aoyagi-full` and the L=2 gauge-slice on `origin/genm-b3closer`; grounded on the
WALLS-UNIFY cert (`genm-wallunify-pnp`) + the two D1 de-risk certs (`genm-d1uniform`/`genm-d1lower`) +
the Aoyagi 2024 PDF Section 5. Deliverable: the concrete ∀-L build plan so the controller can charge it
in bounded pieces.

---

## HEADLINE FINDING (sharpens the mission framing — load-bearing)

**The ∀-L R1 core resolution is ALREADY ASSEMBLED sorry-free EXCEPT for ONE hypothesis.**
`r1_resolution_general` (`R1ResolutionGeneral.lean:119`) proves, for every nondegenerate reduced-width
`M : Fin (L+1) → ℕ`,

    rlctAtOn (dlnLoss M 0) 0 = ofReal (lambdaCore M)

conditional on the SINGLE named input `hbox : RouteMBoxThresholdFinite M`. Everything else in R1 is
banked ∀-L, sorry-free (verified by reading the actual theorems, not the docstrings):

| R1 leg (∀-L) | object | status |
|---|---|---|
| `hdiv` (cover_ge_div / ≤-leg / the achiever divergence) | `routeMCore_box_diverges_achiever_full'` (`RouteMAchieverFullHNoFree.lean:40`, 0 sorries) | **DONE** — de-conditionalized (`hNo` discharged by the `InteriorDrop`/bridge split) |
| value lane (`⨅ monomialThreshold = ofReal lambdaCore`) | `routeLayerAtlas_value_eq_lambdaCore`, `..._eq_half_minAdm`, `routeLayerAtlas_isResolutionAtlas` (`RouteMLayerValue.lean:94/131`) | **DONE** (sorry-free; the file's `sorry` grep hits are doc mentions only) |
| cover→rlct bridge | `routeM_rlctAtOn_eq_iInf` (`RouteMBridge.lean:79`, 0 sorries) | **DONE** |
| flat↔params transport | `rlctAtOn_routeMCore_transport` | **DONE** |
| `hfin` (cover_le / ≥-leg) reduction | `routeMLayerCover_hfin` (`RouteMLayerCoverHfin.lean:130`) reduces `hfin` to `hbox` | **DONE modulo `hbox`** |
| **`hbox` (the box-integral finiteness itself)** | `RouteMBoxThresholdFinite M` (`RouteMBoxReduction.lean:165`) | **OPEN ∀-L — the ONE target** |

So the entire "∀-L unified Aoyagi blow-up" reduces, in Lean, to proving ONE statement:

> **Target T (`hbox`, ∀-L).** For `M : Fin (L+1) → ℕ` and every real `c'` with `0 < c' < ½·minAdm M`:
> `routeMLayerBoxIntegral M c' 1 < ⊤`, i.e.
> `∫⁻_{A ∈ paramsBoxM M 1} ofReal( frobSq(prod M A)^{−c'} ) < ⊤`,
> where `paramsBoxM M 1 = {A | every layer-matrix entry ∈ [−1,1]}` and `prod M A = A⁰·A¹···A^{L−1}`.

This is a **pure box-integral finiteness** — no RLCT, no cover interface, no germ subtlety. `hbox` is the
`≥`-leg / `cover_le` / finiteness-below-threshold half of Aoyagi's resolution equality (WALLS-UNIFY §1),
and it is the SINGLE remaining analytic atom of ∀-L R1.

**Why this is the "unified blow-up":** WALLS-UNIFY said the blow-up delivers BOTH the `≥`-leg (finiteness)
and the `≤`-leg (divergence). The `≤`-leg needs divergence along ONE branch — the achiever — and is
**already built ∀-L** (`full'`, via a single-pivot chart, NOT the whole atlas). The `≥`-leg needs the
WHOLE cover (every branch finite) — this is the sum-staircase that no single/two-matrix step reaches — and
IS `hbox`. So the blow-up's remaining job is exactly `hbox` = cover_le.

---

## 1. The recursion structure ∀-L (Aoyagi Section 5 → a Lean recursion)

### 1.1 What `hbox` needs and what it does NOT

`hbox` is the finiteness-below-threshold direction only. From the L=2 `hfin` machinery
(`RouteMLayerCoverHfin`) and the value lane, the ∀-L build does **not** need the exact monomial exponents
or the ideal equality `⟨∏C⟩ = ⟨diag(b_i)⟩`; it needs only that a **finite chart cover of the box** exists
on which `frobSq(prod)^{−c'}` transports to an integrable monomial for every `c' < ½·minAdm M`. That is a
per-chart **inequality** `c' < threshold_chart` with `⨅ threshold_chart = ½·minAdm M` — the value lane
already proves `⨅ = ½·minAdm M`, so the finiteness only needs each `threshold_chart ≥ ½·minAdm M` and the
box covered.

### 1.2 The two candidate Lean recursion shapes

The r1upper-derisk (2026-07-01) proved the CORANK scaffold walls at L≥3 (its measure is the corank of one
square factor; the sum-threshold needs ≥2 boundaries). It named the missing piece §3(a): "a new
WellFounded recursion on the **arity L**, not on corank." WALLS-UNIFY (2026-07-03) then identified that
missing recursion as **Aoyagi's (S,J) blow-up** — validated uniform-in-`v` and bounded by
`genm-d1uniform`. Two shapes are available; the choice is the first design decision for the build thread.

- **Shape A — arity-L descent mirroring `minAdmRec`** (`RouteMLayerSplit.minAdmRec`,
  `minAdmRec_eq_minAdm` PROVEN):
  `minAdm(M₀,…,M_L) = min_{0≤t≤min(M₀,M₁)} [ (M₀−t)(M₁−t) + minAdm(t, M₂,…,M_L) ]`.
  Mirror this on the integral: **stratify the box by the rank `t` of the front boundary** `A⁰·A¹`
  (finitely many pivot-minor charts, one per `t` and per chosen `t×t` minor), on each chart a monomial
  blow-up c-o-v peels the `(M₀−t)(M₁−t)` transverse directions at codim `(M₀−t)(M₁−t)` (a Morse/monomial
  factor), leaving a reduced-arity box integral for the chain `(t, M₂,…,M_L)` at the **shifted exponent**
  `c' − (M₀−t)(M₁−t)/2`. WellFounded on **arity L** (strictly decreasing: L → L−1). Terminates at the
  two-matrix base (L=2), where the banked `routeMBoxThresholdFinite_mnp` (`RouteMSchurRectCapB.lean:453`)
  closes it. The finiteness composes ADDITIVELY across boundaries precisely because each peel SHIFTS the
  exponent down by that boundary's codim/2 (contrast `fibre_lintegral_mul_le`, which caps at width/2 and
  PRESERVES the exponent — the r1upper "cap p/2" undershoot).
  *This is the coarsest recursion that reaches the sum-threshold; it is the finiteness-only reading of
  Aoyagi's (S,J) with S = the arity index.*

- **Shape B — the full (S,J) lex recursion** (Aoyagi verbatim, `genm-d1uniform` distillation):
  double index `(S,J)`, `S∈{0..L+1}` = factors absorbed into `diag(b₁,…,b_{M(S)})` (`M(S)=min_{s≤S}M^(s)`),
  `J∈{0..M(S+1)}` = diagonal entries peeled. Per step = explicit blow-up along `{d_ij=0, u_{s,k}=0}`
  (Case 1) or `{d_ij=0}` (Case 2) with monomial substitution `d = u·d'` and monomial Jacobian
  `∏ u_{s,k}^{M_{s,k}−1}`. Lex measure `(S, J, #{u : t̃=J+J₁})`, all bounded (`S≤L+1`, `J≤min_s M^(s)`,
  `#u` finite). Load-bearing invariant = the total-chain property `T_{s,k} ≤ T_{s',k'} or ≥` (line 1459),
  re-established each case. Terminates in the diagonal monomial (normal-crossing) form.

**Recommendation for `hbox` (finiteness only): Shape A, with a WEIGHTED-integral induction statement.**
For the exact VALUE (needed by the value lane) Shape B is Aoyagi's route, but the value lane is ALREADY
banked (`routeLayerAtlas_value_eq_lambdaCore`), so the build does not re-derive the value — it needs only
finiteness. Shape A's arity-L descent (i) matches the already-proven `minAdmRec` arithmetic 1-to-1 (the
termination and the additive codim are `minAdmRec`'s own structure), (ii) bottoms out on the ALREADY-BUILT
L=2 two-matrix box (`routeMBoxThresholdFinite_mnp`), and (iii) avoids the total-chain-invariant bookkeeping
(Shape B's one terse spot the formaliser must machine-check, `genm-d1uniform` §residual-risk). The
total-chain invariant is needed to pin exact exponents and θ; for a finiteness inequality it is not.

**Critical refinement (decorrelated Codex, §6): the induction statement must be a WEIGHTED integral, not
the bare box integral.** A *plain* arity-L induction is "too coarse — it forgets how vanishing orders
accumulate across boundaries" (this is precisely why the two-matrix corank recursion undershoots). The
correct induction carries the accumulated Jacobian monomial `wσ` from prior blow-ups:

    Iσ(c') := ∫_{Uσ} wσ(u) · Fσ(u)^{−c'} du  < ⊤,

with `Fσ` the current residual product-norm and `wσ` the accumulated exceptional-divisor weight. Each child
chart has the shape `Fσ∘φ = m(u)²·Fτ(v)·U(u,v)` (`a ≤ U ≤ b` unit), `|Jac φ| ≤ C·n(u)`, so Tonelli gives

    Iσ(c') ≤ C · (∏_{new vars} ∫₀¹ tᵃ⁻²ᶜ'ᵇ dt) · Iτ(c').

The new monomial power enters from the CURRENT boundary; the child carries the previous weights in `wτ`.
That is exactly where "sum across boundaries" lives. (My §2 sub-lemma 3 "exponent-shift" is the same
bookkeeping at a *varying* c'; Codex's fixed-c' + accumulated-weight form is cleaner for Lean because the
per-boundary `∫₀¹ tᵃ⁻²ᶜ'ᵇ` factors are independent 1-D integrals summed by `ENNReal.sum/prod`, and c'
stays fixed against the single threshold `½·minAdm`.) **Adopt the weighted form for the induction
statement.**

### 1.3 The ∀-L analog of the L=2 `jacFlatL2_rank_eq` / the finite atlas

At L=2 the box finiteness is `routeMBoxThresholdFinite_mnp` via the rectangular corank recursion
(`RouteMSchurRect*`, `RouteMSchurGeneral.core_schurGen_lt_top`): a radial-Δ pivot cover (`r²` charts) ×
minor-pivot Schur split × Morse-block peel, WellFounded on corank. The ∀-L analog under Shape A is: the
per-boundary **rank-`t` pivot-minor cover** (finite: `Σ_t C(M_s,t)·C(M_{s+1},t)` charts at each boundary,
finite product over boundaries) × the same radial/Morse peel per boundary × the arity descent. The finite
atlas is a `Finset` of (boundary-index → chosen minor) tuples — bounded by `∏_s 2^{M_s·M_{s+1}}`, finite.
`jacFlatL2_rank_eq` (the L=2 residual-Jacobian full-rank fact) generalizes to the **per-boundary Varah/Gram
full-rank of the front product** — the SAME lemma the smeared-derisk isolated as the one new brick
(`Core.Matrix.RectVarahChain`, ~150–250 lines, no Mathlib gap; smeared-derisk §4/§6).

---

## 2. The Lean decomposition of `hbox` (bounded sub-lemmas; banked vs new; sizes)

Target: `RouteMBoxThresholdFinite M` (∀-L), Shape A. Sub-lemmas in dependency order:

1. **`minAdmRec` shift arithmetic** (BANKED core + thin new). The achieving-`t` split
   `½·minAdm(M) = min_t [½(M₀−t)(M₁−t) + ½·minAdm(t,rest)]` and the "for `c' < ½·minAdm(M)`, on the
   rank-`t` chart `c' − (M₀−t)(M₁−t)/2 < ½·minAdm(t,rest)` for the stratum's `t`" bookkeeping.
   *Off the PROVEN `minAdmRec_eq_minAdm` + `omega`/`Finset.inf'` arithmetic. ~80–150 lines, no new math.*

2. **The per-boundary rank-`t` pivot-minor cover of the box** (NEW, bounded). A finite `Finset` of charts
   covering `paramsBoxM M 1`, indexed by (front pivot `t×t` minor). Reuse the radial-Δ pivot cover pattern
   of `RouteMSchurGeneral`/`RouteMSchurRectCover` (the `r²` chart cover exists at depth 2). *~200–300 lines;
   generalizes a banked pattern from "one square factor" to "the front boundary of an L-chain."*

3. **The per-boundary exponent-shifting peel** (NEW — the load-bearing analytic step). On a rank-`t` chart,
   a monomial blow-up c-o-v with `|det Dφ| = (monomial of codim (M₀−t)(M₁−t))` such that
   `∫_chart frobSq(prod)^{−c'} ≤ (finite monomial factor) · ∫_{reduced box} frobSq(prod_{reduced})^{−(c'−(M₀−t)(M₁−t)/2)}`.
   The monomial factor finite iff `c' < ½·(M₀−t)(M₁−t) + (boundary threshold)` — the exponent SHIFT is the
   whole point. Bricks: `fibre_lintegral_mul_le` (the crude p/2 peel, adapt to shift), the radial c-o-v +
   minor-pivot Schur split (`RouteMSchurRectStep`, `schur_minorPivot_split_rect`), the Morse dominator
   (`radial_morse_dominates_lt_top`). *~300–500 lines; this is where the "new but bounded" content lives —
   the analog of the corank per-step, re-cast to descend arity and shift the exponent.*

4. **The front-product full-rank Varah chain** (NEW brick, smeared-derisk-identified). `det(P₁ᵀP₁) ≠ 0`
   box-unconditionally where `P₁ = (A⁰···A^{k})[:,:t]` is the front-product rank block — needed so the
   rank-`t` chart's routing/shear is well-defined. `Core.Matrix.RectVarahChain`, composing the banked
   single-factor `StrictRowDominant.exists_argmax_bound`. *~150–250 lines; no Mathlib gap; the ONE genuinely
   new real-matrix lemma. The wide-factor-before-bottleneck phrasing (smeared-derisk §5) is the subtlety.*

5. **The arity-descent assembly (WellFounded on L)** (NEW wiring, mechanical). Chain 1–4 into the recursion:
   base case L=2 → `routeMBoxThresholdFinite_mnp`; step → cover (2) + peel (3) + shift (1), sum over the
   finite chart Finset (`ENNReal.sum_lt_top`), recurse on `(t,M₂,…,M_L)`. *~200–400 lines; mechanical once
   1–4 land, but the cast/reindex plumbing (arity descent changes `Fin (L+1)` → `Fin L`) is the bulk, like
   the interior/smeared opaque-width decodes.*

6. **`hbox` ⟹ retire `routeMCore_threshold_lt_top` (`RouteMSchur.lean:426`)** (BANKED, one line). Once (5)
   gives `hbox`, `routeMCore_threshold_lt_top_of_box M hbox` (`RouteMBoxReduction.lean:174`, PROVEN)
   discharges the RouteMSchur:426 sorry directly. The 426 skeleton is then redundant.

**Recommended file split (Codex Q2 two-layer separation):** keep the combinatorial chart-tree builder
(sub-lemmas 1,2,5's indexing — the lex-well-founded `(S,J,K)` state + the finite chart `Finset`) in ONE
module, and the analytic finiteness induction (sub-lemmas 3,4 — the weighted-integral `Iσ` per-step + the
Varah brick) in a SEPARATE module, with index-transport lemmas isolated from the measure-theory lemmas.
This is the discipline that keeps `Fin`-arithmetic from contaminating the Tonelli proofs.

**Total scale estimate:** ~1100–1900 lines, comparable to the interior (`genm-glinterior`) or smeared
general-L builds. The genuinely-new mathematics is bricks (3) + (4); the rest is banked-pattern
generalization + arity-descent cast plumbing. **No research wall** — Mathlib HAS the integral
change-of-variables (arXiv:2207.12742, since 2022); every step is an explicit monomial c-o-v (best done as
custom fiberwise-scaling Tonelli lemmas, not the general diffeo API) + a matrix full-rank fact.

---

## 3. The unification wiring (item 3 — precise, with a framing correction)

The mission asked how the ONE blow-up "discharges BOTH the D1 ≥-leg AND `RouteMBoxThresholdFinite`(hbox) —
closes `Skeleton.lean:1124/1172` (D1) AND retires `RouteMSchur.lean:426`." The honest wiring, split by
what the blow-up DOES and does NOT close:

### 3.1 What the blow-up closes DIRECTLY (via `hbox`)

- **`RouteMSchur.lean:426`** (`routeMCore_threshold_lt_top`, the ∀-M flat-integral finiteness skeleton):
  RETIRED as a corollary — `routeMCore_threshold_lt_top_of_box M hbox` (PROVEN) discharges it the instant
  `hbox` lands. This IS the WALLS-UNIFY `le_antisymm` `≥`-leg (`cover_le`): `hbox` = the finiteness-below-
  threshold half of `resolution_charts`'s `rlctAtOn(core) 0 = ⨅ monomialThreshold` equality.
- **`resolution_charts` (`Skeleton.lean:1228`) / `R1ResolutionInterface`** (the ∀-L R1 core resolution):
  CLOSED — `r1_resolution_general M hL hMid hbox` gives `rlctAtOn(core) 0 = ofReal(lambdaCore M)`; the value
  lane converts to the `⨅ monomialThreshold` shape of `resolution_charts`. The `≤`-leg (`cover_ge_div` /
  hdiv) is already banked (`full'`), so `hbox` is the last input.

### 3.2 What the blow-up does NOT close (framing correction — flag for controller)

`Skeleton.lean:1124` and `:1172` are the D1 sorries, and per WALLS-UNIFY §2 the blow-up is **orthogonal**
to them — it FEEDS them (supplies R1's output) but does not close them:

- **`Skeleton.lean:1124`** (`deepest_regular_core_normal_form`, #44, the gauge slice): splits
  `rlctAt(deepestPoint) = nReg/2 + rlctAtOn(core) 0`. This is Aoyagi Lemma 2 + Thm 3 (block normal form) +
  the gauge-slice c-o-v + Fubini additivity — NOT the blow-up. It CONSUMES R1 at `M=H−r` (it needs the core
  value `lambdaCore`, supplied by `r1_resolution_general`). L=2 is **essentially built** on `genm-b3closer`
  (the two-peel chain `D1RectTwoPeelClosed` is sorry-free; `hRne`/`hInterface` the analytic finish).
- **`Skeleton.lean:1172`** (`rlctAt_deepest_le_of_optimal`, the D1 ≥-leg = Aoyagi Thm 4, fibre monotonicity):
  `rlctAt(deepestPoint) ≤ rlctAt(v)` for all optimal `v`. This is a HOMOGENEITY comparison
  (`genm-d1lower` Step 2) proved via radial scaling + `rlctAt_mono`, and a per-`v` constant-rank/Morse
  chart — NOT the blow-up. Its L=2 producer `rlctAt_deepest_le_of_optimal_L2` (`D1SecondPeelGlueL2.lean:60`)
  is a two-peel: first peel → `nReg/2 + slice residual`; second peel → the slice residual IS a degraded
  core `dlnLoss M' 0` (`M'=(m−a,m−a−b,m−b)`), and **GATE 2 `hInterface` = `R1ResolutionInterface` at M'** —
  again CONSUMING R1's output. Plus the per-`v` chart data + the rank bound `hrank₂`.

**So the precise unification:** the blow-up = `hbox` = the `≥`-leg/`cover_le` (WALLS-UNIFY's `le_antisymm`
`≥`-direction). It closes R1 (`resolution_charts`/`r1_resolution_general`) and retires RouteMSchur:426.
R1's OUTPUT (`R1ResolutionInterface`, ∀-width) is then consumed by BOTH the value side (#44, Skeleton:1124)
AND the D1 ≥-leg's GATE 2 (Skeleton:1172). But 1124 and 1172 carry ADDITIONAL, separate content — the
gauge-slice and the per-`v` Morse-with-parameters chart — that the blow-up does NOT supply. The reading
"one blow-up subsumes both the D1 ≥-leg and hbox" is exact ONLY for the WALLS-UNIFY sense (hbox = the
≥-leg of the RLCT equality); it is NOT that the blow-up closes the Thm-4 sorry at 1172.

### 3.3 The full ∀-L headline ladder (what remains after `hbox`)

`aoyagi_learning_coefficient` (`Skeleton.lean:1725`) = `deepest_point_reduction` (D1) ▸ `product_reduction`
(#44 ▸ arithmetic). Three ∀-L sorries remain, in order of coupling to the blow-up:

| # | sorry | ∀-L status | needs blow-up? |
|---|---|---|---|
| R1 | `resolution_charts` (1228) | closed by `r1_resolution_general` modulo `hbox` | **IS `hbox`** |
| D1a | `deepest_regular_core_normal_form` (1124) | L=2 nearly done (genm-b3closer); ∀-L gauge slice open | consumes R1; separate |
| D1b | `rlctAt_deepest_le_of_optimal` (1172) | L=2 producer built; ∀-L per-`v` chart open | consumes R1; separate |

Charge order: **`hbox` first** (unblocks R1, feeds D1a+D1b), then the ∀-L gauge slice (D1a), then the ∀-L
per-`v` Thm-4 producer (D1b). D1a and D1b share the "constant-rank/Morse-with-parameters chart" machinery
(Skeleton:1169 notes obligation (a) of D1b IS the #44 chart machinery), so they can be charged as one
gauge-chart family.

---

## 4. Kill-conditions / risks

**Kill-condition for the `hbox`-is-bounded claim (stated before hunting):** a width vector `M` (some
`L≥3`) at which the per-boundary exponent-shifting peel (sub-lemma 3) CANNOT be built with a monomial
Jacobian of codim exactly `(M₀−t)(M₁−t)` — i.e. the box-integral finiteness at that boundary does not
factor as (monomial)·(reduced box) with the exponent shifted by that boundary's codim. If such an `M`
exists, the arity-L descent (Shape A) fails and Shape B (full (S,J)) becomes mandatory (still bounded per
`genm-d1uniform`, but larger and with the total-chain invariant to machine-check).

Risks, ranked:

- **R1 (highest) — the finite-cover-of-the-box bookkeeping (WALLS-UNIFY's named proviso).** Aoyagi's
  read-off is germ-level at the origin; `hbox` needs `π⁻¹(box)` covered by FINITELY many charts with unit
  factors uniformly bounded above/below, so `∫_box` is a FINITE `Finset.sum` of chart-monomial integrals.
  `genm-d1uniform` proved the (S,J) chart family is finite (bounded lex measure) and each chart's pullback
  of a bounded box stays in a polydisc. Under Shape A this is the finite pivot-minor `Finset` at each
  boundary — bounded, but the machine-check that the charts COVER the whole box (not just a germ) and that
  the unit factors are bounded away from 0/∞ is the one thing the build must not hand-wave. *This is the
  exact shape of the current `IsRouteMCover.cover_le` field — not new, but load-bearing.*

- **R2 — Mathlib change-of-variables for the monomial peels.** Each blow-up step is a `lintegral` change of
  variables under an explicit monomial map. Mathlib has `MeasureTheory.lintegral_image_eq` /
  `MeasurePreserving`/`MeasurableEmbedding` + the `abs_det_fderiv` c-o-v; the depth-2 build already used
  these (`measurePreserving_paramsEquivFlat`, the radial c-o-v in `RouteMSchurRectStep`). Risk is that the
  arity-descent map (which drops a factor's dimension) needs a c-o-v that is a measurable embedding on a
  half-open chart domain, not a global diffeo — the depth-2 charts handle this, so it is a
  generalization, not a gap. *Watch: the rational shear routing (`Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂`) is defined off a
  measure-zero det-locus; the box-unconditional full-rank (brick 4) is what keeps it a.e.-defined.*

- **R3 — the wide-factor-before-bottleneck in the Varah chain (brick 4).** smeared-derisk §5: when a front
  factor is WIDE (`M_j < M_{j+1}`) before the rank bottleneck, the per-factor uniform lower bound is FALSE
  (the wide factor has a kernel); the chain must be phrased as "the leading coordinate stays dominant
  through the chain," not "each factor bounded below." Bounded (the interior tide solved the analogous
  per-layer width bookkeeping) but the sharpest surface; test on `(2,3,1,2,1)` (wide factor + interior
  bottleneck) symbolically before committing the arity-descent plumbing.

- **R4 (framing) — do NOT conflate the blow-up with the D1 sorries.** §3.2: the blow-up closes `hbox`/R1
  only; 1124/1172 are separate ∀-L lifts (gauge slice + Thm-4 per-`v` chart) that CONSUME R1's output but
  are not closed by it. Charging them "for free with the blow-up" would leave silent holes.

---

## 5. Registers

- **Claim (load-bearing, new-tier, SURVIVED first stress-test):** the ∀-L R1 core resolution
  (`resolution_charts`) reduces — in the CURRENT banked Lean — to the single hypothesis
  `hbox : RouteMBoxThresholdFinite M` (a box-integral finiteness), because `r1_resolution_general` closes
  everything else sorry-free (hdiv via `full'`, value lane, bridge, transport, `hfin`-reduction all
  banked). Kill-condition = a banked-sorry hiding in the value lane / achiever / bridge that
  `r1_resolution_general` transitively depends on. STRESS-TEST: read each called lemma's file — achiever
  `full'` (0 sorries), value lane (`routeLayerAtlas_value_eq_lambdaCore`/`_isResolutionAtlas` sorry-free),
  bridge (0 sorries), `hfin`-reduction (modulo `hbox` only). SURVIVED.

- **Claim (design, new-tier):** `hbox` ∀-L is a BOUNDED build (~1100–1900 lines) via an arity-L descent
  (Shape A) mirroring the PROVEN `minAdmRec`, bottoming out on the built L=2 `routeMBoxThresholdFinite_mnp`,
  with per-boundary exponent-shifting peels + a front-product Varah full-rank brick. NOT a research wall
  (contra the r1upper-derisk WALL-for-the-corank-scaffold verdict, which is correct only about THAT
  scaffold). Kill-condition in §4.

- **Most likely to advance the expedition:** landing `hbox` — it is the single unblocker for ∀-L R1, and
  R1's output feeds both D1 sorries. It converts the r1upper "WALL" into a charge.

- **Most likely to break:** the Shape-A per-boundary exponent-shift (sub-lemma 3) — if the box integral at
  a boundary does not factor with the codim shifted correctly, Shape A collapses to Shape B (bigger, +
  total-chain invariant). The next computation that would clarify: symbolically verify, on `(2,2,2,2)`
  (minAdm=3, two active boundaries [1,2]), that stratifying `A⁰·A¹` by rank-1 and blowing up gives a
  monomial factor of codim `(2−1)(2−1)=1` times a reduced `(1,2,2)`-chain box at exponent `c'−½`, and that
  `c'<3/2 ⟹ c'−½ < ½·minAdm(1,2,2)=1`. If the exponent bookkeeping closes on `(2,2,2,2)`, Shape A is the
  route; if not, commit to Shape B.

- **Next computation:** the `(2,2,2,2)` exponent-shift check above (a pen-and-paper/sympy adjudication —
  hand to the `pen-and-paper` seat as a `witness`-style factorization certificate), and the
  `(2,3,1,2,1)` Varah-chain wide-factor test (smeared-derisk §7).

---

## 6. Decorrelated Codex (xhigh, hypothesis withheld)

`codex/linf-recursion-prompt.md` (+ `-answer.md`): framed the target box-integral finiteness + the banked
state + the (S,J) blow-up candidate, WITHHELD my verdict and the `genm-d1uniform` uniformity finding.

**VERDICT MATCHED: BOUNDED (large-but-mechanical), no research-level obstruction for the finiteness
direction** — "if you formalize it as a finite tree of explicit monomial charts with one-sided bounds,
rather than the full ideal-equality/multiplicity proof." Decorrelated agreements on every crux:

- **Q2 (the crux, full decorrelation):** the induction statement must be the WEIGHTED integral
  `Iσ(c') = ∫ wσ·Fσ^{−c'}` carrying the accumulated Jacobian weight; per-step `Fσ∘φ = m²·Fτ·U`,
  `|Jac φ| ≤ C·n`, Tonelli → `Iσ ≤ C·(∏∫₀¹ tᵃ⁻²ᶜ'ᵇ)·Iτ`. "Each step contributes a new monomial power from
  the current boundary while the child carries the previous ones — that is where the sum across boundaries
  enters. The two-matrix corank recursion fails because its induction statement FORGETS that accumulated
  weight." (Independently surfaced my exponent-shift as the load-bearing content — and improved its
  bookkeeping.) Recommends a two-layer split: (i) a combinatorial chart-tree builder on a lex well-founded
  state `(S,J,K)`; (ii) an analytic finiteness induction on that finite tree.
- **Q3 (matched):** (a) don't need the full total-order invariant as a standalone theorem — store as a
  per-chart certificate; (b) don't need exact leaf exponents (value lane banked) — one-sided bounds suffice
  (lower-bound `Fσ∘φ ≥ const·m²·Fτ`, upper-bound `|Jac| ≤ const·m`); (c) organize as a finite `Finset.sum`
  over a finite (even overlapping) chart cover — `∫_union ≤ Σ∫_chart` for nonnegative integrand.
- **Q4 (matched my R1/R2):** biggest burden = germ→whole-box globalization (finite family of local models
  covering all singular points, unit factors bounded away from 0/∞); recommends AVOIDING the general
  diffeomorphism c-o-v API and instead proving custom fiberwise-scaling Tonelli/Fubini lemmas ("the maps are
  triangular enough that this is much cleaner"); package Case 1/Case 2 as a small inductive datatype of
  local configurations, keeping index-transport lemmas separate from measure-theory lemmas.
- **Q5 (matched):** no fundamentally simpler SHARP route — plain arity-L induction or Hölder/Brascamp-Lieb
  is too coarse (forgets accumulated vanishing orders); the only simplification is the weighted "carried
  diagonal-block state" induction, which is the same monomial-blow-up mechanism in disguise. Explicitly
  advises NOT formalizing exact ideal equality, θ, or a general blow-up framework.
- Confirms Mathlib HAS a general integral change-of-variables (since 2022, arXiv:2207.12742), so this is a
  proof-engineering build, not a missing-theorem wall.

Full decorrelation on the verdict AND on the load-bearing crux (the weighted/accumulated-weight induction).
