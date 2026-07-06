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

## 0. THE SHARED CRUX — DLN model-identification (from the gatesclose2 L=2-close assessment)

The L=2-close thread (`genm-gatesclose2`) found the pivotal shared crux, and it reshapes the load-bearing
analytic content of the WHOLE endgame — including this ∀-L design. Recording it as §0 because it is the
invariant BOTH the R1 box-finiteness recursion AND the D1 ≥-leg recursion maintain.

### 0.1 The concrete-residual discipline (the ∀-q gates are provably FALSE)

The L=2 D1 ≥-leg was wired through an **abstract ∀-`q` gate** (`hD1ge_L2_rect_of_gates`,
`D1RectHeadlineWire.lean`) demanding two properties for EVERY `C²` residual `q`. Both are **false as
literally stated** (decorrelated-Codex + gatesclose2 analysis):

- `hRne` (slice non-vanishing) fails on `q ≡ 0` (trivial-core stratum: chart equation holds, slice `≡ 0`).
- `hInterface` (degraded-core value) fails on `R = x² + u⁴`: peeling the `x`-square gives built residual
  `q₂ = u²`, slice `u⁴`, `rlctAtOn = 1/4 ≠ lambdaCore(M')`.

**FIX (architectural — binds this ∀-L design too):** bind `q`/`q₂` to the **CONCRETE producer residual**
(as `d1ge_L2_rect_two_peel_hrank_closed` constructs) and discharge the properties for THAT residual, where
b3's rank fact and the DLN structure live — then retire the ∀-`q` wire. **This ∀-L design uses CONCRETE
charts/residuals throughout, never ∀-`q` abstract gates.** (Codex independently reached the same via Q3(a):
"store as a per-chart CERTIFICATE, not a global algebraic theorem" — the chart certificate IS the concrete
residual + its model-identification.)

### 0.2 The model-identification lemma (the load-bearing analytic content)

> **Crux (`degraded_slice_is_core_up_to_bounded_unit_local_diffeo`, ∀-L).** A DLN-loss residual germ `R` —
> the slice left after peeling regular/rank blocks at a stratum with degraded reduced widths `M'` — equals
> the **reduced-core DLN model up to a bounded unit and a local diffeo**: `R = U · (dlnLoss M' 0) ∘ φ` near
> the base point, with `U` bounded away from `0` and `∞` and `φ` a local `C¹` diffeomorphism.

This is **Aoyagi's Step-0 + Step-1 model-identification** (`genm-d1lower`): Step-0 = the Gram-sandwich
(`α₁·Σh̃² ≤ K ≤ α₂·Σh̃²`) making the integral loss `=` the algebraic reduced-core up to a bounded positive
unit; Step-1 = the block reduction (`P₁(∏A)P₂ = diag(C1, ∏C')`) exposing the reduced core `∏C'`.
Consequence, via the **BANKED** bounded-unit + diffeo RLCT-invariance (`rlctAtOn_unit_invariant_aux`
`S1Local.lean:139`, `rlctAtOn_comp_homeomorph` `S1Fubini.lean:54`, `rlct_unit_invariant` `Skeleton:201`):
`rlctAtOn R (base) = rlctAtOn (dlnLoss M' 0) 0`, closed by `r1_resolution_general M' … hbox`. **The crux is
the IDENTIFICATION; the wrapping is banked** — which is why "hard-but-bounded, not a wall" (Aoyagi does it).

### 0.3 Why it is the shared crux — it recurses down the blow-up, and R1 IS its origin instance

The identification is **recursive**: `dlnLoss M' 0` is itself a DLN core, so peeling ITS next rank-drop
boundary yields a smaller `dlnLoss M'' 0 · (bounded unit) ∘ (diffeo)` — the SAME shape, one boundary
shallower — down to the deepest stratum. The recursive OBJECT is "a DLN reduced-core model `dlnLoss M' 0`,
up to a bounded unit ∘ local diffeo"; the per-step lemma is the model-identification.

- **R1 (box finiteness) IS the origin instance.** At the deepest point the top-level unit is `1` and the
  identification is EXACT: `dlnLoss M 0 = frobSq(prod M A)` (`dlnLoss_zero_eq_frobSq`, banked). Each blow-up
  step of the box-finiteness recursion (Codex's weighted form `Fσ∘φ = m²·Fτ·U`, `a≤U≤b`) is this SAME
  identification with a per-step bounded unit `U` and reduced core `Fτ = frobSq(smaller product)`.
- **D1 ≥-leg consumes it at a general `v`.** There the top-level unit is nontrivial (the Gram-sandwich),
  and the peel chain identifies the residual as a degraded core, recursively to the deepest — mirroring the
  blow-up. **The L=2 close (one peel: `v` → `nReg/2` + degraded core `M' = MprimeRect`) is the BASE INSTANCE
  of this recursion.**

**So ONE model-identification build (+ the banked invariance wrappers) serves BOTH the L=2 headline close
AND the ∀-L unified build.** The two consumers wrap it differently — R1 sums the per-step monomial
contributions for FINITENESS; D1 sums the per-peel codims for the VALUE comparison — but the per-step
IDENTIFICATION is one lemma. It is the same Step-0/Step-1 the whole expedition already relies on, made an
explicit recursive lemma; bounded-but-hard, not a wall.

### 0.4 The L=2 four-lemma runway = the base instance of the ∀-L decomposition

The gatesclose2 runway (shortest-first; only `slice_zero_set_caps_rlct_half` exists, in
`HeadlineL2Assembly.lean`; the other three are the runway) is the L=2 instance of the ∀-L
model-identification decomposition:

| L=2 lemma (gatesclose2) | role | ∀-L generalization |
|---|---|---|
| `slice_zero_set_caps_rlct_half` (moderate; `C¹`-in-`s`) | pos-measure slice zero-set ⟹ `rlctAtOn ≤ nReg/2` | the per-peel regular-block cap (the `≤` half of each peel's value) |
| `slice_ae_nonzero_of_posrank_jacResid` (moderate; rank thm) | `rank(jacResid q t0) ≥ 1` ⟹ slice a.e.-nonzero — the CONCRETE-`q` route to `hRne`, off b3's banked rank fact (avoids the circular `rlctAt v > nReg/2`) | per-peel: the concrete residual's Jacobian has the right rank ⟹ non-degenerate stratum ⟹ slice a.e.-nonzero |
| **`degraded_slice_is_core_up_to_bounded_unit_local_diffeo`** (hard; the crux) | 2nd-peel residual `R₂ = U·(dlnLoss M' 0)∘φ` | **THE ∀-L crux (§0.2), recursively down the blow-up** |
| `degraded_slice_rlct_eq_lambdaCore` (bounded once crux lands) | value (b) from crux + `r1_resolution_general` + invariance; nullity (a) from crux + polynomial zero-set transport | per-peel value + non-vanishing, from the crux + banked invariance |

Then a concrete `d1ge_L2_rect_two_peel_closed` (CONSTRUCTS `q`/`q₂` internally, discharges the properties
via the 4 lemmas) closes L=2 LEAF 2 → sorry-free `aoyagi_learning_coefficient_L2`, retiring the ∀-`q` wire.

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
   the analog of the corank per-step, re-cast to descend arity and shift the exponent.* **This peel IS the
   §0 model-identification at the origin** (Codex's `Fσ∘φ = m²·Fτ·U`, `a≤U≤b`): `Fτ = frobSq(prod_reduced)`
   is the smaller DLN core and `U` the bounded unit — so building sub-lemma 3 and the §0 crux is one shared
   effort (R1's origin instance vs D1's general-`v` instance of the SAME per-step identification).

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
  core `dlnLoss M' 0` (`M'=(m−a,m−a−b,m−b)`) **via the §0 model-identification crux**, and **GATE 2
  `hInterface` = `R1ResolutionInterface` at M'** — CONSUMING R1's output. Plus the per-`v` chart data + the
  rank bound `hrank₂`. **NB (gatesclose2):** the current `hD1ge_L2_rect_of_gates` wire states GATE 2 ∀-`q`,
  which is PROVABLY FALSE (§0.1); the ∀-L build must bind `q`/`q₂` to the concrete producer residual.

**So the precise unification:** the blow-up = `hbox` = the `≥`-leg/`cover_le` (WALLS-UNIFY's `le_antisymm`
`≥`-direction). It closes R1 (`resolution_charts`/`r1_resolution_general`) and retires RouteMSchur:426.
R1's OUTPUT (`R1ResolutionInterface`, ∀-width) is then consumed by BOTH the value side (#44, Skeleton:1124)
AND the D1 ≥-leg's GATE 2 (Skeleton:1172). 1124 and 1172 carry ADDITIONAL content — the gauge-slice and the
per-`v` chart — the blow-up does NOT supply; but **that content's load-bearing analytic core IS the §0
model-identification crux, which is the SAME per-step lemma R1's box-finiteness recursion uses at the
origin.** So the honest unification is two-level: (i) the blow-up = `hbox` closes R1 and feeds R1's value
into 1124/1172 (the WALLS-UNIFY `≥`-leg sense — exact); (ii) ONE model-identification crux (§0) is the
per-step analytic content shared by R1's recursion and the D1 peels — proving it once serves the L=2 close
AND the ∀-L build. The reading "one blow-up subsumes both the D1 ≥-leg and hbox" is exact for sense (i)
(hbox = the ≥-leg of the RLCT equality); it is NOT that the blow-up closes the Thm-4 sorry at 1172 — that
needs the model-identification crux + the per-`v` chart, which sense (ii) supplies.

### 3.3 The full ∀-L headline ladder (what remains after `hbox`)

`aoyagi_learning_coefficient` (`Skeleton.lean:1725`) = `deepest_point_reduction` (D1) ▸ `product_reduction`
(#44 ▸ arithmetic). Three ∀-L sorries remain, in order of coupling to the blow-up:

| # | sorry | ∀-L status | needs blow-up? |
|---|---|---|---|
| R1 | `resolution_charts` (1228) | closed by `r1_resolution_general` modulo `hbox` | **IS `hbox`** |
| D1a | `deepest_regular_core_normal_form` (1124) | L=2 nearly done (genm-b3closer); ∀-L gauge slice open | consumes R1; separate |
| D1b | `rlctAt_deepest_le_of_optimal` (1172) | L=2 producer built; ∀-L per-`v` chart open | consumes R1; separate |

Charge order: **`hbox` first** (unblocks R1, feeds D1a+D1b), then the **§0 model-identification crux**
(the shared analytic content — closes the L=2 headline NOW and is the per-step of both D1a and D1b at ∀-L),
then the ∀-L gauge slice (D1a) + per-`v` Thm-4 producer (D1b). D1a and D1b share the model-identification +
the "constant-rank/Morse-with-parameters chart" machinery (Skeleton:1169 notes obligation (a) of D1b IS the
#44 chart machinery), so they charge as one gauge-chart family on top of the crux. **The crux is the
highest-leverage single build: it is the base-instance of the L=2 close (unblocking the headline today) AND
the per-step of the ∀-L D1 recursion** — a "build it once, use it at every L and every peel" lemma.

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

- **R5 (the model-identification crux, §0) — the ∀-`q` trap + the hard-but-bounded diffeo/unit.** Two
  sub-risks. (a) The **∀-`q` framing is provably false** (gatesclose2 §0.1: `q≡0` kills `hRne`, `R=x²+u⁴`
  kills `hInterface`) — the build MUST bind residuals to the concrete producer, never state a ∀-`q` gate;
  re-checking a gate is a ∀-`q` statement before proving it is the guard. (b) The identification
  `R = U·(dlnLoss M' 0)∘φ` itself (bounded unit `U` away from 0/∞, `φ` a local `C¹` diffeo) is the genuine
  hard-new-analysis (Aoyagi Step-0/Step-1); the RLCT-invariance WRAPPER is banked
  (`rlctAtOn_unit_invariant_aux`/`_comp_homeomorph`), so the residual is exactly the identification, not the
  invariance. Kill-condition: a stratum where the second-peel residual is NOT a bounded-unit·diffeo image of
  a DLN reduced core (would break both L=2 and ∀-L). The gatesclose2 `R=x²+u⁴` case shows this fails for an
  ARBITRARY `C²` residual — the identification is true only for the CONCRETE DLN-structured residual, which
  is why (a) and (b) are coupled.

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

- **Claim (shared-crux, new-tier — from gatesclose2):** the model-identification
  `degraded_slice_is_core_up_to_bounded_unit_local_diffeo` (residual `= U·(dlnLoss M' 0)∘φ`, §0.2) is the
  ONE analytic lemma shared by the L=2 headline close (its base instance, one peel) and the ∀-L D1 recursion
  (per-peel, down the blow-up); it is Aoyagi Step-0/Step-1, bounded-but-hard, with the RLCT-invariance
  wrapper banked. Kill-condition: a stratum whose concrete second-peel residual is not a bounded-unit·diffeo
  image of a DLN reduced core (R5). Must be proved for the CONCRETE residual (the ∀-`q` version is FALSE).

- **Most likely to advance the expedition:** two, coupled. (i) landing `hbox` — the single unblocker for
  ∀-L R1 (converts the r1upper "WALL" into a charge); (ii) landing the §0 model-identification crux — it
  closes the L=2 headline TODAY (retiring the false ∀-`q` wire) and is the per-step of the ∀-L D1 recursion.
  The crux is the higher-leverage single build (base-instance-of-L=2 AND per-step-of-∀-L).

- **Most likely to break:** the Shape-A per-boundary exponent-shift (sub-lemma 3) — if the box integral at
  a boundary does not factor with the codim shifted correctly, Shape A collapses to Shape B (bigger, +
  total-chain invariant). The next computation that would clarify: symbolically verify, on `(2,2,2,2)`
  (minAdm=3, two active boundaries [1,2]), that stratifying `A⁰·A¹` by rank-1 and blowing up gives a
  monomial factor of codim `(2−1)(2−1)=1` times a reduced `(1,2,2)`-chain box at exponent `c'−½`, and that
  `c'<3/2 ⟹ c'−½ < ½·minAdm(1,2,2)=1`. If the exponent bookkeeping closes on `(2,2,2,2)`, Shape A is the
  route; if not, commit to Shape B.

- **Next computation:** (i) the `(2,2,2,2)` exponent-shift check above (pen-and-paper/sympy `witness`-style
  factorization certificate); (ii) the `(2,3,1,2,1)` Varah-chain wide-factor test (smeared-derisk §7);
  (iii) **the model-identification crux on the concrete L=2 second-peel residual** — symbolically exhibit
  `R₂ = U·(dlnLoss (MprimeRect …) 0)∘φ` with `U` bounded away from 0/∞ and `φ` a local `C¹` diffeo, for the
  CONCRETE `q₂` that `d1ge_L2_rect_two_peel_hrank_closed` builds (NOT ∀-`q₂`). This is the base-instance
  certificate that unblocks BOTH the L=2 headline close and the ∀-L D1 recursion; it is the single
  highest-leverage adjudication to hand the `pen-and-paper` `witness` seat next.

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
