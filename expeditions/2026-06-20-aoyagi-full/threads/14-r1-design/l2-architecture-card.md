# L2 architecture + S1.5 restatement — the smooth-block Fubini lemma

- **Seat:** `pp` (design). **Read-only; /tmp scratch; no Lean.** Task #34 (S1.5/L2-additivity strategy).
- **Verdict:** the abstract disjoint-block additivity (S1.5 as fm-2 found it — FALSE two ways + needs
  Laplace machinery, uncitable) is NOT needed. Replace it with the **smooth-block/monomial Fubini
  lemma**, proven by integrating the smooth block out in closed form. Me + decorrelated Codex agree,
  independently, via the same route.

## The question

After the L2/Theorem-3 split, the loss is, in disjoint variable blocks,
`F = Σ_{i=1}^n x_i² + ‖∏C‖²` (n = r(H¹+H^{L+1})−r² smooth regular coords + the singular core in the
complementary vars). Target `rlctAt F = n/2 + λ_core`. Does L2 need the abstract additivity
`λ(f(x)+g(y)) = λ(f)+λ(g)`?

## Verdict: NO — three options adjudicated

**(a) R1-on-full-loss (resolve regular+core together) — does NOT work directly.** `F = Σx² + core`
is a SUM, not monomial×unit. The regular coords are NOT extra normal-crossing factors: a monomial
zero-set is a union of coordinate hyperplanes, but `Σx² + m² = 0 ⟺ x=0 ∧ m=0`. Even after blowing up
the x-cone (`Σx² = r²·unit`, Jac `r^{n-1}`) the full loss is `r²·unit + m²·unit` — still a sum, S2
inapplicable. Making (a) work needs **mixed principalization of `(x_1,…,x_n, m(u))`** — a genuine
extra resolution theorem, heavier in Lean than the analytic estimate. (Codex + pp agree.) AVOID.

**(b)-general full additivity — AVOID** (fm-2's finding: false without hyps — non-measurable g; g≡0 ⟹
RHS=⊤; and even with hyps needs Laplace/Mellin `L_F(t)L_G(t)~t^{−(λ_F+λ_G)}`, Mathlib-gap, uncitable).

**(b)-special / (c) — THE ANSWER: the smooth-block Fubini lemma.** Integrate the SMOOTH block out in
closed form (the smoothness is exactly what makes it explicitly integrable):

> **S1.5 (restated) — smooth-block Fubini-product RLCT.** In a core normal-crossing chart where
> `core∘φ = unit·∏_j u_j^{2k_j}` and `|det Dφ| = unit'·∏_j |u_j|^{h_j}`, the full loss
> `F = Σ_{i=1}^n x_i² + core` has
> `rlctAt F = n/2 + min_j (h_j+1)/(2k_j)`.
> Equivalently, adding `Σx_i²` shifts the chart's RLCT by exactly `n/2`.

## The proof (light — radial scaling + Fubini, NO Laplace)

The load-bearing identity (verified exactly, sympy `/tmp/l2_scaling_check.py`, n=1,2,3):
> `∫_{|x|<ε} (|x|² + s)^{−c} dx = C(n,c)·s^{n/2−c}` for `s ≥ 0`, with `C(n,c) = ∫(ρ²+1)^{−c}ρ^{n−1}dρ`
> **finite iff `c > n/2`** (substitute `x = √s·ρ`; Beta-function convergence).

Then by **Fubini** (x-block integrated first, `s = core(y) ≥ 0`):
`∫∫ |Σx² + core|^{−c} dx dy = C(n,c) · ∫ |core(y)|^{−(c − n/2)} dy`.
The y-integral is the core's RLCT integral at the **shifted exponent `c' = c − n/2`**, so it converges
iff `c − n/2 < λ_core` iff `c < n/2 + λ_core`. Hence `rlctAt F = n/2 + λ_core`. ∎

Codex's independent asymptotics match: `I_c(A) := ∫_{|x|<ε}(|x|²+A²)^{−c}dx` is bounded for `c<n/2`,
`~log(1/A)` at `c=n/2`, `~A^{n−2c}` for `c>n/2` — same `s^{n/2−c}` scaling, giving the core integral
`∫∏|u_j|^{h_j + k_j(n−2c)} du`, finite iff `c < n/2 + min_j (h_j+1)/(2k_j)`.

**What it needs from Mathlib (all reachable, NO Laplace/Mellin):**
1. the radial-scaling identity `∫(|x|²+s)^{−c}dx = C·s^{n/2−c}` (a polar-coordinates + `x=√s·ρ`
   change-of-variables computation; `C` a Beta integral, finite iff `c>n/2`);
2. Fubini on the product domain (x-block × core-vars), legitimate (nonneg integrand);
3. the shifted-exponent comparison to the core's RLCT (which R1/S2 already supply as
   `min_j (h_j+1)/(2k_j)`).
The smooth-block-ALONE value `rlctAt(Σx²) = n/2` (fm-2 is proving it) is the `core ≡ const` /
`s→` special case — a sublemma, useful but it does NOT combine the blocks by itself.

## Where it lives in the architecture

The restated S1.5 is applied **per chart, inside R1**: each core normal-crossing chart (from the
binding-divisor resolution) carries the regular `Σx²` block alongside; the Fubini lemma shifts that
chart's RLCT by `n/2`. Then
`λ_full = min_chart (n/2 + λ_{core,chart}) = n/2 + min_chart λ_{core,chart} = n/2 + λ_core
       = n/2 + ½·min_t Mval(t)`.
So L2's regular⊕core combination is the Fubini lemma + R1's core resolution + the min-over-charts —
NOT a standalone additivity theorem. The `n = r(H¹+H^{L+1})−r²` regular count is the L2 §3 figure
(½·n = the regular term; design-spec terminology already corrected to "rank-r stratum dim").

## Recommendation (one line)

**Restate S1.5 as the smooth-block Fubini-product RLCT lemma** (`rlctAt(Σx² + monomial·unit, Jac
weight) = n/2 + min_j(h_j+1)/(2k_j)`), prove it by the radial-scaling identity + Fubini (light,
one-citation-clean, NO Laplace), and apply it per-chart inside R1. Drop the abstract additivity (false
+ heavy) and the R1-on-full-loss mixed-principalization (heavier). The smooth-block-alone `n/2` value
is a sublemma. This is L2's analytic engine, one-citation-compliant.

---

## RE-ADJUDICATION 2026-06-21 (fm-2 SPECIFY-phase de-risk + pp + Codex, decorrelated)

fm-2's de-risk REVISES the "light" claim and the hygiene; all three corrections adopted.

### (A) The two directions are NOT symmetric: `≥` light, `≤` heavy

- **`≥` / integrability (LIGHT, ~4–6 sublemmas):** for `c < n/2 + min_j(h_j+1)/(2k_j)`, split
  `c = a+b` (a,b ≥ 0) with the a.e. pointwise comparison `(‖x‖²+G)^{−c} ≤ ‖x‖^{−2a}·G^{−b}` (both
  terms ≥ 0), then `Integrable.mul` over the product domain: x-integral `∫‖x‖^{−2a}` finite iff
  `a < n/2`, y-integral `∫G^{−b}w` finite iff `b < min_j(h_j+1)/(2k_j)`; open ranges cover all `c`
  below threshold. fm-2 building this now (explicit monomial core).
- **`≤` / non-integrability (HEAVIER, ~5–7 sublemmas via the cusp — see (C)):** for
  `c ≥ n/2 + min_j(h_j+1)/(2k_j)`, show the integral `= ∞`. The naive pointwise split goes the WRONG
  way (gives only an upper bound on the integrand). Needs a genuine divergence witness.

### (B) HYGIENE — the lemma MUST use the EXPLICIT monomial core (not abstract G)

For abstract `G ≥ 0, ≢ 0` the lemma is FALSE (germ-local `≡0 → ⊤`, the same trap as the 12th
fidelity issue). STATE it with `G(y) = ∏_j |y_j|^{2k_j}` EXPLICIT, `k_j ≥ 0` integers, and the
Jacobian weight `w(y) = ∏_j |y_j|^{h_j}` in `weightedThreshold`. (The earlier card's `monomial·unit`
must be the literal monomial, not an opaque nonneg G.)

### (C) The CORRECTED radial fact + the LIGHTEST `≤` route (the cusp)

The exact identity `∫_{|x|<ε}(‖x‖²+s)^{−c}dx = C·s^{n/2−c}` holds ONLY for `ε=∞`; for finite `ε`
(an RLCT nbhd) it is only the near-0 asymptotic, and Mathlib has NO parametric radial integral. So the
`≤` route does NOT use that identity. The LIGHTEST `≤` route is the **CUSP lower bound** (pp + Codex,
independently — `/tmp/cusp_route.py`, `/tmp/codex-cusp-answer.md`):

> On the cusp `D = {(x,y) : ‖x‖² ≤ G(y)}` (inside a product nbhd `B_x(0,R)×Q_y` with `Q_y` shrunk so
> `G ≤ R²`): `F = ‖x‖²+G ≤ 2G ⇒ |F|^{−c} ≥ (2G)^{−c}`. By Tonelli (nonneg),
> `∫_D |F|^{−c} w ≥ 2^{−c}·∫_y vol{‖x‖²≤G(y)}·G^{−c}·w dy = 2^{−c}·V_n·∫_y G^{n/2−c}·w dy`
> `= 2^{−c}·V_n·∫ ∏_j |y_j|^{h_j + k_j(n−2c)} dy`, which is `+∞` iff some `h_j+k_j(n−2c) ≤ −1`
> iff `c ≥ n/2 + min_{j:k_j>0} (h_j+1)/(2k_j)`. EXACTLY the threshold. ∎

**THE KEY SHAVE — EXACT ball-volume, NOT a parametric integral** (dodges fm-2's flagged gap): the
`x`-slice contributes `vol{x∈ℝⁿ : ‖x‖²≤s} = V_n·s^{n/2}` (`V_n = vol(unit ball)`), an EXACT scaling of
the unit-ball volume — a **measure of a ball**, not a parametrized radial integral asymptotic. Mathlib
has this (`MeasureTheory.measure_ball` / `addHaar_ball` scaling).

**Three ingredients (all EXACT, Mathlib-reachable) + Tonelli — ~5–7 sublemmas, NOT 10–15:**
(i) cusp containment + `|F|^{−c} ≥ (2G)^{−c}` on `D` [a.e. monotone];
(ii) EXACT ball-volume `vol{‖x‖²≤s} = V_n·s^{n/2}` [scaling, NOT parametric];
(iii) monomial divergence `∫∏y_j^{a_j} = ∞ iff some a_j ≤ −1` — **REUSE S2** (Codex shave: the cusp-
volume step produces a pure monomial `∏|y_j|^{h_j+k_j(n−2c)}` in `y`, exactly S2's input, so divergence
reuses the existing S2 result rather than re-proving it);
(+) Tonelli for the `∫_D = ∫_y∫_x` split (nonneg integrand).
*Not lighter:* single-`y_j`/1-D reduction (annulus/box bookkeeping — pp + Codex agree).

### (D) The FULL equality IS needed for R1's UPPER bound (confirmed)

R1's binding chart has `F = Σx² + monomial-core`. S2 (the cited normal-crossing fact) covers a PURE
monomial, NOT `Σx²+monomial`. The `+Σx²` shifts the threshold by `n/2`; without the `≤`
(non-integrability at the threshold) we get only `rlctAt ≥ n/2 + monomial-threshold`. So the `≤`
(cusp) is REQUIRED for `rlctAt ≤ n/2 + …` ⟹ the R1 upper bound. **Do NOT try to fold `Σx²` into S2
via a normal-crossing change of variables** — `Σx²` is smooth radial data, not a coordinate monomial
product (pp + Codex agree); the cusp-volume argument is the clean replacement for the missing
normal-crossing form. The cusp is unavoidable but light (the ball-volume scaling is the trick).

---

## L2 BUILD STATE (crux2, 2026-06-22) — `origin/fm2/deepest-gauge-chart`

The value-free L2 reduction `deepest_regular_core_reduces` (split APPROVED #44):
`rlctAt (dlnLoss H B) deepest = nReg/2 + rlctAtOn (dlnLoss M 0) 0`. R1's core value folds separately
(`▸ resolution_charts`). Modules: `Validate/DeepestGaugeChart.lean` (structure + 7 sub-lemmas +
assembly), `Foundations/S1Spectator.lean` (the reusable spectator-peel). NOT yet in the aggregator
(controller wires).

PROVEN (green, axiom clean-three):
- `rlctAtOn_spectator_peel` (S1Spectator) — loss-independent factor is RLCT-neutral; reusable for D1 #42.
- sub-2 `deepestPoint_is_rank_exact` (= `deepestPoint_isDeep.2`).
- sub-7 `deepest_reduced_core_identification` (reduced core flat↔Params via `paramsEquivFlat M`).
- The structure `DeepestGaugeChart` (g147 interface; refined: `split_mp`, `split_zero`).
- The assembly `deepest_regular_core_reduces` composes the sub-lemmas green.

OPEN (3 named sorries):
- sub-3/4 `deepest_gauge_chart_exists` — the XL g150-cert block algebra (#44c, hero-piece).
- sub-5 `deepest_nonMP_chart_transport_unit` — `weightedThreshold_transport` (homeo chart) + `jac_unit`
  weight peel + `loss_form` germ + `chart_zero`. ~100-150 lines.
- sub-6 `deepest_regular_smooth_split` — route built+mapped in-comment (split MP transport + additive
  block + spectator-peel + sub-7), reverted to clean sorry pending TWO sub-obligations below.

TWO CERT GAPS found in the build (NOT in g150/g147 — decorrelation catch):
1. **`hGne` (reduced-core germ-nonvanishing).** `rlct_additive_smooth_block` is FALSE for a
   germ-vanishing block. So sub-6 needs `dlnLoss M 0 ≠ 0` a.e. near the deepest core point. Holds when
   the reduced chain `M = H−r` is non-degenerate (zero-product locus is a proper subvariety); FAILS if
   some interior `M_s = 0`. Now a hypothesis of sub-6 + `deepest_regular_core_reduces`, discharged at
   spine wiring. The cert noted `dlnLoss_nonneg` (sqrt wrapper) but missed nonvanishing.
2. **`Measurable (dlnLoss M 0)`.** Needed for `rlct_additive_smooth_block`'s `hGmeas`. `fun_prop`
   deep-recurses on `prodAux`; needs a hand `continuous_prodAux` (induction; the `prodAux` definitional
   `Fin.cast` makes the entry-product `show` fiddly — a focused cast-handling mini-lemma). Reusable
   bedrock (every `rlctAtOn` integrand site). Can't live in `Loss.lean` (no `Params` topology there —
   `Params` is a def wrapper, instance is in `Rlct.lean`); home is downstream of `Rlct`.

### Update (crux2, 2026-06-22, later) — gap #2 CLOSED; sub-6 now plumbing-bound

Cert-gap #2 (`Measurable (dlnLoss M 0)`) is **CLOSED**: `continuous_prodAux`/`continuous_prod`/
`continuous_dlnLoss` PROVEN in `DeepestGaugeChart.lean` (local helpers, lift to Foundations at #28).
The `prodAux` `Fin.cast` that stalled 3 solo attempts — Codex (g151, xhigh) gave the idiom: define
`layer` via the same `rw [e1,e2]` block, prove `Continuous layer` by
`simp only [e1, e2, eq_mpr_eq_cast, cast_eq]` reducing the cast to `continuous_apply`, then
`Continuous.matrix_mul` + `hMul.congr … rfl`. Build green (2673), axiom clean-three.

sub-6 `deepest_regular_smooth_split` is now **plumbing-bound** (no conceptual blocker): the route
(split MP transport → additive block → spectator-peel → sub-7) is built; the two residual plumbing
steps are (a) lift `hGne` (core a.e.) to the product nbhd via `quasiMeasurePreserving_fst`/`.ae`, and
(b) the 3-way `(reg)×((core)×(spec))` reassociation so the spectator-peel and additive block apply.
Both reachable; reverted to a clean mapped `sorry` pending a focused fill.

### Update (crux2, 2026-06-22, R-SQUEEZE) — value-free reduction consuming side FULLY PROVEN

The sub-34 worker's g152/g153 decorrelated finding (raw-∏T squeeze REFUTED; global `chart : Flat ≃ₜ
Flat` over-reaches — honest gauge slice is a LOCAL diffeo) prompted the interface call (crux2 owns it):
**R-SQUEEZE.** `DeepestGaugeChart` trimmed of `chart`/`Dchart`/`hasDeriv`/`jac_unit`/`loss_form`-equality
→ a `loss_squeeze` datum (`c₁Φ ≤ dlnLoss∘flat ≤ c₂Φ` near the deepest point, `Φ = ∑reg² + dlnLoss M 0
core`). Kept `nGauge`/`split`/`split_mp`/`split_basepoint`.

PROVEN (axiom clean-three, `origin/fm2/deepest-gauge-chart @c1ce00f`):
- sub-2, sub-5 (`deepest_squeeze_transport`: `rlctAtOn_eq_rlctAt` + Params→flat MP + `rlctAtOn_squeeze`),
  sub-6 (smooth-split, re-based to `wstar`), sub-7, the assembly `deepest_regular_core_reduces`.
- Foundations bedrock: `rlctAtOn_spectator_peel`, `continuous_prodAux/_prod/_dlnLoss`,
  `weightedThreshold_weight_unit_invariant`, `rlctAtOn_mono`/`rlctAtOn_squeeze` (re-homed to
  S1NonMPTransport from GeneralR1Recursion — Foundations-grade, 2nd use).

OPEN — ONLY sub-3 `deepest_gauge_squeeze_exists` (the sub-34/#53/#54 obligation against the trimmed
structure): the MP `split` reindex + the two-sided `loss_squeeze` whose content is the matrix-core
comparability `‖T·(I−VY)⁻¹·S‖² ≍ dlnLoss M 0(core)` (gauge-normalized core, NOT raw ∏T).

Net: the value-free L2 reduction is PROVEN-modulo the single squeeze-datum existence. The two cert gaps
(hGne — threaded hypothesis; dlnLoss-measurability — closed via Codex g151) both resolved.

### Update (crux2, 2026-06-22, coreEmbed fix) — gauge-normalized core via coreAbsorb

cobuild-sub34's g153 (decorrelated, exact-numeric + Codex) caught a REAL flaw in the R-squeeze
structure: the hardcoded `(paramsEquivFlat M).symm` core + the MP `split` force the RAW `∏T` chain,
making `loss_squeeze` FALSE (`‖T·g·S‖²/‖T·S‖²→∞`, g=(I−VY)⁻¹ between layers). The producer caught a
consumer-interface bug — decorrelation working.

Fix (Codex g154, winner "design D"): keep `split` MP (core slot = raw `T`); add a `coreAbsorb`
self-homeo absorbing the gauge unit into the core (fixing reg/spectator slots) + the producer field
`coreAbsorb_rlct` (absorbed-Φ and raw-disjoint-Φ have the same RLCT — the g-unit peel, via
`weightedThreshold_transport` + `weightedThreshold_weight_unit_invariant`). `loss_squeeze`/`Φ` use the
absorbed (T̃-normalized) core; sub-6 inserts one `rw [coreAbsorb_rlct]` before the additive block.

Consuming side (sub-5/6/7 + assembly + `ofExactGerm`) re-proven axiom clean-three against the
gauge-normalized core (`@bd016d0`). The raw-∏T trap is now structurally impossible. The single open
obligation is `deepest_gauge_squeeze_exists` (cobuild-sub34's `ofExactGerm` target: split + coreAbsorb
+ the one hard `coreAbsorb_rlct` + `loss_germ`). #54 (Schur core = dlnLoss M 0 T̃) feeds both.

### Update (crux2, 2026-06-22) — D1 ≥-leg CORE fully proven

`origin/fm2/d1-deepest-min @152ef0d` (rebased onto deepest-gauge-chart for S1NonMPTransport),
`Validate/DeepestMinRlct.lean`, zero sorries, all axiom clean-three:
- `rlctAtOn_ray_scaling_invariant` (L1-a): `rlctAtOn F (t•v) = rlctAtOn F v` for homogeneous `F`,
  `t>0` — the scaling `σ=t•·` (det `t^N`) via `weightedThreshold_transport` + `weightedThreshold_weight_unit_invariant` (the `t^N` weight peel) + homogeneity + `rlctAtOn_unit_invariant_aux` (the `t^D` function peel).
- `rlctAtOn_lsc_at_origin` (L1-b): `rlctAtOn F 0 ≤ rlctAtOn F v` — the LIGHT nbhd-monotonicity from the
  `sSup`/`∃Ω∋·` def (the controller's `rlctAt`-hint, g170; g160's "heavy Watanabe/Varchenko primitive" was an overestimate).
- `deepest_le_of_homogeneous_core`: the D1 (a) CORE, = L1-b.

The hero-task constraint (only S2 citable) HOLDS for the D1 ≥-leg core: "deepest = min-core" is PROVEN
value-free, NO Aoyagi 2013 Thm 2 citation, NO new analytic primitive. g158's "rlctAt_mono is
2-funcs-1-point, D1 is 1-func-2-points" gap is bypassed by the L1-a (ray-constancy) + L1-b (limit
nbhd-monotonicity) decomposition. Remaining: the full-B bridge (CORE → full `dlnLoss H B`) via L2 +
the constant fibre-rank shift (g170 route 1).

### Update (crux2, 2026-06-22) — #59 obligation (i) `split` DELIVERED (`origin/fm2/split-reindex`)

The `split` field (gauge-slice MP reindex) of `DeepestGaugeChart` is PROVEN sorry-free in
`Validate/DeepestSplitReindex.lean` (axiom clean-three, no `monomial_rlct`). Three theorems:
- `layer_block_count {a b r} (r≤a)(r≤b) : a*b = (a−r)(b−r) + r(a+b−r)` — per-layer block identity.
- `flatDim_deepest_split H r hr hL : flatDim H = deepestNReg H r + flatDim (deepestM H r)
  + deepestNGauge H r` — the load-bearing dimension identity (`deepestNGauge := flatDim H − nReg −
  flatDim M ≥ 0`; surplus `= r(2·Σ_interior H_i − (L−1)r) ≥ 0` via each interior `H_i ≥ r`).
- `deepestSplit_exists H r hr hL wstar : ∃ split : (Fin (flatDim H) → ℝ) ≃ₜ
  DeepestSplit H r (deepestNGauge H r), MeasurePreserving split volume volume ∧ split wstar = 0`.
  Built per cobuild-sub34's g159 recipe (relabel+translation, NOT matmul — det=±1, MP):
  `translation (measurePreserving_sub_right) ∘ relabel (volume_measurePreserving_piCongrLeft via
  Fintype.equivOfCardEq on the dimension identity) ∘ unpack (volume_measurePreserving_sumPiEquivProdPi
  ×2)`. The g125-vs-structure MP tension is resolved (g157, recorded above): the unit-Jacobian content
  stays in cobuild-sub34's `coreAbsorb` (non-MP); `split` is the pure MP reindex.

SEAM-verified: a scratch confirmed `deepestSplit_exists` discharges the `split`/`split_mp`/
`split_basepoint` fields at `nGauge = deepestNGauge H r`, `wstar = paramsEquivFlat (deepestPoint ...)`.
HONEST factoring: the split's three fields do NOT pin the slot SEMANTICS (regular = g125 pivots, core
= `FlatIdx (deepestM H r)` raw `T_s`) — those are pinned only by `loss_squeeze`, so cobuild-sub34
realizes the concrete partition when wiring (ii)–(iv). g159 flags the `coreAbsorb` GLOBAL homeomorphism
+ its Jacobian as "the wall" — cobuild-sub34's remaining XL.

### FIDELITY FINDING (crux2, 2026-06-22) — interior-only hMid does NOT imply hGne

Threading the locked `hMid` (`∀ s : Fin L, 0 < s.val → r < H s.castSucc`, interior H_1..H_{L-1}) into
the L2 lemmas surfaced a gap. The L2 lemmas (`deepest_regular_smooth_split`,
`deepest_regular_core_reduces`) take the analytic `hGne` (`dlnLoss M 0 ∘ flatSymm ≠ 0` a.e. near 0).
**`hGne` does NOT follow from interior-only `hMid`** — it needs `r < H_s` for ALL `s` (all reduced
widths `M_s = H_s − r ≥ 1`), endpoints included:
- `M_0 = 0` (r = H_0, B full row rank): `prod_M` is `0 × M_L` → no entries → `dlnLoss M 0 ≡ 0` → hGne FAILS.
- `M_L = 0` (r = H_L): `prod_M` is `M_0 × 0` → hGne FAILS.
- interior `M_s = 0`: `prod_M ≡ 0` → hGne FAILS (this one IS covered by hMid).
All numerically verified. The endpoint cases are reachable under `hr : ∀ s, r ≤ H s`. Since
`rlct_additive_smooth_block` is FALSE for a germ-vanishing block, the M_0=0 case breaks the current
L2 proof route.

RESOLUTION PENDING controller/fm3 verdict:
- (A) widen the locked form to `r < H_s` for ALL s (contradicts fm3's interior-only lock — needs R1
  re-confirm);
- (B) keep interior-only + add a degenerate-endpoint branch (M_0=0 or M_L=0 ⟹ core RLCT 0, separate route).

THE `hMid ⟹ hGne` BRIDGE (non-degenerate all-s case) — HEAVY, roadmap-grade. Two pieces:
1. `prod_M ≢ 0` when all `M_s ≥ 1` (constructive: an explicit nonzero-product witness). Tractable.
2. `{A : dlnLoss M 0 A = 0}` measure-zero. Mathlib has NO multivariate "nonzero analytic/poly ⟹ ae ne
   zero" (only 1-D `IsolatedZeros`). From-scratch: induct on #vars + Fubini to 1-D slices + univariate
   finite-roots (`Polynomial.setOf_isRoot_finite`). ~150–250 LoC standalone. Shared R1+L2 obligation.
