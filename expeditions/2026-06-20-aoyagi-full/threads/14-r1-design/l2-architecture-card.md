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
