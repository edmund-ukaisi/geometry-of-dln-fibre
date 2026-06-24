# R1 EXECUTION handoff — pen-and-paper → formaliser (pp leads, fm formalises)

- **Seat:** `pp` (leads the math). **fm formalises.** Task #11. Trunk @`c32b694` (S1.1/S1.3/S1.4 closed,
  Fubini engine closing). R1 needs NO domain hypothesis (rv-2 sweep: SAFE at every corner).
- **Target:** `resolution_charts (H) (B) (wstar) : ∃ ι [Fintype ι] (d k h), rlctAt H (dlnLoss H B) wstar
  = ⨅ i, monomialThreshold (d i) (k i) (h i)`. Genuine (rlctAt = opaque sSup; the ∃ must encode the
  resolution data). The docstring's "exponents range over exactly Adm" is STALE — the deliverable is
  the VALUE-MATCH, NOT a chart↔Adm set-bijection (charts outnumber strata; thread-14 corrections).

## The decomposition (R1.1–R1.7; UPPER cheap, LOWER the real work)

| # | sub-lemma | status / who |
|---|---|---|
| R1.1 | chart family `ι` = pivot branches of the iterated L1; per chart `(d_i,k_i,h_i)`, k=1 per exceptional divisor | construct (REUSES L1) — the geometric mountain |
| **R1.2** | **multiplicity-control / divisor-ratio** (the per-divisor estimate) — SEE BELOW, the FIRST handoff | pp states, fm formalises NOW |
| R1.3 | `codim S(t) = Mval(t)` (nested Schur-block residual = regular sequence) | thread-03 proven (pen+paper) → Lean |
| R1.4 | Fubini-per-chart `rlctAt(Σx² + core) = n/2 + rlctAt(core)` | fm-2's S1Fubini (closing) |
| R1.5 | S1.1 min-over-cover `rlctAt = ⨅ charts` | `weightedThreshold_transport` (trunk, S1.1) |
| R1.6 | cover/exhaustiveness (pivot branches partition `{core=0}`) | construct — the residual real work |
| R1.7 | S2 `monomial_rlct` (the ONE axiom): `monomialThreshold d k h = ⨅_j axisRatio (h j)(k j)` | cited (trunk) |

UPPER (`rlctAt ≤ …`): R1.1+R1.2 binding divisor on the min stratum (via R1.3) — ONE chart, cheap.
LOWER (`rlctAt ≥ …`): R1.2-over-all-divisors + R1.6 cover + R1.5 min — the real work.
Use-site OBLIGATIONS folded into R1.2/assembly: (1) unit-absorption via `rlct_unit_invariant` (chart
core = unit·monomial, NOT pure monomial — strip the unit BEFORE S2); (2) hcore_top endpoint (pin its
form — strict-above is free from the down-set; at-endpoint needs the monomial `∫|y|^{−1}=∞` fact).

## ★ FIRST HANDOFF — R1.2 ARITHMETIC CORE (self-contained ℝ≥0∞, NO geometry, fm starts NOW) ★

The divisor-ratio is `axisRatio h k = (h+1)/(2k)` (trunk def). The regular-sequence structure gives
`k=1, h=c−1` for a binding divisor over a codim-`c` stratum. Two pure-arithmetic lemmas, fully
decoupled from the chart construction — fm can formalise these immediately:

```
-- R1.2a: the regular-sequence divisor ratio (k=1, h=c−1 ⟹ ratio c/2). c = Mval(t) = codim.
theorem axisRatio_regularSeq (c : ℕ) (hc : 1 ≤ c) :
    axisRatio (c - 1) 1 = (c : ℝ≥0∞) / 2
-- proof: axisRatio (c-1) 1 = ((c-1)+1)/(2·1) = c/2 (Nat.sub_add_cancel hc; ENNReal arith).

-- R1.2b: multiplicity control (the lower-bound inequality, ANY divisor with k≥1).
theorem axisRatio_ge_of_mult (h k m : ℕ) (hk : 1 ≤ k) (hmult : m * k ≤ h + 1) :
    (m : ℝ≥0∞) / 2 ≤ axisRatio h k
-- proof: axisRatio h k = (h+1)/(2k) ≥ (m·k)/(2k) = m/2  (hmult + ENNReal div monotone).
--   This is the multiplicity-control mechanism: m = min_t Mval; for our core k=1, h=c−1,
--   so m·k = m ≤ c = h+1 (since c = Mval(t') ≥ m = min Mval). The k≥2 case never occurs
--   (regular sequence ⟹ k=1), but the lemma is stated generally for robustness.
```

Verified (`/tmp/r12_arith.py`): `axisRatio(c−1, 1) = c/2` for c=1..5 ✓; the ≥ from `m·k ≤ h+1`.
These two are the formalizable seed of R1.2 — `ℝ≥0∞` `div`/`le` lemmas, no measure theory, no
charts. **Hand fm R1.2a + R1.2b first.** They feed BOTH the upper bound (R1.2a: binding divisor
realises `Mval(t)/2`) and the lower bound (R1.2b: every divisor `≥ min Mval /2`).

## R1.2 — the GEOMETRIC content (the k=1 mechanism, after R1.1 lands) — Codex-sharpened

The arithmetic (R1.2a/b) takes `(k,h)=(1,c−1)` as GIVEN. The geometric content — WHY `k=1, h=c−1` —
is the multiplicity-control mechanism, provable once R1.1 supplies the charts. **Codex sharpened the
`k=1` hypothesis beyond "regular sequence" to the precise Lean-ready form:**
> **k=1 (ord_I(F)=2):** let `Z` be the smooth codim-`c` center with ideal `I=(g_1,…,g_c)` (the
> residual Schur-block generators, regular sequence = transverse local parameters). The needed
> hypothesis is that **the degree-2 initial form of `F` along `I` is POSITIVE-DEFINITE on `I/I²`** —
> satisfied by `F = Σ_a g_a²` (or `gᵀA g + higher I-adic`, `A|_Z` pos-def). Then `ord_I(F)=2`, and on
> the blow-up chart `g_p=u, g_q=u·v_q`: `F∘π = u²·(positive nonvanishing) = u²·unit` ⟹ `k=1`.
> **⚠️ REAL/positive-definite is ESSENTIAL** (Codex flag): over ℂ, `Σz_a²` can vanish on exceptional
> directions ⟹ the unit-nonvanishing fails. We are over ℝ with `F=Σg²` ⟹ pos-def ⟹ safe. (This is
> the same real-vs-complex point as the `(x²+y²)²` codim-shortcut counterexample.)
> **h=c−1:** smooth codim-`c` blow-up ⟹ Jacobian `u^{c−1}`.
This is R1.2's geometric obligation; depends on R1.1 (the chart) + R1.3 (`codim = Mval`).

**Mval(t) is the CORE codim (Codex flag — verified):** `Mval(t) = codim S(t)` is in the REDUCED-width
core variables (`M⁽ˢ⁾ = H⁽ˢ⁾ − r`); it does NOT include the regular-block `n`. The `n/2` is added
SEPARATELY by Fubini (R1.4). So the assembly bound is `n/2 + B/2` (`B = min_t Mval`), NOT `B/2`. My
assembly below separates them correctly; do not double-count.

**Keep R1.2 BARE (Codex):** R1.2 is ONLY the divisor inequality `h+1 ≥ k·B`. Do NOT fold in
unit-absorption or Fubini — the assembly applies those separately (1. `rlct_unit_invariant`; 2.
`monomial_rlct`; 3. R1.2; 4. S1Fubini). This keeps R1.2 a clean exported API.

## R1.1 — the chart construction (the geometric mountain; design in thread-14 docs)

`ι` = pivot branches of the iterated L1 (Aoyagi affine atlas, NOT his exponent bookkeeping — value
from R1.3-codim, design-doc §0/§2). Each branch resolves a nested-rank stratum via iterated
block-elimination (REUSES `block_elimination`, trunk) exposing the residual Schur-block; one blow-up
of the residual-zero center (codim `Mval(t)`, regular sequence) gives the binding divisor. The charts:
the explicit polynomial substitutions (thread-14 r1-design.md §2, symbolically verified on
(1,1,1)/(2,1,2)/(2,2,2)). **This is the heavy piece — design it next with fm in parallel to the
R1.2-arithmetic formalisation.** Validate-small-first: (1,1,1) [no blow-up] → (2,1,2) → (2,2,2).

## Assembly (after R1.1–R1.7)

```
rlctAt(dlnLoss B) wstar
  = ⨅ charts (n/2 + rlctAt(core_chart))            [R1.5 min-over-cover + R1.4 Fubini-per-chart]
  = n/2 + ⨅ charts rlctAt(core_chart)              [n chart-independent — R1.5 factorises]
  = n/2 + ⨅ charts ⨅_j axisRatio(h,k)              [R1.7 S2, after R1.2 unit-absorption]
  = n/2 + ½·min_t Mval(t)                           [R1.2a upper (binding) + R1.2b lower (all divisors) + R1.6 cover]
  = aoyagiLambda H r                                [Lambda def: reg + lambdaCore]
```
The `∃ ι d k h` is discharged by the chart family R1.1 produces; the `= ⨅ monomialThreshold` is the
value-match above.

## NET — first concrete handoff + the plan

**Hand fm R1.2a (`axisRatio_regularSeq`) + R1.2b (`axisRatio_ge_of_mult`) NOW** — pure ℝ≥0∞ arithmetic,
no dependencies, the seed of R1.2's upper+lower. Then R1.1 (the chart mountain) + R1.3 (codim=Mval in
Lean) in parallel; R1.4/R1.5/R1.7 are trunk/closing; R1.6 (cover) is the residual real work. The two
use-site obligations (unit-absorption, hcore_top endpoint) fold into the assembly. Climb order:
R1.2-arith (now) → R1.3 codim → R1.1 charts (validate-small-first) → R1.6 cover → assembly.

---

## ★ ARCHITECTURE FINDING (escalated to controller) — resolution_charts is orphaned + mis-scoped ★

While designing R1.1 I found (and escalated) a statement-fidelity issue:
- **`resolution_charts` is consumed by NOTHING** (grepped): the headline goes
  `aoyagi_learning_coefficient → deepest_point_reduction → product_reduction (= aoyagiLambda directly)`;
  `product_reduction` does NOT call `resolution_charts`. Orphaned rung; product_reduction's R1 content
  is unplugged.
- **The statement can't hold for the full loss at r>0:** `rlctAt(dlnLoss B) wstar = ⨅ monomialThreshold`
  — but `monomialThreshold = ⨅ axisRatio` is a MIN, while the full-loss RLCT = `n/2 + ½·min Mval` is a
  SUM (the regular `n/2` is additive via Fubini, NOT a min-direction). FALSE for r>0 (n>0). Only holds
  at r=0 (n=0) — why the (1,1,1) validate case didn't catch it.

**FIX (recommended, pending controller approval): re-scope `resolution_charts` to the CORE** ‖∏C‖²:
`rlctAt(core) = ⨅ monomialThreshold = ½·min Mval = lambdaCore`, and `product_reduction` WIRES it:
`dlnLoss(deepest) →[L2 block-elim split]→ reg ⊞ core →[S1Fubini]→ n/2 + rlctAt(core)
→[resolution_charts(core)+S2+A1]→ n/2 + ½ min Mval = aoyagiLambda`. Clean separation (R1=core, L2=split+Fubini, A1=arithmetic).

**R1.1 CORE chart (d,k,h) — READY to hand fm post-re-scope** (verified thread-03/14, /tmp/r11_core_charts_ready.py):
- (1,1,1): ι=Unit, d=2, k=(1,1), h=(0,0) → ⨅ monomialThreshold = 1/2 = ½·min Mval ✓.
- (2,1,2): 4 charts, each d=2, k=(1,1), h=(1,1) → ⨅ = 1 = ½·min Mval ✓.
- (2,2,2): 24 charts, min chart dirs x:(k=1,h=3), s:(k=1,h=2) → monomialThreshold=3/2, ⨅=3/2=½·min Mval ✓.

R1.2a/b (handed to fm) are core-divisor arithmetic — correct under either reading. R1.1 design HELD
pending the controller's re-scope call.
