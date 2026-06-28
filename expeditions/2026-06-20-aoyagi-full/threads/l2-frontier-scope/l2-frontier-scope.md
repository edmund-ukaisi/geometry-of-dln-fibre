# L2 general-`L` frontier-scope — map + build-ready cert (scout, read-only, 2026-06-28)

**Mission (A):** make the L2 general-`L` interior leg of `aoyagi_learning_coefficient` build-ready
for a clean formaliser commission. Output: a frontier-map of the 6 named sorries + a traced
sorryAx-dependency + a build-ready cert for the highest-VOI next piece.

**Method:** SOURCE-LEVEL trace (the worktree has no DLNFibre oleans built; a full Skeleton
import-closure build is the formaliser's job, not a scout's). Every claim below is grounded in the
actual Lean text at the cited line; decorrelated Codex (`codex/voi-{prompt,answer}.md`, xhigh)
corroborated the central finding + sharpened the VOI read.

---

## TL;DR — the brief's premise is PARTLY INVERTED (key finding)

The brief framed 2915/3099/3104/3118/3123/3289 as the "general-`L` frontier the headline genuinely
needs closed." **That is not the current wiring.** The actual situation:

1. **The headline's L2 gap is a DIFFERENT, single bare sorry**:
   `deepest_regular_core_normal_form` (`Skeleton.lean:1131`). `aoyagi_learning_coefficient` →
   `product_reduction` → this. The whole `DeepestGauge*` apparatus is the INTENDED producer for it
   but is **not yet wired in**.

2. **`DeepestGaugeConstruction` carries 4 active sorries, not ~20.** Bare-`sorry` lines: **2915,
   3118, 3123, 3289**. (3099/3104 in the brief are not `sorry` lines — they are the docstring +
   `have hcorner'`/`have hinterface` headers at those line numbers; the actual interior sorries are
   3118/3123. The "~20 sorries" count in the synthesis/comment is stale — the rest are docstring
   text containing the word "sorry".) Confirmed: `grep -c '^\s*sorry'
   DeepestGaugeConstruction.lean = 4`.

3. **None of the 4 flow into the headline's `sorryAx` today.** Two independent reasons:
   - `deepest_regular_core_reduces` (`DeepestGaugeChart.lean:570`, the value-free reduction the
     intended bridge `deepest_normal_form_of_value` calls) bottoms out at
     **`deepest_gauge_squeeze_exists` (`DeepestGaugeChart.lean:403`) — itself a BARE `sorry`**, NOT
     `:= deepest_gauge_chart_construct …`. So the producer (where the 4 live) is disconnected from
     the chart-existence consumer.
   - `DLNFibre.lean` (the aggregator) imports `DeepestBaseL1` but **does NOT import**
     `DeepestGaugeConstruction`, `DeepestGaugeChart`, or `DeepestNormalFormWiring`. And
     `DeepestGaugeChart` does not import `DeepestGaugeConstruction`. So the 4 sorries are not even in
     the headline build's term — `#print axioms aoyagi_learning_coefficient` cannot see them.

   Net: **closing 2915/3118/3123/3289 reduces the headline's gap by ZERO** until the wiring + the
   `deepest_gauge_squeeze_exists` close land. (Codex Q1 AGREE; Q2 PARTIAL — "wiring converts hidden
   producer debt into visible headline debt"; it does not by itself reduce `sorryAx` if the producer
   still carries sorries after wiring.)

**Consequence for the commission:** the highest-VOI L2 work is NOT "close a frontier sorry." It is
the two-step **(I) close `deepest_gauge_squeeze_exists` for the path the headline actually takes,
then (II) wire it + the L=1 base + the WLOG seam into the headline.** And the cleanest probe is an
**L=2-only `deepest_gauge_squeeze_exists`** that bypasses 3118/3123/3289 entirely (Codex Q4 AGREE).
See the cert in §3.

---

## 1. The exact headline → L2 dependency chain (traced at the source)

```
aoyagi_learning_coefficient            Skeleton.lean:1725   (general L)
  └ rw deepest_point_reduction         Skeleton.lean:1187
  │    └ ≥ leg: rlctAt_deepest_le_of_optimal   Skeleton.lean:1177   ← BARE SORRY (D1, off-mission)
  └ exact product_reduction            Skeleton.lean:1142
       └ rw deepest_regular_core_normal_form    Skeleton.lean:1124  ← BARE SORRY at :1131  (THE L2 GAP)
       └ rw reg_shift_add_core_eq_aoyagiLambda  (proven)

INTENDED close of Skeleton:1131 (not yet wired):
  deepest_normal_form_of_value         DeepestNormalFormWiring.lean:48   (conditional, body sorry-free)
    takes (hGne, hRValue) as hyps; rw [deepest_regular_core_reduces, hRValue]
       └ deepest_regular_core_reduces  DeepestGaugeChart.lean:570
            └ obtain ⟨Γ⟩ := deepest_gauge_squeeze_exists  DeepestGaugeChart.lean:403  ← BARE SORRY
            └ deepest_squeeze_transport (proven, = Γ.loss_squeeze)
            └ deepest_regular_smooth_split (proven, consumes hGne)

INTENDED producer of deepest_gauge_squeeze_exists (DISCONNECTED — no `:=` exists):
  deepest_gauge_chart_construct        DeepestGaugeConstruction.lean:3296   (Nonempty, 2 ≤ L)
    └ deepest_gauge_construction       DeepestGaugeConstruction.lean:2925
         carries sorries 2915, 3118, 3123, 3289
```

The two off-the-headline bare sorries that ARE on the headline path: `rlctAt_deepest_le_of_optimal`
(D1 ≥-leg, Skeleton:1177 — not this mission) and `deepest_regular_core_normal_form` (Skeleton:1131
— the L2 value-form). The headline carries `sorryAx` from BOTH today. The 6 frontier sorries are NOT
among them.

---

## 2. Frontier-map — the 4 active sorries in `DeepestGaugeConstruction`

For each: WHAT it is, WHAT it needs, banked pieces, risk, headline-relevance.

### 2915 — the L=2 diffeo (`deepest_diffeo_bridge_L2`)
- **WHAT.** `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar` for the joint `(T1,Y1)` Ψ at L=2 — the
  `hstep2` L=2 branch (`deepest_gauge_construction` calls it at :3282). The collapsed two-grouping;
  feed the joint Ψ to the banked `rlctAtOn_diffeo_bridge_of` (`DeepestDiffeoBridge.lean:39`).
- **WHAT IT NEEDS.** The composition identity = E1 (core half, `frobSq_prod_absorbed_eq_rcore`,
  `DeepestCompositionE1.lean:53`, banked) **+ E2** (reg-preservation `deepestEFull ∘ Ψ =
  deepestEFull`). E2 is the gap. It is sound ONLY at block-triangular endpoint frames
  (block-LOWER `endpointP0`, block-UPPER `endpointQL`) — verified exact-rational
  (`31-pin2-comparability/e2-verify/e2_mw2.py`: "Mw GENERAL" fails 8/8, "Mw P0-lower QL-upper"
  passes 0 bad). The triangular normalizers are banked sorry-free
  (`Core.Matrix.RankNormalFormTriangular.{blockLower_left_normalizer, blockUpper_right_normalizer}`),
  BUT they carry `[Invertible A11]` (the boundary corner's leading `r×r` block). The producer's
  `deepestPoint` does NOT supply that: `IsDeepLayers` (Skeleton:513) pins only **tail-columns/rows
  zero** for the boundary corners (clauses 4,5), and `deepestPoint_exists` builds `layer0 = U·projM`
  whose top `r×r` block CAN be singular (`r=1, U=[[0],[1]]`: rank 1, top block 0 — `a11_check.py`).
- **THE UNBLOCKER ("(1a)").** Strengthen `IsDeepLayers` + `deepestPoint_exists` so the boundary
  corner's leading `r×r` block is invertible (`U` rank-`r` ⟹ permute `r` independent rows to the top
  — always achievable), and emit block-triangular frames from the frame bundle. Then E2 holds via the
  banked normalizers + the `(T1,Y1)` Ψ.
- **TYPE.** Design (bundle-wide `IsDeepLayers` def change) + Lean-plumbing (re-thread the existence
  proof + every consumer of `IsDeepLayers`/`deepestPoint_exists` + the frame bundle). The math is
  settled (the triangular-frame E2 fact is exact-verified; the invertible-leading-block fact is
  elementary). **Bounded but invasive** (Codex Q3: "engineering-heavy but conceptually localized").
- **RISK.** The strengthening touches `deepestPoint_exists` (a `Classical.choice` existence whose
  witness `wLayers` is in `Skeleton.lean:789`) and every downstream `IsDeepLayers` consumer. Medium
  blast radius; no research wall. The math caveat is closed (it is NOT free from front-pivot — that
  was a refuted steer, synthesis UPDATE-96 `a11_check.py`).
- **HEADLINE-RELEVANCE.** Off the path today (see §0/§1). On the path only AFTER the wiring +
  `deepest_gauge_squeeze_exists` close.

### 3118 / 3123 — the L≥3 interior `hinterface` (Item 19)
- **WHAT.** Inside `deepest_gauge_construction`, the `hinterface` proof needs, for every interior
  layer (`1 ≤ s.val ∧ s.val+1 < L`), `Qf s = 1` (3118) and `Pf (s+1) = 1` (3123) — the
  interior-frame triviality `endpoint_telescoping` (`DeepestTelescoping.lean:174`) consumes.
- **WHAT IT NEEDS.** A BUNDLE-CHOICE fix, **NOT new math.** The interior deepest layer IS the corner
  already (`deepestPoint_interior_eq_corM`, `DeepestFrame.lean:93`, proven), and the trivial frame
  `P=Q=1` carries it to corM (`deepestPoint_interior_frame_id`, `DeepestFrame.lean:108`, proven). The
  gap: the frame BUNDLE `deepestPoint_frame_pivot_exists` (`DeepestPivotFrame.lean:272`) picks
  interior frames via `deepestPoint_frame` (`= Classical.choose` of `deepestPoint_frame_exists`),
  which is a GENERIC rank-normal-form, NOT committed to the identity. Fix: have the bundle emit
  IDENTITY interior frames (a `DeepestPivotFrame` re-thread using `deepestPoint_interior_frame_id`).
- **TYPE.** Lean-plumbing (re-architect the frame bundle's interior arm). Vacuous at L=2 (`1 ≤ s.val
  ∧ s.val+1 < 2` is empty), so OFF the L=2 path entirely.
- **RISK.** Low (the identity frames are admissible — both supporting lemmas are proven). Codex Q3:
  "bounded if identity frames are mathematically admissible throughout the bundle API" — they are.
- **HEADLINE-RELEVANCE.** Off the L=2 path (vacuous). Needed only for a clean GENERAL-L headline.

### 3289 — the L≥3 `hstep2` grouped-G0 diffeo (Item 24)
- **WHAT.** The `hstep2` L≥3 branch: the diffeo bridge `rlctAtOn Φscore = rlctAtOn Φcore` for L≥3,
  via the two-grouping `G0 = prodAux (L−1)` (first `L−1` layers), `G1 = last layer`, with `W := I +
  Z1·A1⁻¹·A0⁻¹·Y0` on grouped blocks + the grouped pivot `A0⁻¹`.
- **WHAT IT NEEDS.** The recursive multi-factor reparametrization — the general-`L` grouped-block
  diffeo. The cert's `(T1,Y1)` Ψ generalizes to the grouped product, but the proof is the recursive
  multi-factor version. **This is the one genuine research-risk item** (Codex Q3: "failures there can
  expose missing compatibility lemmas or even a wrong parametrization").
- **TYPE.** Math (new) + Lean. Multi-tide. Vacuous at L=2.
- **RISK.** HIGH relative to the others. The "no research wall" premise is least secure here.
- **HEADLINE-RELEVANCE.** Off the L=2 path. The single biggest general-L unknown.

### (off-mission, on-path) Skeleton:1131 + Skeleton:1177
- `deepest_regular_core_normal_form` (Skeleton:1131) — THE L2 value-form gap the headline actually
  carries; closed by `deepest_normal_form_of_value` once the chart wiring lands.
- `rlctAt_deepest_le_of_optimal` (Skeleton:1177) — the D1 ≥-leg (Aoyagi Thm 2 fibre monotonicity).
  On the headline path, but a separate (D1) leg, not L2.

---

## 3. BUILD-READY CERT — close `deepest_gauge_squeeze_exists` for L=2, then wire the headline

**This is the highest-VOI L2 piece.** It is the ONLY piece that, when closed, reduces the headline's
actual `sorryAx` on the L2 leg — and it bypasses the two riskiest frontier sorries (3289, and the
3118/3123 bundle re-thread) entirely.

### Statement (the target the formaliser builds)

Two coupled deliverables, in order:

**(I) `deepest_gauge_squeeze_exists` close (L=2 path + L=1 base).** Replace the bare sorry at
`DeepestGaugeChart.lean:403` with a real proof:
```
theorem deepest_gauge_squeeze_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B …) (hB : B.rank = r) (hr : ∀ s, r ≤ H s) (hL : 1 ≤ L) :
    Nonempty (DeepestGaugeChart H r B hB hr hL)
```
by case-split on `L`:
  - **L = 1:** the smooth base case — already banked sorry-free as
    `deepest_regular_core_normal_form_L1` (`DeepestBaseL1.lean:244`). Build the `DeepestGaugeChart`
    inhabitant for L=1 directly (the chart is the trivial split — `prod H A = A 0`, no product), OR
    route the L=1 normal-form value through a separate L=1 chart constructor. (If a full L=1
    `DeepestGaugeChart` is awkward, the cleaner target is to have `deepest_regular_core_reduces`
    case-split on L and use the L=1 normal-form lemma directly, never constructing a chart at L=1.)
  - **2 ≤ L:** `deepest_gauge_chart_construct H r B hB hr hL (by omega) hJfront`
    (`DeepestGaugeConstruction.lean:3296`), discharging the front-pivot `hJfront` via the WLOG seam
    (next bullet). THIS is the wiring that does not exist today.

**(II) Wire it into the headline.** Replace the bare sorry at `Skeleton.lean:1131`
(`deepest_regular_core_normal_form`) with
`exact deepest_normal_form_of_value H r B hB hr hL hGne hRValue`
(`DeepestNormalFormWiring.lean:48`), discharging `hGne` (reduced-core germ-nonvanishing — banked as
crux2 #65 `dlnLoss_deepest_core_ae_ne_zero` for non-degenerate `M`, here `hpos` ⟹ no interior
`M_s = 0`) and `hRValue` (R1's value — IN FLIGHT on the other fronts; take as hypothesis / gate on
R1). Add `DeepestGaugeConstruction`, `DeepestGaugeChart`, `DeepestNormalFormWiring` to `DLNFibre.lean`.

### The front-pivot WLOG seam (banked sorry-free — the missing glue)
`deepest_gauge_chart_construct` requires `hJfront` (the `B`-pivots-are-the-first-`r` hypothesis). The
seam to discharge it is banked: `FrontPivotWLOG.lean` (sorry-free) — `rlct_infimum_colPerm_eq:313`
(the `⨅`-over-`optimalSet` RLCT is invariant under a column-permutation of `B`) + lemmas 1–4
(`paramColPermLast` MP homeomorph, `dlnLoss_colPerm_eq`); `FrontPivotProducer.lean` (sorry-free) —
`frontEmbed` + `pivot*_frontEmbed`. The chart is run at `B·Π` (Π brings `B`'s pivots to the front),
and the headline's `⨅ optimalSet` is invariant. **NOTE:** `deepest_gauge_squeeze_exists` is stated
for a GENERAL `B`, but `deepest_gauge_chart_construct` is stated for FRONT-pivot `B`. The seam lives
at the `⨅`-level (`rlct_infimum_colPerm_eq`), NOT at the `Nonempty (DeepestGaugeChart …)`-level — so
the cleanest wiring may push the WLOG up to `deepest_point_reduction`/the headline `⨅`, and have
`deepest_gauge_squeeze_exists`/`deepest_regular_core_reduces` carry a front-pivot hypothesis. **The
formaliser must resolve WHERE the WLOG seam sits** — this is the one genuine design decision in (I).

### Approach (citing banked pieces)
- E1 banked: `frobSq_prod_absorbed_eq_rcore` (`DeepestCompositionE1.lean:53`).
- The abstract diffeo bridge banked: `rlctAtOn_diffeo_bridge_of` (`DeepestDiffeoBridge.lean:39`).
- The triangular normalizers banked sorry-free: `Core.Matrix.{blockLower_left_normalizer,
  blockUpper_right_normalizer}` (`RankNormalFormTriangular.lean:36,62`).
- PIN0 (`deepest_coreAbsorb_exists`), PIN1 (`deepest_regAbsorb_exists`), PIN2-matrix-core
  (`deepest_loss_squeeze`, axiom-clean), the split MP reindex (`deepestSplit_mp_basepoint`), the
  `(T1,Y1)` Ψ, `endpoint_telescoping`, the L=1 base (`DeepestBaseL1`), the WLOG seam
  (`FrontPivotWLOG`/`FrontPivotProducer`) — ALL banked sorry-free.
- The L=2 `hstep2` branch closes via `deepest_diffeo_bridge_L2` (sorry 2915) — see below.
- thread-14 cards: `g125-L2-deepest-split-certificate.md` (the unit-pivot witness),
  `pin0-coreabsorb`/`pin1-regabsorb`/`pin2-loss-squeeze` statement cards, `sub34-gate-status.md`.

### What the L=2 path STILL needs closed inside the construction: 2915 only
At L=2, `deepest_gauge_construction`'s `hinterface` (3118/3123) and `hstep2` L≥3 (3289) are
**vacuous** (the interior/`L≥3` guards are empty). The ONLY active sorry on the L=2 path through
`deepest_gauge_construction` is **2915** (`deepest_diffeo_bridge_L2`). So the L=2 commission is:
**close 2915 (the (1a) `IsDeepLayers` strengthening) + the wiring (I)+(II).** That is a clean,
bounded L=2 headline — no L≥3 interior, no grouped recursion.

### Scope estimate
- (II) wiring + aggregator + `hGne` discharge + the L=1 inhabitant: **1 tide** (mostly `exact` +
  imports + the documented `hGne` lemma), MODULO the WLOG-seam-placement design decision.
- (I) the L=2 `deepest_gauge_squeeze_exists` + 2915: **2–3 tides** (the (1a) `IsDeepLayers`
  strengthening is the bulk — bundle-wide def change + re-thread `deepestPoint_exists` + consumers +
  emit triangular frames; then 2915 closes via the banked normalizers).
- 3118/3123 (interior bundle-choice): **1 tide** — needed only for general-L, can follow.
- 3289 (grouped recursion): **multi-tide, research-risk** — the last piece; do NOT front-load it.

### Kill-conditions (state before building)
1. **The (1a) strengthening breaks an existing consumer of `IsDeepLayers`/`deepestPoint_exists`** in
   a way that re-opens a banked-clean result (e.g. `deepestPoint_isDeep`, `product_reduction`'s
   wiring). If touching `IsDeepLayers` forces a non-trivial re-proof of a CITED/banked result, STOP
   and report — the strengthening is more invasive than scoped. (Mitigation: the synthesis flags "a
   hard soundness gate — no IsDeepLayers change without re-verifying the headline," synthesis:337.)
2. **`hGne` does NOT hold under `hpos` at L=2.** If the reduced-core germ-nonvanishing fails for some
   `hpos`-satisfying `H` (an interior `M_s = H_s − r = 0` slipping through), the wiring (II) is
   unsound. (Mitigation: `hpos : ∀ s, r < H s` ⟹ `M_s = H_s − r ≥ 1 > 0` everywhere — so `hGne`
   should hold; VERIFY the banked `dlnLoss_deepest_core_ae_ne_zero` actually consumes `hpos`/`M_s>0`.)
3. **The WLOG seam cannot be placed cleanly** — if `deepest_gauge_squeeze_exists` genuinely needs a
   front-pivot `B` (so a general-`B` `Nonempty (DeepestGaugeChart …)` is FALSE without the column
   perm baked into the chart), and the `⨅`-level seam doesn't transfer, the whole route needs
   `deepest_regular_core_reduces` restated with a front-pivot hypothesis. STOP and report the
   restatement before grinding.
4. **The banked producer is not semantically strong enough** (Codex's "BIGGEST RISK"): wiring (I)
   reveals `deepest_gauge_chart_construct`'s output does not match the `DeepestGaugeChart` fields the
   consumer needs without unplanned interface lemmas. (Mitigation: the fields ARE matched at
   `deepest_gauge_chart_construct:3307` — it constructs the full structure — so this risk is low, but
   the formaliser should green-gate the structure-field match FIRST, before touching 2915.)

### Recommended commission ORDER (de-risked)
1. **FIRST, cheap probe (½–1 tide):** wire (II) + add imports, taking BOTH `hGne` and the
   L=2-chart-existence as `sorry`/hypotheses, and run `#print axioms
   aoyagi_learning_coefficient` (L:=2). This makes the producer debt VISIBLE on the headline and
   confirms the chain compiles end-to-end. (Codex Q2: this is "honest dependency accounting" — it
   converts hidden debt to visible debt and validates the trace.)
2. **THEN (1a)+2915 (2–3 tides):** the L=2 `deepest_gauge_squeeze_exists`. This is the real
   mathematical work and the true bottleneck for a clean L=2 headline.
3. **THEN 3118/3123 (1 tide) + 3289 (multi-tide):** general-L interior, only after L=2 is clean.

---

## 4. Verdict on the (A) premise ("L2 bounded, no research wall")

**PARTLY TRUE, with one genuine research-risk item.**
- The L=2 leg (the headline's actual near-term target) is **bounded**: the only active sorry on it is
  2915, whose math is settled (triangular-frame E2 exact-verified; invertible-leading-block
  elementary) — the work is the invasive-but-localized (1a) `IsDeepLayers` strengthening + the
  wiring. No research wall on L=2.
- 3118/3123 (general-L interior) are **bounded** (bundle-choice, both supporting lemmas proven).
- **3289 (the L≥3 grouped-G0 recursive diffeo) is the genuine research-risk** — "bounded" is the
  least secure claim there. It should be the LAST L2 piece, scoped on its own, not front-loaded.

The mission's framing of "make the L2 frontier build-ready" is best served by **NOT** commissioning a
frontier sorry directly, but by commissioning the **wiring + L=2 `deepest_gauge_squeeze_exists`
(2915)** — the piece that actually moves the headline and de-risks the rest.

---

## STEP_BACK reflection
- **Most likely to advance the expedition:** the cheap probe (commission step 1 — wire (II) + run
  `#print axioms`). It is ½–1 tide, validates this entire source-trace against the build, and
  converts invisible producer debt into a visible, actionable headline gap. Highest VOI per tide.
- **Most likely to break:** the (1a) `IsDeepLayers` strengthening (kill-condition 1) — touching a
  bundle-wide def with a "hard soundness gate" attached. If it re-opens a banked result, the L=2
  cost balloons.
- **Next computation that would clarify:** a forced-recompile `#print axioms
  aoyagi_learning_coefficient` at L:=2 AFTER the cheap-probe wiring — it would settle, against the
  kernel rather than a grep, exactly which sorries the L=2 headline carries (my trace predicts:
  Skeleton:1177 D1-leg + `deepest_gauge_squeeze_exists` + 2915, and NOTHING from 3118/3123/3289).
  That is the formaliser's first green-gate, and it is the definitive test of this whole map.
