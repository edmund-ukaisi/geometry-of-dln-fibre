# genm-l2scope — the #44 / deepest-point normal-form close at L = 2 (READ-ONLY map)

**Scout:** genm-l2scope. **Date:** 2026-06-30. **Discipline:** read-only (grep / Read /
`.ilean` / git inspection; no edits, no mutating build).

**Headline verdict:** the #44 L = 2 geometry is **already fully banked clean-three**
(`deepest_gauge_construction_L2`). The remaining work is **NOT geometry** — it is a small,
bounded **wiring** problem: (a) re-point the existing front-pivot chain off the sorryAx-tainted
general `deepest_gauge_construction` onto the clean `_L2`, and (b) connect that chain into the
Skeleton headline (or fill the standalone Skeleton sorry from it). **Charge it** as a bounded
wiring task — but be precise about the sorryAx-taint trap (below), and note the headline still has
**three other** open Skeleton rungs at L = 2 (#44 is one of four).

> **Major correction to the commissioning brief.** The brief's per-file sorry counts
> ("`DeepestGaugeConstruction.lean` (14)", "`DeepestL2Wiring.lean` (10)",
> "`DeepestNormalFormFrontPivot.lean` (5)", "`DeepestL2ConjSub4.lean` (4)",
> "`DeepestNormalFormWiring.lean` (3)", "`DeepestDiffeoBridgeL2.lean` (2)") count **occurrences of
> the word "sorry" in comments/docstrings**, not actual `sorry` tactics. The REAL sorry-tactic
> counts in canonical (`expedition/aoyagi-full`, HEAD `39930b35`) are:
>
> | file | real `sorry` tactics | where |
> |---|---|---|
> | `DeepestL2Wiring.lean` | **3** | lines 844, 847, 989 — **all in the L ≥ 3 arm** of `deepest_gauge_construction` (the #120 wall), explicitly tagged "SCOPED GAP (L ≥ 3 …), roadmapped #120" |
> | `DeepestGaugeChart.lean` | **1** | line 357 — `deepest_gauge_squeeze_exists` (general-`B` chart existence; **superseded at L = 2** by `deepest_gauge_chart_construct`) |
> | `DeepestGaugeConstruction.lean` | **0** | — |
> | `DeepestDiffeoBridgeL2.lean` | **0** | (3144 lines, fully assembled; `_impl` at 3058) |
> | `DeepestNormalFormFrontPivot.lean` | **0** | the front-pivot chain is sorry-free modulo named hyps |
> | `DeepestNormalFormWiring.lean` | **0** | conditional bridge, sorry-free |
> | `DeepestL2ConjSub4.lean` | **0** | `deepest_diffeo_bridge_L2_assembled` (Fin 3) lives here |
> | all other `Deepest*` | **0** | — |
>
> Net: the entire Deepest* cluster has **4** real sorries; **3 are the #120 L ≥ 3 wall**, and the
> 1 remaining (`deepest_gauge_squeeze_exists`) is bypassed at L = 2. **Zero L = 2-critical
> geometry sorries remain.**

---

## Q1 — The chain: clean-three `deepest_gauge_construction_L2` → `deepest_regular_core_normal_form` (L = 2)

There are **two parallel chains**; the live one does NOT touch the Skeleton bare sorry.

### The gauge-geometry producer (banked clean-three)
- `deepest_gauge_construction_L2` (`DeepestL2Wiring.lean:124–632`) — **standalone, clean-three**
  `[propext, Classical.choice, Quot.sound]` (AxCheck:120, brief-confirmed). Conclusion: the
  existential gauge bundle ending in
  `rlctAt H (dlnLoss H B) deepestPoint = rlctAtOn (Sreg_E + coreΦ) (paramsEquivFlat deepestPoint)`.
  Body builds the diffeo bridge via `deepest_diffeo_bridge_L2_assembled`
  (`DeepestL2ConjSub4.lean:644`, `H : Fin 3`) — sorry-free. Its `hTilde` (the π̃ local-diffeo) is
  discharged in-body via `deepestEFull_deriv` (no sorry).
- `deepest_gauge_construction` (`DeepestL2Wiring.lean:634–989`) — the **general-L wrapper**:
  `rcases Nat.lt_or_ge L 3` → L < 3 arm = `exact deepest_gauge_construction_L2 …` (clean); L ≥ 3 arm
  carries the 3 #120 sorries (844/847/989). **Same conclusion** as `_L2`; only extra hyp on `_L2` is
  `hLlt : L < 3`.

### The value chain (the Skeleton-facing route)
```
deepest_gauge_construction[_L2]   (gauge bundle, RLCT-equality)
   └─ deepest_gauge_chart_construct        (L2Wiring:996)  -- builds Nonempty (DeepestGaugeChart …)
        └─ deepest_gauge_squeeze_exists_frontPivot   (FrontPivot:46) = the above, with hJfront/htop
             └─ deepest_regular_core_reduces_frontPivot   (FrontPivot:62)
                  =  deepest_squeeze_transport  (projects loss_squeeze, GaugeChart:365, sorry-free)
                  ▸ deepest_regular_smooth_split (GaugeChart:434, sorry-free; consumes hGne)
                  ⟹ rlctAt deepest = nReg/2 + rlctAtOn(dlnLoss M 0) 0      [VALUE-FREE]
                       └─ deepest_normal_form_of_value_frontPivot (FrontPivot:91)
                            ▸ hRValue : rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)   [R1's value]
                            ⟹ rlctAt deepest = nReg/2 + ofReal(lambdaCore M)   [= #44's conclusion verbatim]
```
`nReg = r·(H⁰ + Hᴸ − r)`. The closed-form value is **exactly** the Skeleton
`deepest_regular_core_normal_form` RHS; the recombination to `aoyagiLambda` is
`reg_shift_add_core_eq_aoyagiLambda` (Skeleton:1089, proven).

**How the geometry discharges the value:** `deepest_squeeze_transport` projects the bundle's
`loss_squeeze` field (the RLCT-equality `_L2` produces); `deepest_regular_smooth_split` then peels
the `nReg/2` regular shift via `rlct_additive_smooth_block` + spectator-peel + the reduced-core
identification, landing the value-free `nReg/2 + rlctAtOn(dlnLoss M 0) 0`.

### The Skeleton bare sorry is NOT yet wired to this
`deepest_regular_core_normal_form` (`Skeleton.lean:1124`) is a **bare `sorry`**. The canonical
headline `aoyagi_learning_coefficient` (Skeleton:1725) routes
`deepest_point_reduction` (D1) ▸ `product_reduction` (Skeleton:1143) ▸ this bare sorry — it does
**not** call the front-pivot chain. The front-pivot chain
(`aoyagi_learning_coefficient_frontPivot`, FrontPivot:125) is a **parallel, sorry-free-modulo-hyps**
headline that the controller intends to wire in via the column/row-perm WLOG
(`headline_frontPivot_exists` / `HeadlineRowColPermWLOG.lean`) — that wiring is the open seam, not
the geometry.

---

## Q2 — Which sorries are L = 2-critical (vs #120 / unrelated)

**L = 2-critical geometry sorries: NONE.** The gauge geometry is banked clean.

The 4 real Deepest* sorries, classified:
- `DeepestL2Wiring.lean:844, 847` — `hinterface` interior `Qf s` / `Pf (s+1)`, **L ≥ 3 only**
  (`hspos`/`hint` arms vacuous at L = 2). **#120 wall.**
- `DeepestL2Wiring.lean:989` — `hstep2`, the grouped-`G0` recursive diffeo, **L ≥ 3 only**. **#120 wall.**
- `DeepestGaugeChart.lean:357` — `deepest_gauge_squeeze_exists` (general-`B`, all-`L` chart
  existence). **Bypassed at L = 2**: `deepest_regular_core_reduces` (GaugeChart:539) calls it, but
  the live route uses `deepest_regular_core_reduces_frontPivot` (FrontPivot:62), which instead calls
  `deepest_gauge_squeeze_exists_frontPivot` → `deepest_gauge_chart_construct` (no sorry of its own).
  Not on the front-pivot critical path.

The four open **Skeleton** rungs the headline still needs at L = 2 (separate obligations, named):
1. **#44** `deepest_regular_core_normal_form` (Skeleton:1131) — the L2 value-form (this scope).
2. **#107** `rlctAt_deepest_le_of_optimal` (Skeleton:1177) — the **D1 ≥-leg** (genm-d1asm / #247's
   thread; separate, do not conflate).
3. **R1** `resolution_charts` (Skeleton:1234) — supplies `hRValue`/`hcore`
   (`rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`); R1-LOWER/UPPER lanes in flight.
4. `aoyagiTheta_eq` (Skeleton:1707) — secondary θ deliverable, **off the λ headline path**.

So #44-at-L2 in isolation = "discharge the Skeleton sorry from the (clean-routed) front-pivot value
chain", with `hGne` and `hRValue` as the two inputs the chain still takes as hypotheses.

---

## Q3 — Near or tangled? (per-sorry bounded-vs-wall)

**Near, and bounded.** The geometry is done. What remains for #44-at-L2:

1. **sorryAx-taint re-point (the one real trap).** `deepest_gauge_chart_construct` (L2Wiring:1009)
   calls the **general** `deepest_gauge_construction`, whose L ≥ 3 arm contains `sorry`. Lean's
   `#print axioms` is transitive over the *full proof term* and does **not** prune the unexecuted
   `rcases` branch — so `deepest_gauge_chart_construct` and the entire front-pivot chain built on it
   **carry `sorryAx`**, even though only the clean `_L2` branch is reachable at L = 2. Corroboration:
   AxCheck pins `deepest_gauge_construction_L2` (clean) and `aoyagi_learning_coefficient` (sorryAx
   expected), but pins **none** of `deepest_gauge_chart_construct` / `*_frontPivot` — the harness
   does not yet claim them clean. **Fix = bounded:** specialise `deepest_gauge_chart_construct` (and
   the front-pivot lemmas) to `L = 2` (or thread `hLlt : L < 3`) and route to
   `deepest_gauge_construction_L2` directly. The conclusions are identical; only the `hLlt` arg is
   added. ~1 file, signature-local. **BOUNDED.**

2. **`hGne` (reduced-core germ-nonvanishing).** Input to `deepest_regular_smooth_split`. Holds when
   the reduced chain `M = H − r` is non-degenerate; the headline's `hpos : ∀ s, r < H s` gives
   `0 < M s` ∀s, so `prod M` is not identically zero and `{prod_M = 0}` is measure-zero. Producing
   the actual `∃ U ∈ 𝓝 0, ∀ᵐ z, dlnLoss M 0 (…z) ≠ 0` witness from `hpos` is a real (small) lemma —
   an a.e.-nonvanishing-of-a-nonzero-polynomial argument (the same shape already used in
   R1-LOWER's `frobSq(Sc·S) > 0 a.e.`, #134). **BOUNDED, not yet written as the L2 `hpos ⟹ hGne` glue.**

3. **`hRValue` (R1's core value).** = `resolution_charts` (#3 above) ▸ A1 `lambdaCore_eq_clean`
   (Skeleton:4246, built). This is **R1's lane**, not #44's — #44 takes it as a hypothesis. Out of
   scope for the #44 close; it is the shared dependency with R1.

4. **Skeleton wire-in.** Either fill `deepest_regular_core_normal_form` (Skeleton:1131) via
   `deepest_normal_form_of_value_frontPivot` + the WLOG transfer of `(hJfront, htop)`, or wire the
   parallel `aoyagi_learning_coefficient_frontPivot` into the headline via `headline_frontPivot_exists`.
   The `(hJfront, htop)` discharge is the column/row-perm ⨅-WLOG (KC1/KC2,
   `HeadlineRowColPermWLOG.lean`; #100/#101/#102/#117/#154 lineage). **BOUNDED but is the genuine
   remaining seam** — it's wiring, not geometry.

**No tangle across the 10/14-sorry files** — those counts were comment-word artefacts. The real
critical path touches: the re-point (1 file), the `hpos ⟹ hGne` glue (1 small lemma), and the WLOG
Skeleton wire-in (the FrontPivot/Headline seam). The 600–1500-line gauge-slice geometry the brief
worried about is **already banked** in the 3144-line `DeepestDiffeoBridgeL2.lean` + `_L2`.

---

## Q4 — What the stalled L2 lineage left (banked-but-unmerged?)

**Nothing unmerged closes anything canonical lacks.** Concretely (all vs canonical
`origin/expedition/aoyagi-full` @ `39930b35`):

| branch | commits ahead of canonical | content |
|---|---|---|
| `genm-l2fin` | **0** | fully merged; canonical is ~40 commits AHEAD of it |
| `genm-l2close`, `genm-l2tie`, `genm-l2cle`, `genm-l2cle-leaves`, `genm-l2conj`, `genm-l2psi`, `genm-l2subs`, `genm-l2thread`, `genm-l2-wt` | **0** | fully merged |
| `genm-l2wire2` | 5 | **docs only** (LINK2 route notes, π̃ soundness gate); +21/−13 in `DeepestL2Wiring.lean` is a STALE earlier-state edit, superseded |
| `genm-l2leaves` | 9 | +1333 lines in `DeepestDiffeoBridgeL2.lean` — but that branch's file is **2252 lines with 1 sorry (line 2172)**, whereas **canonical's is 3144 lines, sorry-free**. genm-l2leaves is the STALE earlier S2/S4-leaf route; canonical superseded it with the full `_impl` assembly. |

The brief's premise (last push 24h+ ago, stood down) is right that the lineage is stale — but the
reason is that **its output already landed in canonical and was then surpassed**, not that it holds
unmerged value. No merge needed; nothing to salvage.

---

## Q5 — Recommendation: CHARGE IT (bounded wiring), with a crisp sorry-list

**Commission #44-at-L2 NOW as a bounded build.** It is not "open-but-near design"; it is "geometry
done, wiring to finish." The crisp work-list, in order:

1. **Re-point to clean-three** (kills the sorryAx taint): make `deepest_gauge_chart_construct` route
   to `deepest_gauge_construction_L2` (thread `hLlt`/`L = 2`), so the front-pivot chain becomes
   clean. Add AxCheck pins for `deepest_gauge_chart_construct` / `deepest_gauge_squeeze_exists_frontPivot`
   to lock it. ~1 file. **(The de-risking step — do first; cheap `#print axioms` probe confirms.)**
2. **`hpos ⟹ hGne` glue**: a small a.e.-nonvanishing lemma (template: #134). ~1 lemma.
3. **Skeleton wire-in**: fill `deepest_regular_core_normal_form` (or wire
   `aoyagi_learning_coefficient_frontPivot`) via `deepest_normal_form_of_value_frontPivot`, with
   `(hJfront, htop)` discharged by the KC1/KC2 column/row-perm WLOG. **This is the genuine seam** —
   confirm the WLOG lemmas (`headline_frontPivot_exists`, `HeadlineRowColPermWLOG`) actually land
   `(hJfront, htop)` at the deepest point before committing; if the WLOG is itself open, #44-at-L2's
   *headline* close inherits that, though the *normal-form value* (modulo `hGne`+`hRValue`) is
   reachable independently.

**Out of scope (do NOT bundle into the #44-at-L2 charge):** the D1 ≥-leg #107 (separate thread,
genm-d1asm/#247), R1's `resolution_charts`/`hRValue` (R1 lane), the #120 L ≥ 3 wall, and θ.

**Kill-condition for "bounded" (stated before confirming):** if the WLOG transfer of
`(hJfront, htop)` to the constructed `deepestPoint` is itself an open research gap (not just an
unwired-but-proven lemma), then the #44-at-L2 *headline* is NOT bounded — only the conditional
value-form is. I verified the chain lemmas exist and are sorry-free; I did **not** trace the WLOG
lemmas' own sorry-status to ground (`HeadlineRowColPermWLOG.lean` + `headline_frontPivot_exists`),
so the commissioned build should verify that as gate step 0.

---

## Evidence anchors (canonical, `expedition/aoyagi-full` @ `39930b35`)
- `lean/DLNFibre/DLN/RLCT/Skeleton.lean`: `deepest_regular_core_normal_form` (1124, bare sorry @1131),
  `product_reduction` (1143), `deepest_point_reduction` (1187), `rlctAt_deepest_le_of_optimal`
  (sorry @1177), `resolution_charts` (sorry @1234), `aoyagi_learning_coefficient` (1725),
  `reg_shift_add_core_eq_aoyagiLambda` (1089), `lambdaCore_eq_clean` (4246).
- `…/Validate/DeepestL2Wiring.lean`: `deepest_gauge_construction_L2` (124), `deepest_gauge_construction`
  (634, L-split @693–696, #120 sorries @844/847/989), `deepest_gauge_chart_construct` (996).
- `…/Validate/DeepestGaugeChart.lean`: `deepest_gauge_squeeze_exists` (sorry @357),
  `deepest_squeeze_transport` (365), `deepest_regular_smooth_split` (434),
  `deepest_regular_core_reduces` (524).
- `…/Validate/DeepestNormalFormFrontPivot.lean`: the sorry-free front-pivot chain (46/62/91/125).
- `…/Validate/DeepestNormalFormWiring.lean`: `deepest_normal_form_of_value` (48, conditional bridge).
- `…/Validate/DeepestL2ConjSub4.lean`: `deepest_diffeo_bridge_L2_assembled` (644, `Fin 3`).
- `…/Validate/DeepestDiffeoBridgeL2.lean`: `deepest_diffeo_bridge_L2_impl` (3058), 3144 lines, 0 sorry.
- `…/RLCT/AxCheck.lean`: pins `deepest_gauge_construction_L2` (120, clean-three),
  `deepest_gauge_construction` (125, sorryAx expected), `aoyagi_learning_coefficient` (251, sorryAx
  expected); does NOT pin the front-pivot/chart-construct lemmas.
