# genm-d1l2prod — the L=2 D1 ≥-leg reduction (first-peel wired, residual isolated)

The finite-atlas re-architecture of the D1 `≥`-leg at L=2, wired **as far as the banked producers
honestly reach**. This is a **scoped reduction, not a closure** of LEAF 2: the full
`∀ v, ∀ H` leaf is a re-architecture with a genuine analytic residual (the per-`v` residual-core
domination), triply-corroborated (blocker cert `genm-d1build/blocker-cert.md` + two decorrelated
Codex xhigh consults + synthesis UPDATE-607). What is delivered: the fully-banked FIRST selected-minor
IFT peel is wired in, and the remaining per-`v` debt is isolated to ONE precisely-named fact.

## Deliverable

Module `lean/DLNFibre/DLN/RLCT/Validate/D1L2ProducerReduction.lean` (@ `b37d7ef2`), two theorems.

---

> **Claim (reduction 1).** At a general optimal `v` at L=2 (`prod H v = B`, `rank B = r`), the D1
> per-point `≥`-leg `rlctAt deepest ≤ rlctAt v` reduces to the deepest-side value equality `hDeepest`
> plus the **residual-core domination** `hDom` — with the (sorry-free) FIRST selected-minor peel
> produced inside the proof.
>
> - **Lean:** `DLNFibre.DLN.RLCT.d1ge_L2_of_firstPeel_dominates`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1L2ProducerReduction.lean` @ `b37d7ef2`)
> - **Gloss.** For `H : Fin 3 → ℕ`, `deepest v : Params H`, `coreDeepest : ℝ≥0∞`, given
>   `hopt : prod H v = B`, `hB : B.rank = r`, `hDeepest : rlctAt (dlnLoss H B) deepest =
>   nRegL2 H r / 2 + coreDeepest`, and `hDom` — that for EVERY first-peel `C¹` residual `q` with the
>   chart transfer `rlctAt (dlnLoss H B) v = rlctAtOn (∑ p.1² + ∑ (q p)²) (0, t0)`, the slice residual
>   `R t = ∑ (q (0,t))²` is a.e.-nonzero near `t0` AND `coreDeepest ≤ rlctAtOn R t0` — then
>   `rlctAt (dlnLoss H B) deepest ≤ rlctAt (dlnLoss H B) v`.
> - **Proved.** The reduction, sorry-free. Internally: `exists_jacFlatL2_minor` (the coverage minor,
>   `nReg ≤ jacFlatL2.rank`, banked) → `dln_hchart_residual` (the selected-minor IFT chart, banked) →
>   `rlctAt_ge_nReg_add_slice_of_residual` (the quasi-split `hAtV` half, banked) →
>   `deepest_le_of_optimal_via_L2_ge` (the arithmetic close, banked). The FIRST peel is UNCONDITIONAL
>   over `v` and `H` — no rank-`r`-exactness, no deepest-gauge chart, no Morse-Bott lemma; it AVOIDS the
>   middle-stratum `hRform` obstruction of the old `GeneralVChartL2` route (which is FALSE at a
>   middle-stratum `v`).
> - **Assumed.** `hDeepest` (the deepest value; here a hypothesis so the reduction is `deepest`-agnostic)
>   and `hDom` (the residual-core domination — the genuine per-`v` content, see Deferred).
> - **Cited.** none (axioms `[propext, Classical.choice, Quot.sound]` — forced `#print`).
> - **Deferred.** `hDom` is NOT discharged: it is the SECOND selected-minor peel's value
>   (`rlctAtOn R = extra/2 + lambdaCore(M')` via `secondPeel_hchart_residual` + the degraded-core R1
>   value) + the rectangular value arithmetic + the second-peel Jacobian rank bound. The `∀`-over-residuals
>   shape is the established banked reduction idiom (cf. `hInterface` in `D1SecondPeelGlueL2`), NOT a
>   disguised chart-existence: `ContDiff`/`hchart` are the chart's OWN facts, produced inside; `hDom`
>   only supplies the value comparison + non-vanishing.
> - **Status.** sorry-free (forced `#print axioms` = clean-three).

---

> **Claim (reduction 2, LEAF-2 drop-in).** At the front-pivoted `B` (`htop`/`hcolfront` headline WLOG),
> for the constructed `deepestPoint`, the D1 per-point `≥`-leg reduces to the SAME `hDom` — the
> deepest-side value produced INSIDE from the banked #44-at-L2 fed the banked R1 value.
>
> - **Lean:** `DLNFibre.DLN.RLCT.d1ge_L2_deepestPoint_of_firstPeel_dominates`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1L2ProducerReduction.lean` @ `b37d7ef2`)
> - **Gloss.** Same as reduction 1 but at `deepest = deepestPoint H r B hB hr hL`, with `coreDeepest =
>   ofReal(lambdaCore (H − r))` produced internally via `deepest_regular_core_normal_form_L2_front`
>   (#44 at L=2, front-pivot) fed `r1_resolution_interface_L2_generic` (the banked R1 value at `M = H−r`).
>   Its conclusion `rlctAt (dlnLoss H B) (deepestPoint …) ≤ rlctAt (dlnLoss H B) v` is EXACTLY the
>   per-`v` shape of `HeadlineL2Assembly.lean`'s `hD1ge_L2` slot.
> - **Proved.** The reduction + the deepest-value production, sorry-free. This is the drop-in that closes
>   LEAF 2 once a `∀ v ∈ optimalSet, hDom v` producer lands: `fun v hv => …_deepestPoint_… v hv (hDom v)`.
> - **Assumed.** `htop`, `hcolfront` (headline column/row WLOG — supplied at the ⨅ by
>   `headline_frontRowColPivot_exists`), `hpos` (`∀ s, r < H s`), and `hDom` (as above).
> - **Cited.** `monomial_rlct` (the S2 normal-crossing→RLCT axiom) — via the banked R1 value
>   `r1_resolution_interface_L2_generic`. Forced `#print axioms` = `[propext, Classical.choice,
>   Quot.sound, monomial_rlct]` (clean-four). NO `sorryAx`, no new axiom.
> - **Deferred.** `hDom` (same residual content as reduction 1). `coreDeepest = ofReal(lambdaCore (H−r))`
>   is the general-`H` (NOT square) deepest core value — so the rectangular value arithmetic in the
>   eventual `hDom` producer must cover non-square `H − r` (the banked square-only
>   `coreDeepest_le_extra_half_add_lambdaCore_Mprime` does not).
> - **Status.** sorry-free (forced `#print axioms` = clean-four, `monomial_rlct` only).

---

## What remains for the FULL LEAF-2 close (the precise residual — NOT laundered)

`hDom` (the residual-core domination + slice non-vanishing) is the tracked analytic content. Its
honest discharge (the SECOND selected-minor peel + degraded-core R1, per `D1SecondPeel*` /
`D1ChartProducerL2Build`) needs, at general `H` and general `v`:

1. **The second-peel Jacobian rank bound** `extra ≤ (jacResid (q (0,·)) t0).rank` for the concrete
   bump-globalised first-peel residual `q` — the "chart-unwind through `Ψsymm` + split homeomorph +
   bump" (flagged open in `D1SecondPeelMinor.lean`'s docstring; Codex: bounded DLN linear algebra, NOT
   a Mathlib analytic wall).
2. **The rectangular value arithmetic** `lambdaCore(M) ≤ extra/2 + lambdaCore(M')` for non-square
   deepest widths `M = H − r` (the banked adjudication is square-only, `1 ≤ m ≤ 8`).
3. **`hDegraded`** — R1's resolution value at the rectangular degraded core `M'` (R1 at rectangular
   widths; the `R1ResolutionInterface` predicate exists, needs instantiation).
4. **The `(m,a,b)` middle-stratum extraction** at a general `v` (`a = rank(layer1)−r`, `b =
   rank(layer2)−r`), and `hRne` (slice non-vanishing) for both peels.
5. **The full `∀ v`**: the deepest-type `v` (extra = 0) degrades gracefully (empty second minor,
   `det = 1`), but the middle-stratum value input does not vanish there.

Per two decorrelated Codex xhigh consults + the blocker cert: **the full `∀ v, ∀ H` LEAF 2 is not
closable sorry-free by wiring the current bank** — the per-`v` middle-stratum residual value is the
genuine analytic residual on this route. This card delivers the honest reachable output: the first-peel
wiring + the precisely-isolated `hDom`, NOT a scoped closure.

## Structure & ideas observed (for the eventual `hDom` producer)

- The load-bearing coverage invariant `nReg ≤ jacFlatL2.rank` (banked `nReg_le_jacFlatL2_rank`) is what
  makes the FIRST peel unconditional — the selected-minor IFT atlas never stalls because SOME invertible
  `nReg`-minor always exists at any fibre point.
- The residual after the first peel is the vector of **unselected loss entries** (`‖q(0,·)‖²`), NOT the
  homogeneous reduced core `dlnLoss M 0`. So the clean d1reduce-cert reading "one peel → homogeneous
  core → Theorem 4" does NOT hold on this Lean route; a SECOND peel is genuinely needed. (Corrects the
  cert's speculation that the general-`v` residual is directly the homogeneous core at a basepoint.)
- The `hDom` `∀`-over-residuals idiom matches the banked `hInterface` shape in `D1SecondPeelGlueL2`; the
  eventual producer instantiates it at the concrete `dln_hchart_residual` output.
