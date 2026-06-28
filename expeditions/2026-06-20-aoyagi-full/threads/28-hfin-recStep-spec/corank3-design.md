# corank-3 design — the recursion's first real firing, with the threshold trap caught (2026-06-28)

**Context.** O1/O2 cleared by the controller's decorrelation (`n4-o2-adjudicate`: O2 HOLDS via pure
translation Jac≡1; O1 a build cost). The corank-2 weld (`core_schur2_lt_top`) is the validated base case.
Charge: the corank-3 instance — the recursion's FIRST real firing (Sc becomes 2×2, NOT a scalar).

## THE THRESHOLD (the load-bearing knowing-decision — Codex hit the undershoot trap)

Codex (xhigh) answered "corank-3 inner threshold c' < 2, reuse `schurInner_S_le` verbatim." **WRONG —
the undershoot trap.** Codex reused my r=2-HARDCODED lemmas (`schurInner_S_le`/`schurSplitD_lintegral_lt_top`
are Fin-4-Morse, threshold 2) for the corank-3 leaf. The cert is ground truth:
**λ_{3,4} = 4** (not 2) — the (3,3,4) cell is `‖T‖²(rlct 2) ⊕ ‖Δ·S‖²(λ_{2,4}=2)` = 4 = ½·minAdm(3,3,4).
The corank-3 target threshold is **c' < 4**, via the SHIFTED-EXPONENT Morse peel (NOT the threshold-2
verbatim reuse).

## THE corank-3 MECHANISM (c' < 4, matches "keep both blocks")

Target: `∫_{R∈matBox 3 3 T} ∫_{S∈matBox 3 4 T} ‖R·S‖_F^{−2c'} < ⊤` for `0 < c' < 4 = λ_{3,4}`.
1. **Radial blow-up**: cover R by the 9 entry-charts (`recStep`/`argmaxCellOn` on `Fin 9`), radial
   `Δ = a·R`, Jac `|a|⁸` (`pivotBlowupOnDeriv_det`, card 9 → 8); a-axis threshold `r²/2 = 9/2`.
2. **N2b j=1 split** (general-r, PROVED): `‖R·S‖² ≳ ‖(R·S)_row0‖²(Morse, p entries) + ‖Sc·S_bot‖²`, Sc
   now **2×2** (corank-2 — the recursion's first non-scalar residual), S_bot = rows 1,2 of S (a 2×p block).
3. **Shifted-exponent Morse peel** (the existing `radial_morse_residual_power_le`/`core_T_peel_le`,
   `RadialResidualPower`): peel the top block `‖(R·S)_row0‖²` (Morse, threshold (jp)/2 = ... the spectator
   T block, threshold 2 for (3,3,4)), leaving the corank-2 residual at the SHIFTED exponent `c' − 2`.
4. **Close the residual** `∫_Δ ∫_{S_bot} frobSq(Δ·S_bot)^{−(c'−2)}` by `core_schur2_lt_top` (my closed
   corank-2 lemma, needs `c'−2 < 2`) ⟹ **c' < 4**. The translation-domination (`M22 ↦ Sc`, Jac≡1, via
   `lintegral_translate_le_local` + `rowShear_entry_le_one`) confines Sc to the fixed box first.

So corank-3 BOTTOMS OUT in `core_schur2_lt_top` (no fresh general-r induction yet) — but the leaf is
`core_schur2_lt_top` AT THE SHIFTED EXPONENT `c'−2`, NOT `schurInner_S_le` at threshold 2.

## CORRECTION (Codex-confirmed) — the inner is R-INTEGRATED, NOT fixed-R

A second design check (Codex xhigh) caught a subtlety I nearly built wrong: the corank-3 inner per-chart
object must keep angular `R` **INTEGRATED** (`∫_{R-ang}∫_S`), NOT a fixed-`R` lemma like corank-2's
`schurInner_S_le`. At FIXED `R`, the residual `‖Sc·S_bot‖²` (Sc 2×2) contributes its full threshold only
when Sc is full-rank; the `{Sc rank-drop}` locus has POSITIVE measure in the fixed-`R` slice, forcing the
exponent back to 2 (undershoot). Integrating the angular coords lets the corank-2 estimate absorb that
locus. corank-2 worked fixed-`R` only because its residual was a SCALAR Sc (always a Morse block in S
regardless of Sc's value). **So corank-3 does NOT factor through a fixed-R inner lemma** — no
`schurInner3_S_le` analog; the headline mirrors `core_schur2_lt_top` one `r` up, R-integrated throughout.
The Morse peel (row-0 vs S-row0) removes ALL row-0 terms — the residual depends only on M21,M22,S_bot, no
row-0 coupling. M22 lives in free box-coords (ratios ∈[-1,1]) so `M22↦Sc` is a free-coord translation,
Jac≡1 → `core_schur2_lt_top` applies at exponent `c'−2`.

## Genuinely-new pieces (vs corank-2)
- The JOINT-core SHIFTED peel (corank-2 had both blocks Morse → both leaves; corank-3 has a Morse top +
  a corank-2 residual → peel top, recurse-via-core_schur2 the residual at the shifted exponent).
- The 9-chart outer cover (mirrors the corank-2 4-chart `matBox2_*`; mechanical mirror, threshold-agnostic).
- The shifted-exponent atom `radial_morse_residual_power_le` (in `RadialResidualPower`/`RouteM334Hfin`,
  not yet in my module's closure — import or copy).

## BUILT so far (sorry-free, banked, green)
- Outer 9-chart cover: `matToFlat3`/`measurePreserving_matToFlat3`, `flatBox3`/`matBox3_flatBox_preimage`/
  `gFlat3`/`matBox3_outer_flat`, `gFlat3_cover_sum` (recStep), `Rmat3`, `gFlat3_blowup_radial` (N1 pull-out).
- Per-chart support: `flatBox3_blowup_mem_iff`, `innerS3` (the inner angular S-integral),
  `chart_integrand_factor3` (radial decouple `|y p|⁸ → |y p|^{8−2c'}`, needs `y p ≠ 0`).

## JOINT residual-domination — CLOSED (2026-06-28, the controller's named milestone)

The genuinely-new corank-3 piece is BUILT sorry-free (controller's Fubini/translate decomposition):
- **`matBox2_translate_le`** — the `Fin 2 → Fin 2 → ℝ` matrix-box translate-enlarge
  (`measurePreserving_add_right` + `lintegral_mono_set`; the matrix analog of `lintegral_translate_le_local`).
- **`schurResid2_translate_lt_top`** — for a fixed shift `Sh` (`|Sh i j| ≤ B`),
  `∫_{Δ∈matBox 2 2 T}∫_{S∈matBox 2 4 T} frobSq((Δ − Sh)·S)^{−c''} < ⊤` for `0 < c'' < 2`. Via S-monotone
  enlarge (`matBox 2 4 T ⊆ T+B`) + the `Δ ↦ Δ − Sh` translate (Jac≡1, box-enlarge to `T+B`) →
  `core_schur2_lt_top` at radius `T+B`. The M22↦Sc translation = exactly this (`Sc = M22 − Sh`). The
  R-integrated residual the corank-3 recursion produces (Sc varies, dominated by the free 2×2 box).

REMAINING (the wiring, intricate but no new math): recognize the N2b split's `Sc = M22 − M21·M11⁻¹·M12` as
the `Δ − Sh` shape of `schurResid2_translate_lt_top` (the spectator shift `Sh = M21·M11⁻¹·M12`, bounded via
`rowShear_entry_le_one`) inside the per-chart finiteness (N2b split + inverse-power flip + Tonelli +
shifted-peel feed this residual), then the 9-chart sum → `core_schur3_lt_top`.

(superseded — the JOINT residual-domination is now CLOSED, not a wall):

> After N2b j=1 (r=3) + the inverse-power flip (`schurSplit_integrand_le`) + Tonelli `S=(S_row0,S_bot)` +
> the shifted-exponent peel of the top Morse block (`radial_morse_residual_power_le`, threshold 2, leaving
> the residual at exponent `c'−2`), the residual is `∫_{R-ang}∫_{S_bot} frobSq(Sc(R)·S_bot)^{−(c'−2)}`
> with `Sc(R)` the 2×2 Schur complement `M22 − M21·M11⁻¹·M12`. CLOSE it: per fixed spectators (M21,M12),
> `M22 ↦ Sc` is a translation (Jac≡1) into an enlarged box (shift bounded via `rowShear_entry_le_one`) ⟹
> `core_schur2_lt_top` at exponent `c'−2 < 2` × spectator-box-vol.

The fiddly Lean cost (REST HERE rather than grind, per the controller): the 3×3-block index bookkeeping —
extracting the M22 sub-block (rows/cols {1,2} for the (0,0) pivot) of `Rmat3` as a `Fin 2 → Fin 2 → ℝ`
free-coordinate sub-vector to translate, matching `core_schur2`'s `Δ : Fin 2 → Fin 2` and
`S_bot : Fin 2 → Fin 4` (rows {1,2} of S, reindexed `Fin (3−1)=Fin 2`); the matrix-block-translate (a
4-coord translation embedded in the 9-coord `Rmat3`, other 5 coords spectators) needs a `matBox`-block
analog of `lintegral_translate_le_local`. The MATH is settled (O2 cert + Codex ×2); the remaining cost is
the block reindex/translate plumbing.

## Status (2026-06-28)
Design sharp + cert-grounded (threshold 4 CONFIRMED; R-integrated inner CONFIRMED). BUILT sorry-free,
banked green: the outer 9-chart cover + per-chart support + **the JOINT residual-domination
(`matBox2_translate_le` + `schurResid2_translate_lt_top`, the genuinely-new corank-3 math, CLOSED)**.

REMAINING — the per-chart-assembly WIRING (no new math, the recognition + the sum):
- `matBox3_chart_lt_top` (the `matBox2_chart_lt_top` analog): radial CoV (`chart_integrand_factor3`) +
  `piFinSuccAbove` Tonelli a-axis + the JOINT ratio-residual. The ratio-residual differs from corank-2's
  (which used a UNIFORM per-z bound — the fixed-R undershoot): for corank-3 it is the JOINT z-S domination
  `∫_z∫_S frobSq(Rmat3(e.symm(0,z))·S)^{−c'}` → N2b j=1 flip + Tonelli + shifted-peel →
  `∫_z∫_{S_bot} frobSq(Sc(z)·S_bot)^{−(c'−2)}` → Fubini z=(M22-ratios, spectators), recognize
  `Sc(z) = M22(z) − Sh(spectators)` as the `Δ−Sh` shape → `schurResid2_translate_lt_top` per spectator ×
  spectator-vol. The block-index recognition (the M22 sub-block of `Rmat3` as `schurResid2`'s free `Δ`) is
  the fiddly step.
- `core_schur3_lt_top` = `matBox3_outer_flat` + `gFlat3_cover_sum` + `ENNReal.sum_lt_top` over
  `matBox3_chart_lt_top`. c' < 4.

The corank-2 base case stands closed/reviewed/integrated; the JOINT-domination milestone is banked. The
remaining per-chart wiring is the next focused sub-build (the controller pre-named the per-chart Sc=Δ−Sh
recognition / 9-chart index-matching as a valid rest point).
