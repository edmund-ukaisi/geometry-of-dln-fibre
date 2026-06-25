# A1 band (hband / lambdaCore_eq_clean) — CLOSED. Closure memo (pp-hall, 2026-06-21)

Status: **A1 CLOSED** at `origin/worktree-rung0-defs @9e2faea` — green Lean, axioms clean-three
(`[propext, Classical.choice, Quot.sound]`, no `monomial_rlct`, no `sorryAx`). `static_count` and
`lambdaCore_eq_clean` both 0 sorry. The 4 remaining `Skeleton.lean` sorries are OTHER rungs
(product_reduction, deepest_point_reduction, resolution_charts, the karamata core), not the band.

**Controller-confirmed close (2026-06-21):** a114e07e shipped exactly Option A (FMDom_all strong-induction
wrapper + band-free order-statistic kernel + band-at-<i positional closer); `#print axioms
lambdaCore_eq_clean` = clean-three, full library green. The cliff sweep (0 in-window / 613436 out) was
banked as a third decorrelated leg confirming `τ ≤ uTel_i` is load-bearing. Find-confound tally for the
seam: ~8–9 too-clean simplifications caught/corrected before shipping (several pp-hall self-caught with the
algebra — incl. the "qFM-free goal ⟹ qFM-free proof" overclaim, refuted by the cliff). pp-hall stood down
on A1; awaiting the milestone synthesis.

## The closed structure (the honest route that survived the seam)
The band `qFM_uTel_band : uTel M (qFM M) (j+1) ≤ admBound M j` reduces (via the green τ-split in
`FMDom_of_strongCount` + the consumer `qFM_ge_headP`) to the single achiever lemma `static_count`:
```
static_count (i<L) (hband : ∀k<i, uTel_k ≤ qFM_k) (hlo : M^{i+1}<τ) (hhi : τ ≤ uTel_i) :
    cLt (Ymulti M) τ ≤ cLt ((Mwidths M).drop (i+1)) τ
```
Proof = **order-statistic kernel + positional closer**:
- KERNEL (good_floor_core ONE-SHOT, band-FREE, on FIXED Ymulti): `aS_m < τ` (m := cLt(Ymulti,τ)) via
  `cLt_ofFn` + `cLt_le_of_pointwise` + `aS_succ_le_Yvec` + `aS_mono` + `BGEngine.fin_monotone_lt_of_card_ge`
  (the order-statistic helper, Codex-Lean-checked). Then `cLt(Mfull,τ) ≥ m+1`.
- POSITIONAL CLOSER (band-at-<i via `hband`, NO good_floor_core): `cLt(ws_i,τ) = cLt(Mfull,τ) − 1` via
  the `cLt_erase` chain — `Mwidths.take(i+1) = [M^1..M^{i+1}]` has exactly one element `< τ` (only M^{i+1}
  by hlo; M^1..M^i ≥ τ from `M^k ≥ uTel_k` (= hband via the uTel recurrence) + `uTel_antitone_le` + hhi),
  and M^0 (≥τ) handled separately via `hMfcons : Mfull = (M 0) ::ₘ Mwidths`.

`hband` is supplied by the thin strong-induction wrapper `FMDom_all` (`Nat.strong_induction_on i`):
the achiever step at i consumes only band-at-`<i` (the IH) → well-founded, non-circular. The green per-i
pieces (`qFM_ge_headP`, `headP_ge_uTel`, the τ-split, the tight chain `eraseIter_dom`) are reused unchanged.

## Load-bearing fidelity finding: the band is GENUINELY NEEDED (no band-free saturation)
The single open sorry's goal multisets are qFM-free, which suggested a standalone per-i (band-free) proof.
**Refuted** — three converging exact-algebra tests + the declaration-cycle obstruction + Codex-convergent:
1. **The cliff:** `cLt(Ymulti,τ) ≤ cLt(ws_i,τ)` is FALSE for τ > uTel_i (0 violations in-window / 613436
   just past, over 629954). So `τ ≤ uTel_i` is load-bearing, and `τmax_i` (where saturation last holds)
   = uTel_i EXACTLY in ≈52%.
2. **uTel_i has no band-free closed form:** the natural candidate `uTel_i = min(M^1..M^i)` fails 11849/38160.
   So any band-free bound `B_i` with `uTel_i ≤ B_i ≤ τmax_i` would have to equal uTel_i — impossible.
3. **The positional closer needs the band:** `M^k ≥ uTel_k ⟺ qFM_{k-1} ≥ uTel_{k-1}` (the band; uTel
   recurrence, verified equiv 0/94385); feasibility `qFM_{k-1} ≥ M^k` is INSUFFICIENT (uTel_{k-1} > M^k in
   ~14-26%). Codex count algebra independently: the target ⟺ `pτ + ετ ≤ 1` = the positional-prefix fact.
4. **Declaration cycle:** `static_count @3707` needs M^k≥uTel_k ⟸ band ⟸ `qFM_ge_headP(k-1)` ⟸ `FMDom(k-1)`
   ⟸ `FMDom_of_strongCount @3757(k-1)` ⟸ `static_count(k-1)`. In linear order the k-1<i facts aren't
   established; "facts at <i" exist ONLY inside a strong induction. So standalone per-i does NOT typecheck.

Conclusion: the in-order strong induction (`FMDom_all`) is intrinsic and bedrock-consistent — not a
convenience. (An earlier "static_count non-circular per-i" framing of mine was wrong on exactly this; the
band-at-<i is available only via the IH.)

## The seam in retrospect (decorrelation worked)
~9 "too-clean" simplifications surfaced and each was refuted before shipping (head-RAISING `Dom_head_mono`
unsound; strict-dom_Mtail −1 mixed-strictness; `m≤c` fails; the sorted-vs-positional pw-bridge; 3-region /
region-iii telescope; the compressed submultiset+static_count gap; Route-B sum-gap; "static_count
non-circular per-i"; "qFM-free-goal ⟹ qFM-free-proof"). The honest route (order-statistic kernel band-free
on the fixed Ymulti + positional closer via band-at-<i in the in-order induction) held to bedrock; a114e07e's
green build is the verdict. Full decorrelation trail: `codex/a1-{existence,greedy-redteam,band-static,
carrier,relocate,upward,multi,static,static-count,strongcount,window-index,asm-orderstat,qfmfree}-*.md`.

## Levels kept separate (precision)
This closes the **codimension-side** band (`λ_core = cleanCore` at the achiever, the genuine combinatorial
content). The `rlct = ½·codim` reading still rests on the cited analytic bound (Aoyagi/Watanabe) — that is a
separate, Cited interface, not proven by this band.

Recommended next: the `#print axioms` gate on `lambdaCore_eq_clean` (clean-three) to seal it in AxCheck.
