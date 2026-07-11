# The (S,J) IH-descent build-plan — filling `innerCorankDescent_lt_top` (the real remaining §5 content)

**Seat:** pen-and-paper (build-plan scoping, BEFORE formalising — the gate before commissioning).
**Date:** 2026-07-11. **NO Lean build.** **Charge (team-lead #136):** scope the IH-based (S,J) descent
that fills the skeleton hole `innerCorankDescent_lt_top` (the freed-Γ triple), after schur found the
front-first `g(Q)` UNDERSHOOTS (threshold 3, not 7/2 — it misses the deep-layer `A₂` contribution).

**Read (banked):** `RouteMSJDecoratedPeelStep` (skeleton + the hole statement),
`RouteMSJFreedPeel` (the conditional inner-Γ `freedSchurLoss_inner_peel_lt_top`/`_bounded_lt_top` + its 3
interface hyps), `RouteMSJDecoratedRec`/`RouteMSJDecoratedCharge` (`DecoratedPeelStep`, `peelCharge`,
`half_minAdm_sub_half_peelCharge_le`, driver), `RouteMSJLedger` (`sjLoss`/`genMonomial`/`sjLoss_terminal`),
`RouteMSJLinGen` (`SJLinGenState`, `gen_rowMix_const`, `loss_radialStep`), `peel-buildplan.md §1.3`,
the design cert `genm-sjjoint-design/cert.md`, my `normalslice-cert.md` (#109), `covdesign` §CRUX-PROOF.
**Exact algebra (mine):** `/tmp/prodD/descent.py` (threshold arithmetic). **Decorrelated:** own xhigh
`local-codex-consult` (leaning withheld, asked to adjudicate the zero-slack point adversarially):
`codex/descent-{prompt,answer}.md`. Codex's verdict is adopted — it converges with THREE banked lines
(the design cert, the FreedPeel header, covdesign §CRUX-PROOF).

---

## VERDICT (headline): the deep contribution IS a DECORATED (S,J) monomial descent, NOT a plain-IH reduction and NOT a self-contained front brick. The plain reduced-chain IH is INSUFFICIENT as a black box (zero-slack Hölder). Bounded labour, not a wall — the diag(b) ledger to the banked monomial terminal.

The freed-Γ triple's finiteness `< ½·minAdm` needs the deep-layer `A₂` contribution, which schur's
front-only blow-up omits. The deep contribution is coupled to the front (`w = ‖P·Q̃ₚ‖²` and `Q_b = Y·A₂`
BOTH involve `A₂`); a unit-Jacobian CoV straightens the RANK locus but NOT the coupled loss, so the
coupling must be CARRIED through a rank-flag/monomial descent to the banked terminal
`sjLoss_terminal_lintegral_lt_top`, where the charges ADD to `minAdm`. The plain reduced-chain IH is
insufficient (Hölder demands weight-moment `r' → ∞` at the zero-slack endpoint); it may be invoked only
AFTER the decoration is fully discharged, or the recursive hypothesis must itself be Gram/monomial-decorated.
This is bounded (finite flag + banked terminal estimates) but a SUBSTANTIAL unbuilt resolution — the
diag(b) ledger — NOT plumbing.

---

## 1. The local/IH threshold split (Q1) — CONFIRMED (2 + 3/2 = 7/2)

For `(3,3,3,4)`, binding cut `t=1` (`/tmp/prodD/descent.py`, `exists_binding_cut`):
- `peelCharge = (M₀−t)(M₁−t) = 4`, `½·peelCharge = 2` (the LOCAL/front part).
- `redChain t M = (t,M₂,M₃) = (1,3,4)`, `minAdm(1,3,4) = 3`, `½·minAdm(redChain) = 3/2` (the DEEP part).
- `minAdm(M) = peelCharge + minAdm(redChain) = 4 + 3 = 7` (zero slack); `½·minAdm = 2 + 3/2 = 7/2`. ✓
  (`t=2` also binding: `1 + 6 = 7`.)

So `I(c') < ⊤` for `c' < 7/2 = ½·peelCharge + ½·minAdm(redChain)`, the deep contribution `= 3/2` (the
reduced chain `(1,3,4)`). **schur's front-only undershoot omits the deep layer** — it recovers only the
front, losing the reduced-tail `A₂` contribution (Codex Q1: "loses `1/2` overall, rather than literally
omitting all `3/2`" — the front-only captures part of the deep spectrally but not the reduced-tail
Jacobian). The split is charge accounting, NOT yet a factorisation of the integral — that is the descent's
job.

---

## 2. The route (Q2) — DECORATED Route A (carry the coupling); the plain-IH version is INVALID; Route B duplicates it

**The coupling is irreducible by a unit-Jacobian CoV (Codex Q2, adopted; = design cert + covdesign §CRUX).**
After the threaded shear the exact loss is `‖R̃α‖² + ‖R̃B + S̃Z‖²` (NOT the clean `‖R‖² + ‖Z‖²`); cleaning
`R = R̃α` injects the unbounded `|det α|^{−m}`. In the freed-Γ coordinates, `w = ‖P·Q̃ₚ‖²` and `Q_b = Y·A₂`
**both share `A₂`** — a unit-Jacobian shear cannot turn them into independent reduced-chain variables. So:
- the `normalSlice` CoV (#109) straightens the RANK LOCUS `{rank P ≤ q} ≅ Σ⁰(reduced)` — but NOT the
  coupled loss; the residual is NOT a genuine undecorated reduced-chain box integral;
- the coupling must be carried through a **simultaneous rank-flag / monomial descent** (the diag(b) ledger);
- **Route B (fresh full-deep blow-up) would reconstruct essentially the same flag resolution — less
  economical.** So the tractable + faithful path is DECORATED Route A.

**Consequence for the g(Q) / `qPeelIntegral` route (flag for the obligation-1 audit, #133).** The
`qPeelIntegral` (#131) weighted-AM-GM decoupling requires the deep units `U_i = ‖X_i‖²` to be INDEPENDENT
free blocks — `∫∏U_i^{−w_ic'}` factors as `∏∫U_i^{−w_ic'}` ONLY if the `X_i` are disjoint deep coordinates.
Codex's finding (`A₂` shared between `w` and `Q_b`) says the freed-Γ deep is NOT obviously independent-block.
`onePeel334`'s "clean-coordinate iso `X⊥Z` on disjoint `A₂`-row-blocks" CLAIMS the decoupling; Codex says a
unit-Jacobian shear cannot achieve it. **This is exactly the obligation-1 "wrong-geometry" trap I flagged
(#133): applying the sound abstract `qPeelIntegral` to blocks that are not genuinely independent.** The
audit MUST resolve whether `(b2)`'s cast delivers genuinely-disjoint `A₂`-slices (then `qPeelIntegral`
applies) or fudges the shared-`A₂` coupling (then the decorated descent is required). **Recommend the
decorated (S,J) descent as the ROBUST path** — it does not rest on the contested decoupling.

---

## 3. The zero-slack adjudication (Q3) — the plain IH is INSUFFICIENT as a black box; carry the decoration

Codex Q3 (adopted, and it converges with the design cert + FreedPeel header): after the peel the integral
contains `H · F_red^{−s}`, `s = c'−2 < λ := 3/2`, with an unbounded coupled decoration `H` (the Gram/pivot
weight). Hölder needs exponents with `H ∈ L^{r'}`, `r' > λ/(λ−s)`; as `c' ↑ 7/2` (`s ↑ λ`), `r' → ∞`,
while the Gram/pivot decorations have only a FINITE moment range. **So the strict inequality `c'<½·minAdm`
gives pointwise slack for each `c'`, but NOT the arbitrarily-high weight-integrability needed near the
endpoint — the plain IH does NOT close it.** (This refutes my earlier optimistic "the CoV straightens it,
IH sufficient" leaning — the CoV straightens the rank locus, not the coupled weight.)

**What must be carried (the decoration / the diag(b) ledger):** exceptional/radial divisors; their Jacobian
exponents; the vanishing order of each loss generator along each divisor; which generators SHARE a divisor
(the ADD-not-min coupling); the current rank/pivot chart + bounded unit coefficients. At a terminal chart
the ledger gives an explicit monomial integral and the accumulated charges add to `7` — the banked
`sjLoss_terminal_lintegral_lt_top` closes it. A plain outer IH may be invoked ONLY AFTER the decoration is
fully discharged; if the recursion enters a shorter chain while the weight remains, the recursive
hypothesis itself must be Gram/monomial-DECORATED. **Status: bounded, not a wall** (the flag is finite, the
terminal monomial estimates are banked), but a SUBSTANTIAL unbuilt resolution — the (S,J) diag(b) descent —
NOT plumbing. The plain-IH single-peel architecture is genuinely blocked.

This is the dps-instance-cert / FreedPeel finding, now decorrelated-reconfirmed: `DecoratedPeelStep` is the
DECORATED double induction, not a plain-IH single peel.

---

## 4. The banked bricks (Q3-terminal) — which are the descent's terminal, which are reshape, which off-path

- **ON-PATH terminal:** `sjLoss_terminal_lintegral_lt_top` (`RouteMSJLedger:234`) — the monomial-endpoint
  finiteness `∫(sjLoss e u)^{−c'}·∏|u_ℓ|^{h_ℓ} < ⊤` below the monomial threshold, `sjLoss = Σ_i (∏|u_ℓ|^{e_iℓ})²`.
  This IS the descent's terminal (the decorated ledger's leaf).
- **ON-PATH carrier:** `SJLinGenState` + `gen_rowMix_const` (block-elim / det-1 unit clear) + `loss_radialStep`
  (the Case-2 single radial) (`RouteMSJLinGen`) — the diag(b) ledger's descent steps. On-path.
- **ON-PATH charge:** `peelCharge`, `half_minAdm_sub_half_peelCharge_le`, `Mval_decompose`/`sjChargeBudget_le`,
  `minAdm_eq_frontPeel` (#117) — the charges-ADD bookkeeping. On-path (ℕ).
- **CONDITIONAL (interface, §5):** `freedSchurLoss_inner_peel_lt_top` / `_bounded_lt_top` (`RouteMSJFreedPeel`)
  — the per-`Γ` finiteness GIVEN the 3 hyps. On-path as the inner atom; the hyps are supplied by the descent
  (§5).
- **RESHAPE, on-path IF the decoupling holds (contested, §2):** `qPeelIntegral_lt_top` (#131),
  `block_radial_blowup`, `b1` spectral, `cell_1` — these close the corank-q corner IF the deep casts into
  independent blocks. Per Codex (§2), the freed-Γ deep is NOT obviously independent-block, so these are
  on-path ONLY if the obligation-1 audit confirms disjoint `A₂`-slices; otherwise the decorated ledger
  (`sjLoss_terminal` + carrier) replaces them. **The robust terminal is `sjLoss_terminal`, not
  `qPeelIntegral`.**
- **NOT off-path but NOT the terminal:** `normalSlice_transfer` (#109) — the rank-locus CoV; it straightens
  the rank flag (useful) but does NOT decouple the loss (§2), so it is a descent STEP, not the closer.

---

## 5. The 3 interface hyps as a MEASURE statement (Q4) — the structure + Codex's 3 corrections

`freedSchurLoss_inner_peel_lt_top` needs (i) pivot energy `w = frobSq(P·Q̃ₚ) > 0`, (ii) `Q_bQ_bᵀ` PosDef,
(iii) `c' > a·b/2` — all fail pointwise. The descent supplies them thus (Codex Q4, adopted with its 3
corrections):

1. **Pivot energy `w > 0` (fails on the null `{Q̃ₚ=0}`).** a.e. positivity is NOT enough — the inner-Γ
   integral is finite a.e. but its OUTER integral (over `A',x`) can blow up as `w → 0`. **Resolve and
   integrate the `{w=0}` neighbourhoods JOINTLY in `(A',x,Γ)`** (not a.e.-delete). [= my #128 bridge
   finding: keep the pivot coupled, joint integration.]
2. **`Q_bQ_bᵀ` PosDef (fails on the bottleneck `rank Q_b = r < b`, GENERIC in bottleneck widths).** Use a
   finite minor / rank-flag cover. On full-row-rank cells (bounded from the rank boundary): the conditional
   atom applies. On rank `r<b`: do NOT assert PosDef — integrate only the `a·r` ACTIVE Γ-directions, keep
   the kernel directions inside their bounded box, and RECURSE along the rank flag. [= my #130 rank-stratified
   cell cover + #133 box-boundedness; the active-`r` det⁺.]
3. **`c' > a·b/2` (fails on ~94/480 charts).** This is an EXPONENT condition — CANNOT be supplied by
   integrating `A'`. **Branch explicitly:** `c' > a·b/2` → the full-rank Morse atom (`freedSchurLoss_inner_peel`);
   `c' ≤ a·b/2` → the bounded-Γ estimate `∫_{Γ-box}(w+E)^{−c'} ≤ |Γ-box|·w^{−c'}` (`freedSchurLoss_inner_bounded`),
   then resolve the resulting outer `w^{−c'}` singularity JOINTLY. On rank `r` the ACTIVE threshold is
   `a·r/2`, not `a·b/2`; equality is logarithmic (keep it in the bounded/corner branch). [Both banked
   branches EXIST in `RouteMSJFreedPeel` — `_peel` and `_bounded`; the descent selects per chart.]

So the measure-level architecture: **rank-stratified neighbourhood cover, active-rank atoms on good cells,
bounded-box branches elsewhere, and JOINT monomial resolution of `w`, the rank degeneration, and the pivot
degeneration** — the decorated (S,J) descent.

---

## 6. The build-plan (banked vs fresh)

```
innerCorankDescent_lt_top (the hole)  =  the freed-Γ triple, finite for c' < ½·minAdm
  OUTER (banked): decoratedPeelStep arity recursion — routeMBoxThresholdFinite_of_decoratedPeel (driver),
                  peelCharge + half_minAdm_sub_half_peelCharge_le (the ½peelCharge threshold shift).
  INNER (the fill — the DECORATED (S,J) descent, FRESH):
    (a) outer-tail A' integration + the rank-flag / minor cover  [FRESH cover assembly; #130 shape banked-adj]
    (b) per cell: the branch (c'>ab/2 atom / c'≤ab/2 bounded)     [freedSchurLoss_inner_peel/_bounded BANKED]
        supplied as a MEASURE statement (§5): joint {w=0}, active-r det⁺, kernel-in-box  [FRESH measure glue]
    (c) carry the DECORATION through the SJLinGenState ledger      [gen_rowMix_const/loss_radialStep BANKED;
        (divisors, Jacobian exps, vanishing orders, shared divisors) the ledger threading FRESH]
    (d) terminal: the monomial endpoint, charges ADD to minAdm     [sjLoss_terminal_lintegral_lt_top BANKED;
                                                                     Mval_decompose/sjChargeBudget_le BANKED]
    plain IH: invoked ONLY after the decoration is discharged (or a decorated IH)  [the zero-slack gate, §3]
```

**FRESH (the genuine remaining content):** the decorated ledger threading (the diag(b) state through the
rank-flag descent) + the measure-statement glue for the 3 interface hyps + the rank-flag cover assembly.
**BANKED (consumed):** the driver + charge shift (outer), the two inner-Γ branches
(`freedSchurLoss_inner_peel`/`_bounded`), the carrier steps (`gen_rowMix_const`, `loss_radialStep`), the
monomial terminal (`sjLoss_terminal`), the ℕ charge bookkeeping (`Mval_decompose`, `minAdm_eq_frontPeel`).
**CONTESTED (audit-gated):** the `qPeelIntegral`/independent-block reshape — usable IF the obligation-1
audit confirms disjoint `A₂`-slices; else the decorated ledger is the terminal.

---

## 7. Close

- **Firmest.** Threshold split `2 + 3/2 = 7/2` ✓; the deep contribution `= ½·minAdm(redChain) = 3/2`;
  schur's front-only undershoot omits it. The freed-Γ deep is IRREDUCIBLY coupled (`w`, `Q_b` share `A₂`);
  the plain reduced-chain IH is INSUFFICIENT as a black box (zero-slack Hölder, `r'→∞`); the faithful route
  is the DECORATED (S,J) monomial descent to `sjLoss_terminal`, carrying the decoration. Bounded, not a
  wall (finite flag + banked terminal). Decorrelated Codex converges with 3 banked lines (design cert,
  FreedPeel header, covdesign §CRUX).
- **The correction to my earlier leaning (surfaced honestly).** I had leaned "the normalSlice CoV
  straightens the coupling → plain IH / self-contained qPeelIntegral suffices" (#128 v2, #131). Codex's
  adversarial adjudication + the shared-`A₂` structure show the CoV straightens the RANK LOCUS, not the
  COUPLED LOSS — so the coupling is carried (decorated descent), and the `qPeelIntegral` independent-block
  reshape is faithfulness-contested. This is the obligation-1 "wrong-geometry" trap (#133) made concrete —
  the audit must resolve it; the robust route is the decorated descent (terminal `sjLoss_terminal`, not
  `qPeelIntegral`).
- **Most likely to break / the deepest grind.** The decorated ledger threading (the diag(b) state) is the
  substantial unbuilt content — the "double induction" the design cert named. The measure-statement glue
  (joint `{w=0}`, active-`r` det⁺, the `c'≤ab/2` bounded branch) is #128/#130/#133-shaped but genuinely new
  as a composed Lean statement. NOT a wall (banked terminal + finite flag), but NOT plumbing.
- **Next (the gate).** Before commissioning: (1) resolve the obligation-1 audit (disjoint `A₂`-slices? — if
  yes `qPeelIntegral` is a shortcut, if no the decorated ledger is required); (2) commission the decorated
  (S,J) descent as the robust route — outer driver (banked) + the inner ledger threading (fresh) to
  `sjLoss_terminal` (banked), with the 3 interface hyps as the §5 measure statement. The threshold, the
  charges-ADD, the terminal, and the two inner-Γ branches are all banked; the ledger threading + the
  measure glue are the build.
