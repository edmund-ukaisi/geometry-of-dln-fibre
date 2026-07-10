# genm-sjslice — build spec: the FIRST VERTICAL SLICE of the native (S,J) resolution — (3,3,3,4) corank-2

**The Stage-2 PIVOT's first build.** The front-peel shortcut is refuted (triple-decorrelated: it over-charges
the rank flag). The finish is the charter's native (S,J) simultaneous rank-flag resolution. This tide is
**validate-small-first**: formalise the `(3,3,3,4)` corank-2 (S,J) resolution vertical (task #104's cert →
Lean, ONE flag branch) to **shake out the CoV/resolution-map SHAPE + resolve the hIH question** before the
width-general grind. **READ FIRST (in full):**
- `threads/genm-sjrecon/recon-map.md` — THE map (CONSUME/STAGED/LESSONS/DEAD/GAP, all `file:line`-verified).
  Every banked brick you consume + every dead route to avoid is there. This spec is its distilled build order.
- `threads/genm-vslice/cert.md` (task #104 — the composed (S,J) machine END-TO-END on `(3,3,3,4)` corank-2:
  cover → radial → unit-clear → absorb → recurse → monomial endpoint → charges `[4,3,0]=minAdm=7`, sympy-exact).
  **This is the pen-and-paper you are formalising.**
- `threads/genm-covdesign/cert.md` §COUPLED-PIVOT-RESOLUTION (WHY the front-peel fails — the flag must be
  resolved simultaneously) + `stage2-brief.md` (the (S,J) strategy + the det-inverse compass) + `lean/CLAUDE.md`.

## GOAL (this slice)
On the concrete chain `M = ![3,3,3,4]` at corank 2 (the binding flag branch of task #104), formalise the
native (S,J) resolution of the per-chart integral `gammaPeelIntegral` for ONE flag branch, via
**radial blow-up → `blockShear_step` det-1 unit clear → ledger step (`RouteMSJLinGen` radialStep/rowMix) →
terminal endpoint (`RouteMSJLedger`/`RouteMSJTerminal`)**, proving the concrete chart-integral finiteness
(or the largest representative sub-piece you can close cleanly). **This is a SHAPE-VALIDATION slice, not the
full leaf** — concrete widths (no opaque-width casts), one flag branch. Deliverable = the resolution-map
construction on the slice + a REPORT (below).

## BRANCH / BASE
- Worktree; base on `origin/genm-cruxfinish` via `git fetch origin genm-cruxfinish && git reset --hard
  origin/genm-cruxfinish` (it carries `blockShear_step` + `rank_eq_q_add_of_normalForm` in
  `RouteMSJThreadedShear`, the front-peel endpoints, AND the base-branch ledger). VERIFY `RouteMSJLedger` +
  `RouteMSJLinGen` are present (`git show HEAD:…RouteMSJLedger.lean | head`); if absent, cherry-pick from
  `origin/expedition/aoyagi-full`. Push to a NEW branch `git push origin HEAD:genm-sjslice`.
- New file `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJSlice334.lean` (single-writer, yours).

## THE RESOLUTION-MAP SHAPE (from recon GAP §1–2 + #104 cert — build this concretely)
A recursion of `(radial blow-up → det-1 unit clear → absorption-by-renaming into the next factor)` indexed by
the rank flag, each level measure-preserving up to a MONOMIAL Jacobian, landing on the banked terminal:
1. **Entry:** `loss_ofMatrix_product` (`RouteMSJLinGen:166`) connects `gammaPeelIntegral`'s integrand
   `frobSq(rmatMul A₀ (prod (tailChain M) A'))^{−c'}` to the ledger carrier loss.
2. **Radial blow-up** (Case-2 step): `radialStep`/`loss_radialStep` (`RouteMSJLinGen:176/192`) +
   `RouteMSJLedger.prependColumn`/`sjLoss_prependColumn_one` — the `u²` radial factor via `corankStep`
   (`RouteMSJCorankStep:88`), Z-agnostic; charges accumulate ADDITIVELY (the "sum-not-min" corner, recon
   LESSONS — AVOID `fibre_lintegral_mul_le`/product-min, the ×2 undershoot).
3. **Det-1 unit clear:** `blockShear_step` (`RouteMSJThreadedShear:105`, `⅟α`→`⁻¹` via `invOf_eq_nonsing_inv`)
   → block-upper form; `rank_eq_q_add_of_normalForm:55` reads off `rank P = q + rank Z`. **Compass: `α⁻¹` a
   unit coefficient only, Jacobian det 1 — NO det-inverse.**
4. **Block-elimination / row-mix:** `gen_rowMix` (`RouteMSJLinGen:232`, conditional on `hsh`) — on the slice,
   discharge `hsh` concretely (`gen_rowMix_const:251` at fresh common-support blocks); `loss_blockSplit:290`
   is the additive split the corank decrement lands on.
5. **Recurse** down the flag `{rank≤q}⊃{rank≤q−1}⊃…` (the whole point — resolve SIMULTANEOUSLY; the
   front-peel's single-corank peel over-charges the deeper strata, cert §COUPLED). On `(3,3,3,4)` corank-2
   this is the concrete corner blow-up (#104: accumulate `3+2+1`, terminal power `Σqⱼ−1`, threshold `½·minAdm=7/2`).
6. **Terminal endpoint:** `sjLoss_terminal_lintegral_lt_top` (`RouteMSJLedger:234`) / 
   `terminal_monomial_mul_unit_lintegral_lt_top` (`RouteMSJTerminal:160`, consumes bounded-below cores as
   `hunit`). Supply `hunit` via the nonzero-poly a.e.-positivity technique (recon GAP §5: `Uval4422_ae_pos`-style).

## ★ THE hIH QUESTION — REPORT the answer (recon-flagged controller decision)
The leaf hands an arity-IH (`∀ M':Fin(L+1+1)→ℕ, RouteMBoxThresholdFinite M'`). The native (S,J) route
terminates over the rank FLAG (the `remaining` measure), not arity. **On this slice, determine EMPIRICALLY:
does the `(3,3,3,4)` corank-2 construction CONSUME the arity-hIH (at reduced-tail leaves), or is it
SELF-CONTAINED (terminates via the flag/support + the banked terminal, hIH unused)?** Keep `hIH` as a
hypothesis (unused is fine, as `sjJointResolution_frontPeel`'s `_hIH` does). Your finding decides the
width-general induction structure (self-contained (S,J) kernel vs total-width IH) — report it explicitly.

## AVOID (recon DEAD — do NOT touch)
The `sjJointResolution` docstring's Gram `Γ↦Γ·Q_b` route (`RouteMSJFreedPeel` — rewrite the docstring, don't
follow it); the front-peel `normalSlice_transfer` CRUX (`RouteMFrontPeelCarrier:222` — REFUTED; reuse only its
proved endpoints `shiftedThreshold`/`outerRankCover`/`morseCore_residual_lt_top`); the decorated EXTERNAL
predicate `DecoratedBoxThresholdFinite` (mine only its chart-move/measurability bricks); the SEAM route; `#70`.

## DISCIPLINE
- `lean/scripts/lb` ONLY (never bare `lake`); no `lake exe cache get` in the worktree.
- Green-gate the FULL `lake build DLNFibre` before "ready"; AxCheck via FORCE-RECOMPILED `#print axioms`
  (clean-three), never exit-0. Canonical stays 0-axiom + delivered-headlines-clean-three; your gaps on
  `genm-sjslice` only.
- INCREMENTAL push — commit + push each green sub-piece; do NOT go >~45 min uncommitted (a peer crashed).
  Checkpoint + SendMessage the controller (≤180 chars) at: entry-wired, each resolution level green, terminal
  reached, and the SHAPE report.
- Opaque-width casts DON'T bite here (concrete widths) — but note where the general lift will (recon LESSONS).
  Dependent-dim reassoc via `mul_three_reassoc`; `⅟`→`⁻¹` via `invOf_eq_nonsing_inv`; ASCII binders;
  `decide +kernel`. The COMPASS: a det-inverse in a Jacobian = re-express (radial + unit clear + rename); it is
  NOT a wall — the native form exists (charter). Isolate a minimal named sub-sorry + build above it if a step
  resists; report — do NOT halt. Native rank-normal-form only; the `rlct=½codim` reading stays Cited.
- **Fire a decorrelated `local-codex-consult`** if the resolution-map CoV shape (GAP §1) is ambiguous — it is
  the ~65-75%-new heart; get the chart-tree right on the slice before the general grind.

## REPORT (the deliverable — this slice's VALUE is the shape, not just a green)
1. The resolution-map SHAPE that worked (the concrete chart-tree: which blow-up/clear/absorb sequence, which
   banked bricks composed, the Jacobian monomial at each level).
2. The hIH answer (consumed vs self-contained).
3. What GENERALISES to width-general + what's the opaque-width residue (GAP §4) + the `hsh` faithfulness
   status (GAP §3).
4. Any banked brick that DIDN'T fit / needed a new sub-lemma (so the general spec names it).
