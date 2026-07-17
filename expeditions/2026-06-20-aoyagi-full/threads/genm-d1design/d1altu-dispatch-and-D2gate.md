# d1altu-dispatch + D2-gate — the DEFINITIVE d1-a<u by_cases + the #2 feasibility gate (gate-YES, detail-at-scale)

**Seat:** pen-and-paper (design), `genm-d1design`, Lane 1. **Date:** 2026-07-17. **NO Lean.** Two deliverables:
(A) the ONE definitive d1-a<u build dispatch for d1altu (stop the route-churn); (B) the D2 confirming gate
(does the wing rank-σ stratum reuse qbox/projection — detail-at-scale — or need a monolithic det-variety
module — multi-tide?). Verified: `scripts/{d1altu_dispatch,d2_charge_reconcile}.py` + jointpnp TEST-4.

---

## A. THE DEFINITIVE d1-a<u DISPATCH (for d1altu — build from THIS, one clean spec)

`a = M₀−t`, `b = M₁−t = 1` (d=1 via b=1; a<u=t), `redChain t M = (t, M₂, …)`. Disposal
`∫ (W + frobSq(C·Q̃ₚ + γ⊗Q_b))^{−c'}`, `W = frobSq(P·Q̃ₚ) = frobSq(X·Q)`, `X=[P|B₁₂]` (`t×M₁`). Two axes:

    by_cases hlow : (c' : ℝ) < minAdm (redChain t M) / 2
    · -- α-LOW: DROP the WHOLE corank term (freedSchurLoss ≥ W, C,Γ-free ⟹ integrand ≤ W^{−c'}), corank →
      -- bounded box vol, → frontCollapse(X) at exponent c', CHARGE 0 (NOT c'−a/2 — dropping the WHOLE corank
      -- forgoes the a/2 corank charge). Reduces frobSq(X·Q) → hIH(redChain t M) at c'.
      by_cases hM2 : M₂ ≤ b
      · -- CLEAN NOW: frontCollapse_wide_bounded_lt_top (LANDED) at c'. [+ the a.e. null-removal on {W>0}
        --   via MvPolynomial.ae_eval_ne_zero — hpiv supplied.]
      · by_cases hlog : M₂ = b + 1
        · -- LOG: frontCollapse LOG δ-fold over the bounded base (one_add_log_inv_le_rpow).
        · -- M₂ ≥ b+2: frontCollapse POWER = #2 (wing front det resolution).  ⟨SORRY, gated on #2⟩
    · -- α-HIGH: c' ≥ ½·minAdm(redChain t M) ⟹ the drop-whole-corank threshold is exceeded ⟹ the a/2 corank
      -- charge is NEEDED. KEEP the corank (the ‖Q_b‖-weighted joint incidence) = the HEART's rank-1 (b=1)
      -- FreeBilinear leaf, reducing to hIH(redChain t M) at c'−a/2.  ⟨SORRY, gated on the heart rank-1 leaf⟩

**CONFIRMED (lane1shell's points):** the α-LOW branch is frontCollapse(X) at **charge 0** (exponent `c'`, NOT
`c'−a/2` — the whole-corank drop forgoes the a/2), so it needs **`c' < ½minAdm(redChain t M)` AND `M₂ ≤ b`**
for the clean landed frontCollapse. **NEVER `edge_C_shift_bound`** (that's the drop-TRANSVERSE = DECORATED,
Codex D_inc). NEVER the nested-qbox.

**Census (`scripts/d1altu_dispatch.py`, d1-a<u, L∈{4,5}, w≤6; 3024 cuts):**
| β \ α | α-high VACUOUS (drop-corank covers all c'<½minAdm M) | α-high REACHABLE (heart rank-1 for the high range) |
|---|---|---|
| **M₂≤b LANDED** | 496 — FULLY CLEAN NOW | 428 — clean drop-corank range + heart rank-1 |
| **M₂=b+1 LOG** | 213 — LOG δ-fold covers all | 291 — LOG + heart rank-1 |
| **M₂≥b+2 POWER(#2)** | 437 — #2 covers all | 1159 — #2 + heart rank-1 |

α-high (heart rank-1) reachable [`minAdm(redChain t M) < minAdm(M)`] for **1878/3024**; vacuous (drop-corank
covers all) for **1146/3024**. So d1altu's CLEAN-NOW scope = the α-LOW + M₂≤b cells (924 cuts: 496 fully +
428 partial); LOG = M₂=b+1; #2-gated = M₂≥b+2 (α-low) ⊕ the heart-rank-1-gated = α-high (all β).

## B. THE D2 CONFIRMING GATE — **gate-YES: DETAIL-AT-SCALE (reuses qbox row-recursion + projection_rpow + FreeBilinear per-stratum). #2 = a tide, NOT multi-tide.**

**The gate:** does each wing rank-σ stratum `{rank A₁=σ}` (A₁ the free `M₁×M₂` tail layer, jointpnp TEST-4:
`{rank W≤σ}` = surjective-X preimage of `{rank A₁≤σ}`, single-matrix det) express via `det_gram`(sub-block)
/ `projection_rpow` per-level reducible to `hIH(redChain σ M)` — OR need a MONOLITHIC rank-σ blow-up module
(absent in Mathlib)?

**ASSESSED gate-YES (structural argument):**
- **The `{rank A₁=σ}` resolution of a SINGLE free matrix IS qbox's machinery.** qbox
  (`qbox_lintegral_lt_top`) is the `det_gram` ROW-RECURSION: peel A₁'s rows one at a time (`det_gram_cons`),
  each row's rank-contribution = its `projection_rpow` onto the span of the previous rows. `{rank A₁≤σ}` =
  {the rows after the σ-th lie in the σ-dim span} = the projection radials (`projection_rpow_lintegral_uniform`,
  a<r) vanishing. So the rank-σ determinantal resolution of A₁ = the row-recursion (Gram-Schmidt row-peel with
  the rank-drops as projection radials) — the EXACT machinery `qbox` is built from. NO monolithic blow-up.
- **σ=1 is the banked FreeBilinear.** On `{rank A₁=1}`, `A₁ = u⊗v` (rank-1); the loss factors
  `frobSq(X·(u⊗v)·Z_deep) = ‖X·u‖²·‖v·Z_deep‖²` = the FreeBilinear form (`freeBilinear_box_lt_top`, banked).
  Confirmed on the SQUARE template M=(2,2,3,3)@s=1 (`{A₁=0}` = radial codim 6 rlct 3; `{rank A₁≤1}` = row-2's
  projection onto row-1, projection_rpow codim 2).
- **General σ:** the rank-σ stratum's transverse = the `(M₁−σ)` remaining rows' projections onto the σ-dim
  span (projection_rpow, codim `(M₁−σ)(M₂−σ)`); the σ-dim core reduces to `hIH(redChain σ M)` (leading layer
  `V`, σ×M₂). So the stratum = [projection_rpow transverse] + [hIH(redChain σ M)] + [the (M₀,σ) front `X·U`
  via qbox/frontCollapse], charge `(M₀−s)(M₁−s)` (the M₂-excess absorbed by the reduced (s,M₂) layer,
  `d2_charge_reconcile.py`). ALL reused banked machinery.
- **Same dodge-family** as the a=0-bounded (GS square-CoV dodged coarea) + the b=0 reduced-chain recursion:
  the wing rank-σ DODGES the absent general det-variety primitive via the qbox/projection row-recursion.

**So #2 is DETAIL-AT-SCALE — a single tide** (the det-variety kit D1–D5 = the row-recursion + FreeBilinear +
projection_rpow per-stratum + the front qbox + the charge reconciliation), NOT a from-scratch monolithic
det-variety module (multi-tide). **Status: ASSESSED (structural, not hard-proved)** — recommend jointpnp
cross-check the row-recursion expression (its decorrelated eye on "the {rank A₁=σ} exceptional = the row-peel
projections, no bespoke monomial"). My lean: gate-YES, firmly.

**The one residual care (where gate-NO could hide):** if some wing rank-σ stratum's transverse Jacobian is NOT
a pure product of row-projection radials but a genuinely-coupled determinantal monomial (needing the general
Segre/Room-Kempf resolution, not the row-recursion), THEN monolithic (multi-tide). I judge NOT — the
single-matrix A₁ row-recursion (Gram-Schmidt) IS the standard resolution, and qbox already realizes it for the
det_gram form. jointpnp's cross-check settles it.

## GATE CONFIRMED — jointpnp decorrelated (exact symbolic), 2026-07-17

**gate-YES, detail-at-scale — HARD-SETTLED.** jointpnp cross-checked decorrelated (exact symbolic) and
confirmed the `{rank A₁=σ}` resolution is a PURE PRODUCT of row-projection radials; reuses
`det_gram_cons`/qbox/projection_rpow, NO bespoke Segre/Kempf. Load-bearing exact facts verified:
- `det(A₁A₁ᵀ) = ∏ₖ dist(rowₖ, span(rows<k))²` (checked 2×3, 3×3, 3×4) — pure product of per-row projection
  radials, NO cross-terms (= det_gram_cons).
- On the dominant-σ-row chart, `codim{rank A₁≤σ} = (M₁−σ)(M₂−σ) = Σ_{(M₁−σ) non-pivot rows} (M₂−σ)`; each
  non-pivot row = ONE projection_rpow onto the (M₂−σ)-dim complement of the pivot span (converges iff
  exponent `a < M₂−σ = finrank U⊥`). Threshold = codim/2. Reuses projection_rpow **verbatim**.
- **σ=2 witness (my concrete cell, exact):** `det(A₁A₁ᵀ) = det(pivot 2×2 Gram)·ε²·‖n‖²`, ε = 3rd-row
  projection onto the pivot-span complement — the rank-2 transverse is a SINGLE projection radial × bounded
  pivot Gram, NOT a coupled monomial. The varying pivot-span is absorbed by **projection_rpow's UNIFORMITY**
  (stated for finrank U ≥ r) — subspace-variation creates no cross-term. σ=1 = FreeBilinear, confirmed.

So the full #2 Jacobian = [∏ (M₁−σ) row-projection radials] × [front X·U qbox] × [σ-core → hIH(redChain σ M)]
— all banked, pure product. **ONE detail-at-scale tide** (finite dominant-σ-minor chart atlas + per-chart
qbox + sum = N1–N5, reusing the harness's existing dominant-minor cover).

### TWO LOAD-BEARING CAVEATS (jointpnp, keep beside the build)
1. **PEEL-FIRST GUARD (the gate-NO exclusion is conditional).** The genuine gate-NO trigger — a PRODUCT Gram
   `det((CZ)(CZ)ᵀ)^{−r/2}` (two coupled matrices) — is excluded ONLY because the front is full-rank ⟹ the
   Gram is always SINGLE-matrix. gate-YES is **conditional on the build holding PEEL-FIRST**: if any step
   integrates a corank block against a tail product FIRST, the Gram becomes coupled and it is back to the dead
   nested-qbox. **Keep the residual-disposal (retain-γ) guard** — this is the standing kill-condition for #2.
2. **N3 plumbing is a build call.** jointpnp confirmed the determinantal/Gram structure is a pure product
   (the MATH discriminator); the exact Lean monomial-Jacobian identity (N3) coupling this to `‖X·A₁·Z‖²` is
   the formaliser's plumbing — the math CAN close via qbox/projection_rpow; the wiring is the build's.

Ref: jointpnp `scratch/l1_gate2_check.py` (its worktree; diff to re-home via controller).

## Close
- **A (dispatch):** the definitive d1-a<u by_cases (hlow × hM2), CHARGE 0 for the drop-whole-corank, banked
  frontCollapse_wide_bounded (M₂≤b clean) + LOG (b+1) + #2 (≥b+2) + heart-rank-1 (α-high). d1altu builds ONE
  clean spec; clean-now = α-low ∧ M₂≤b (924); sorries precisely scoped (#2-gated, heart-rank-1-gated).
- **B (gate):** gate-YES, DETAIL-AT-SCALE — **CONFIRMED (jointpnp, exact symbolic)**: the wing rank-σ = qbox
  row-recursion + projection_rpow + FreeBilinear per-stratum; NO monolithic det-variety primitive. #2 = a
  single tide. Two caveats: PEEL-FIRST guard (gate-NO exclusion conditional) + N3 plumbing = build call.
- **Next:** #2 is a single detail-at-scale tide, held to PEEL-FIRST. d1altu builds the dispatch.

Files: `…/threads/genm-d1design/d1altu-dispatch-and-D2gate.md` (this); `scripts/{d1altu_dispatch,d2_charge_reconcile,d1_wing_stratum_rank}.py`; `d2-wingfront-pin.md`, `joint-coupled-spec.md`.
