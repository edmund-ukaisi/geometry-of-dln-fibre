# Thread 36 — general achiever Jacobian determinant: route adjudication

**Seat:** scout (recon/design). **Date:** 2026-06-26. **Branch:** `expedition/aoyagi-full`.
**Mandate:** adjudicate the route (a / c / hybrid) for the ∀M achiever-chart Jacobian determinant
`|det Dφ_{M,t}| = ∏_j |u_j|^{leafH j}` — the ONE residual gating
`routeMCore_box_diverges_achiever` ∀M (`RouteMLayerCoverGE.lean:130`) — and hand the controller a
broken-down, bounded build plan.

## Deliverable

`design.md` (this thread): route recommendation + the parametric Schur-frame det theorem + the
Mathlib route + the flat-coordinatization plan + the Phase A/B/C bounded build plan + the
(3,3,3,3) cross-check.

## Headline (the reversal vs the wall report `be84b67b`)

The prior wall report scoped the general det as "multi-week parametric Schur-frame/LDU determinant"
and recommended shipping only the 3 anchors. **That estimate predated the structural collapse found
here:** the per-boundary Schur differential is BLOCK-LOWER-TRIANGULAR (TL,TR,BL,BR ↔ dK,dN,dX,dE),
with diagonal blocks `1, K·(−), (−)·K, 1` — so `|det| = |det K|^{r+c}` via `det_pi`, with NO
per-instance SCC `frameB` grading. The det is now a BOUNDED local theorem; the keystone has MOVED to
the flat-coordinate decoder identity `chartParamsFlat = chartParamsGen`.

## Verification (decorrelated, three angles)

- `my_schur_det.py` — independent symbolic check `|det DS| = (det K)^{r+c}` over 10 (t,r,c) profiles. ✓
- `schur_factorization.py` — the differential is block-lower-triangular AND det-correct, all profiles. ✓
- `full_det_check.py` — full-chart (2,2,2) det: u-exp = `minAdm−1`, spectator unit ratio. ✓ (3,3,3,3
  cert-verified upstream, `verify_codex_3333.py`).
- `codex/route-{prompt,answer}.md` — decorrelated xhigh Codex consult. Confirms route (c) + rate
  transfer via `phiGen`; keystone = `chartParamsFlat_eq_chartParamsGen`; det now bounded; injOn
  structural; prefix-fold genuinely needed.
- Standalone Lean elaboration (`/tmp/det_mulleft_check2.lean`, `/tmp/det_conj_check.lean`,
  Mathlib-only) — A1 det-pi route pieces all elaborate clean against the v4.29 pin. The det engine is
  de-risked.

## Recommendation

Route **(c)** for det/cov; rate-transfer via the banked `routeMCore_phiGen`. Keystone =
`chartParamsFlat_eq_chartParamsGen` (C1); riskiest = C1 then the B2 prefix-fold. The det (A1–A3, B3)
is bounded/routine. ≈ 8–10 scoped lemmas across 3 phases — a chargeable sequence of bounded sub-builds,
NOT an open design problem. Full plan in `design.md §4`.

## No Lean edits (recon only). Artefacts: design.md + 3 verify scripts + the codex pair.
