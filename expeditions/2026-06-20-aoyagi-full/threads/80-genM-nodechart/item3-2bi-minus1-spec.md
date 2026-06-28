# 2b-i + the −1 lemma — SPEC (cast-avoiding, for the controller's gate before cold build)

Branch genm-interior @0806e6fb. All interior files sorry-free (2e CLOSED). This specs the −1 lemma
(leafH_pivot = minAdm−1) + 2b-i (the monomial det |det Dφ| = ∏|u_j|^{leafH j}), with the cast-avoiding
formulation (the slot-guard discipline that made (a) land first-try). Build WITH 2b-i per the controller.

## THE TARGET (the cov field's det + leafH_pivot)
`NodeAchieverChart` needs: `leafH : Fin N → ℕ`, `leafH_pivot : leafH (structPivot) = minAdm − 1`, and
`cov`'s `|det Dφ(u)| = ∏_j |u_j|^{leafH j}`. The chart is `phiFlatLiveR1 ∘ (kLDU lens)` (R1 active-center
decoder, banked sorry-free; the kLDU LDU-lens, banked).

## THE CAST-AVOIDING FORMULATION (the (a) lesson: avoid chartIdxEquiv-level surgery)
(a) landed first-try because the slot-guard verdict ⟹ Function.update (ℕ-indexed) NOT a Fin-N bijection.
The 2b-i analogue: use the banked composeFold/ChartFactor/det_comp machinery (general-width, NO
chartIdxEquiv surgery in the DET) — `phiTarget_abs_det_of_factored phi fs hmap leafH u hdet`:
  GIVEN `composeFold fs = phi` (the item-3 map equality) + per-factor det bookkeeping `hdet`,
  DELIVERS `|det Dφ| = ∏|u_j|^{leafH j}`.
The factors (all banked, conjugated by abstract CLEs — NO literal Fin-N indices in the det):
  fs = [linearFactor Q (the paramsEquivFlat reshape, det 1), radialFactor active p (det |u_p|^{card−1}),
        per-boundary lduChartFactor/schurChartFactor (the LDU monomial + |det K|^{r+c})].
The det side is then CAST-LIGHT (the composeFold telescope); the cast WEIGHT is item-3 (the map equality
composeFold fs = phiFlatLiveR1∘kLDU over opaque widths — the genuine bottleneck, the per-boundary split-CLE).

## THE −1 LEMMA (leafH_pivot = minAdm−1) — the count-level core, cast-avoiding
DEFINE `leafH` from the per-factor det product (the `hdet` RHS): leafH p = (radial exponent) = active.card−1;
leafH (LDU-pivot/Schur axes) = the per-boundary exponents; leafH (else) = 0. Then `leafH_pivot = minAdm−1`
reduces to:
  **`active.card = minAdm`** where `active : Finset (Fin N)` = the radial blow-up active set.
THE CARD-BRIDGE (count-level, from budget_identity, cast-light):
- budget_identity (banked, ℤ): `∑_{k:Fin L} chainEdimZ M k + Text(L)·Wext(L) = minAdm` (TOTAL = minAdm).
- chainEdimZ k = rBlock·cBlock ≥ 0 (rBlock_nonneg/cBlock_nonneg banked). So the ℤ sum = a ℕ sum, and
  `(∑ chainEdimZ + leaf).toNat = minAdm` (Int.toNat round-trip, all summands ≥ 0).
- `active` = the union of the R-block coordinate slots (the u-scaled directions). `active.card` = #R-block
  slots = the same ∑ r_k·c_k + leaf = minAdm (the slot-count IS the budget). The bridge: active.card
  (ℕ Finset) = (∑ chainEdimZ + leaf).toNat (the slot↔dim identity) = minAdm.
- radial exponent = active.card − 1 (radialFactor_abs_det = |u_p|^{active.card−1}, banked); the −1 = the
  ONE fixed pivot (the R1 decoder's fixed-1 / the blow-up gauge). So leafH p = minAdm − 1. ✓
CAST-AVOIDING: `active` is a Finset (Fin N) defined via the SAME chartIdxEquiv role-slots the readers use,
but the CARD is computed via the budget (ℕ arithmetic), NOT a Fin-N bijection — mirroring (a)'s
Function.update (count, not bijection). The slot↔dim identity (active.card = ∑ r_k·c_k + leaf) is the one
new piece; it's a Finset.card-over-chartIdxEquiv-slots count, provable via card_chartIdx-style sum (banked
chartDim_eq_flatDim is the template — same shape, restricted to the R-block sub-slots).

## SUB-PLAN (2b-i, WITH the −1 lemma)
- 2b-i-A: `active : Finset (Fin N)` def (the R-block u-scaled slots) + `active.card = minAdm` (the card-bridge:
  budget_identity + rBlock/cBlock_nonneg + the slot↔dim count). [count-level, cast-light]
- 2b-i-B: the item-3 map equality `composeFold fs = phiFlatLiveR1 ∘ kLDU` over opaque widths (the per-boundary
  split-CLE; the GENUINE cast weight — spec-gate this separately if it thrashes).
- 2b-i-C: the per-factor det bookkeeping `hdet` (radial active.card−1 + per-boundary LDU/Schur via the banked
  _abs_det lemmas) summing to leafH. Then phiTarget_abs_det_of_factored ⟹ the monomial det.
- 2b-i-D: define leafH from the product; leafH_pivot = minAdm−1 (= active.card−1 via 2b-i-A).

## WALL-CHECK / RISK
- The CARD-BRIDGE (2b-i-A): bounded (budget_identity banked; rBlock/cBlock_nonneg banked; the slot↔dim
  count is a chartDim_eq_flatDim-shaped Finset sum). The one subtlety: `active` must be EXACTLY the u-scaled
  R-block slots (Rmat-E interior + leaf Rfin), and the R1 fixed-1 pivot is ONE element of active (the gauge).
  active.card−1 (not card) = the genuine angular count = minAdm−1. ✓ matches the cert.
- The MAP EQUALITY (2b-i-B): THE bottleneck (item-3, the per-boundary split-CLE over opaque widths — the
  same dependent-Fin fight, deferred from the start). RECOMMEND: spec 2b-i-B (the composeFold = chart map
  equality) as its own gate AFTER 2b-i-A/C/D land (the count + det bookkeeping are cast-light; the map
  equality is the heavy cast).
- DO NOT cite budget_identity as #angular=minAdm−1 (genm-budgetrev flag) — it's TOTAL=minAdm; the −1 is the
  active.card−1 (one fixed pivot), proven via the card-bridge.

## RECOMMENDATION FOR THE GATE
Build order: 2b-i-A (card-bridge, active.card=minAdm — count-level, cast-light, the −1 lemma core) FIRST;
then 2b-i-C/D (det bookkeeping + leafH def, given the map equality as a hypothesis, mirroring
RouteMPhiFlatDet's `phiFlat_abs_det_of_factored` which takes the map equality as input); then 2b-i-B (the
map equality) as a SEPARATE spec-gated piece (the genuine cast weight). This isolates the cast-light count
(landable now) from the cast-heavy map equality (needs its own design pass). Confirm before I open 2b-i-A.
