# 2b-i-B F1 SUB-SPEC — the prefix-threading map equality `composeFold fs = phiFlatLiveR1 ∘ kLDU`

Branch genm-interior @e920d323. F1 APPROVED (per-boundary readback via Equiv.apply_symm_apply, reusing the
proven readK_wInt/genBlkFlatLiveR1_wInt_Rmat cancellation). This sub-specs the GENUINE NEW DESIGN — the
foldr prefix-threading — before the cold build. Gate this; then open 2b-i-B as a tide.

## THE FACTOR STRUCTURE (banked machinery, grounded)
Each per-boundary factor is `conjBlockFactor E_s g_s` (RouteMConjBlock), with
  `.f = conjBlockMap E_s g_s = fun u => E_s.symm (Prod.map g_s id (E_s u))`
— applies `g_s` to boundary-s's block `(E_s u).1 : Block_s`, IDENTITY on the rest `(E_s u).2 : R_s`, then
`E_s.symm` back. So factor-s touches ONLY boundary-s's block coords (via E_s); identity elsewhere.
The fold: `composeFold fs = fs.foldr (F g => F.f ∘ g) id` (head applied LAST). `foldDerivList` evaluates
`F_s.D` at the PREFIX `composeFold (tail_s) u` (the factors to s's right, applied first).

## THE PREFIX-THREADING (the genuine new design) — the DISJOINTNESS lemma
The map equality `composeFold fs = chart` holds because the per-boundary factors COMMUTE: factor-s reads/
writes ONLY boundary-s's slots (via E_s), and the E_s block-slots are DISJOINT across boundaries (distinct
boundaries ↦ distinct chartIdxEquiv role-slots — the SAME disjointness readK/X/N/E/W_wInt exploit). So:
  **PREFIX-INVARIANCE: for any factor F_s' (s' ≠ s) applied in the prefix, `(E_s (F_s'.f u)).1 = (E_s u).1`**
  — factor-s' doesn't touch boundary-s's block. Hence factor-s reads the SAME block-value at the prefix
  output as at `u`, so the fold's per-factor action = the decoder's per-block transform, independent of order.
This is the prefix-threading lemma. It reduces (via Equiv.apply_symm_apply on E_s/E_s' + the role-slot
disjointness) to: `E_s ∘ (conjBlockMap E_s' g_s') = (g_s' on E_s'-block, identity on E_s-block) ∘ E_s` —
the two block-CLEs act on disjoint coords. NO global Fin-N bijection; per-pair-of-boundaries disjointness.

## THE SUB-PIECES (the 2b-i-B tide, in order)
- 2b-i-B-1: the per-boundary split-CLEs `E_s : (Fin N → ℝ) ≃L[ℝ] Block_s × R_s` built from chartIdxEquiv's
  role-slots (frameSplitEquiv for the Schur K/X/N/E, the LDUParam for kLDU, liftSlotEquiv for the lift).
  This is the chartIdxEquiv-level construction (the cast surface) — but as a CLE (linear), so it's
  `LinearEquiv.ofFinrankEq`/`Equiv`-level, NOT entrywise. CAST-AVOIDING: build E_s by COMPOSING the banked
  chartIdxEquiv (the role-slot Equiv) with a Pi-reindex to Block_s × R_s — reusing the SAME Equiv the
  readers use, so apply_symm_apply cancels (readK_wInt pattern). The one genuine construction.
- 2b-i-B-2: the DISJOINTNESS / prefix-invariance lemma (above): `(E_s (conjBlockMap E_s' g u)).1 =
  (E_s u).1` for s' ≠ s. Via the role-slot disjointness (the `frameSplitEquiv`/`chartIdxEquiv` slots for
  distinct boundaries are disjoint — provable by apply_symm_apply + the slot-index inequality, like the
  witness's readE = 0 away-from-pivot). The genuine new design.
- 2b-i-B-3: the per-factor MATCH: `conjBlockMap E_s g_s` reproduces the decoder's boundary-s block transform
  (g_s = the Schur frame / LDU lens / chaining on Block_s). Via the reader laws (readK/X/N/E/W) — the SAME
  apply_symm_apply cancellation, PROVEN to work.
- 2b-i-B-4: assemble `composeFold fs = phiFlatLiveR1 ∘ kLDU` by funext + the prefix-invariance (2) threading
  each factor's match (3) through the fold, + the outer linearFactor (paramsEquivFlat∘pack reshape, the
  (4,4,2,2) pattern) + the radialFactor (the radial blow-up, (4,4,2,2) pattern).

## CAST-AVOIDING SUMMARY (the (a)/splitM discipline)
- NO global Fin-N bijection / entrywise Matrix.ext over opaque widths. Everything is per-boundary Equiv-level
  (the E_s CLEs) + apply_symm_apply cancellation (the readK_wInt pattern, cast-clean every time).
- The prefix-threading is the genuine new lemma (2b-i-B-2) — block-disjointness across boundaries; it's the
  foldr analogue of the witness's "readE = 0 away from pivot" (slot-index disjointness).
- RISK: 2b-i-B-1 (the E_s construction) is the cast surface — building the split-CLE from chartIdxEquiv's
  role-slots as a CLE (not entrywise) is the delicate piece. If it thrashes, FALLBACK F2 (define the chart
  AS composeFold fs, transfer only the rate by a map-eq — Codex's item-3 rec; the rate map-eq is local/robust).

## RECOMMENDATION
Open 2b-i-B as a tide, build order 2b-i-B-1 (the E_s CLEs) → 2b-i-B-2 (prefix-invariance/disjointness) →
2b-i-B-3 (per-factor match) → 2b-i-B-4 (assemble). 2b-i-B-1 is the cast surface — if it thrashes >4×,
fall back to F2 (define-as-fold, rate-only map-eq). The genuine multi-tide; a fresh hand can build from this
sub-spec (per remaining budget). Gate the sub-spec (esp. the F1-vs-F2 fallback trigger on 2b-i-B-1).
