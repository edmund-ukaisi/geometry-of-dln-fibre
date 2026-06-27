<task>
DLN deepest-point loss-squeeze cert (Lean 4 / Mathlib). I must close ONE geometric cert
`framedParams_split_eq_frame_raw`. The cert is currently UNPROVABLE as-stated because of a
frame-conjugation mismatch. My controller's design call is: "wire the per-layer gauge frame into the
READING (framedParams's framedLayer), NOT into the MP split." I need you to red-team this call and
pin the exact lemma that closes the cert (or surface if it cannot).

OBJECTS (all real, in the repo):
- `H : Fin (L+1) → ℕ` layer widths; `r` the deepest rank; `B` the target, `B.rank = r`.
- `Params H := (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ` (a layer tuple).
- `prod H A : Matrix (Fin (H 0)) (Fin (H (last))) ℝ` = ordered product of the layers.
- `dlnLoss H B A = ∑ᵢⱼ ((prod H A − B) i j)²` (square-Frobenius loss).
- `paramsEquivFlat H : Params H ≃ᵐ (Fin (flatDim H) → ℝ)` (flattening); `paramsSymm w := (paramsEquivFlat H).symm w`.
- `deepestPoint H r B … : Params H` — the deepest critical point. `(deepestPoint s).rank = r` each layer.
- `deepestPoint_frame H r B … s = (P_s, Q_s)` — per-layer GL units (Classical.choose of rank-normal-form)
  with `P_s · (deepestPoint s) · Q_s = corM` (the block-normal corner blockdiag[I_r, 0]). NOT det-1 in
  general (genuine GL units).
- Interior frames are trivial: interior `deepestPoint s = corM` already, layer-0 right-cols vanish,
  layer-(L−1) left-rows vanish. So in the framed product only the two ENDPOINT frames P_0, Q_{L−1} survive.
- `endpoint_telescoping` (PROVEN, sorry-free): if `C s = P_s · A_s · Q_s` per layer and interior
  interfaces collapse (`Q_s = I`, `P_{s+1} = I` adjacent), then `∃ P0 QL units, prod H C = P0 · prod H A · QL`.
- `split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge` — supplied by `deepestSplit_exists`, a
  MEASURE-PRESERVING (det ±1) bare INDEX REINDEX + translation (carries deepest ↦ 0). NO frame inside.
  `DeepestSplit = (Fin nReg → ℝ) × ((Fin (flatDim (deepestM)) → ℝ) × (Fin nGauge → ℝ))` = (reg, (core, spec)).
- `regGaugeSlotEquiv : (reg × spec slots) ≃ₜ (RegGaugeIdx → ℝ)` — un-flattens the split's reg+spec
  slots into a per-layer X/Y/Z gauge-block grouping (pure coordinate relabel).
- `readX/Y/Z H r hr hL p s` — read the per-layer gauge blocks (X_s : r×r, Y_s : r×(H_{s+1}−r),
  Z_s : (H_s−r)×r) off `regGaugeSlotEquiv p` (p = the (reg, spec) slot). Pure coordinate reads.
- `framedLayer H r hr s X Y Z T = reindex(fromBlocks (1+X) Y Z T)` — a `Params H` layer from gauge blocks.
- `framedParams H r hr hL q := fun s => framedLayer … (readX (q.1,q.2.2) s) (readY …) (readZ …)
   ((paramsEquivFlat (deepestM)).symm q.2.1 s)` — the framed layer tuple from a DeepestSplit point.
- `framedParamsReg` = `framedParams` with the core block T := 0 (the reg-only, core-independent half;
  `deepestEPivot` reads its product's regular blocks).
- The architecture's OWN contract (docstring): `gaugeDecode = gaugeSlotRead ∘ frame ∘ (split.symm − deepestFlat)`
  — i.e. the per-layer frame is meant to sit BETWEEN split.symm and the gauge read.

THE CERT (what must close), for w near the deepest point:
  reindex(P0 · (prod(paramsSymm w) − B) · QL) = fromBlocks (P00−1) P01 P10 P11
  AND  P00/P01/P10 = the regular toBlocks of  reindex(prod(framedParamsReg (split w).reg, (split w).spec))
  AND  the leak ∑(P10 ⅟P00 P01)² ≤ t²·∑E²
  AND  ∑(P11 − P10 ⅟P00 P01)² ≍ deepestCoreF (coreAbsorb (split w)).2.1  (two-sided comparability).

THE MISMATCH I found: `prod(paramsSymm w)` endpoint-frame-conjugated by P0/QL telescopes the FRAMED
product (layers P_s · (paramsSymm w)_s · Q_s). But `framedParamsReg(split w)` reads gauge blocks RAW
off `split w` (no frame). So the framed-product blocks and the framedParamsReg blocks match ONLY if
`framedParams(split w) s = P_s · (paramsSymm w)_s · Q_s` per layer — a round-trip that is NOT supplied
(prior Codex consult flagged exactly this as "the input, not supplied by telescoping").

THE DESIGN CALL to red-team: put the frame into framedParams's READING (framedLayer applies the frame),
keep `split` frameless (so split stays MP — needed by L2). Rationale given: telescoping already
frame-conjugates the product side via P0/QL; the reading side must be frame-conjugated to match; and
deepestPoint_frame is a GL unit (not det-1) so composing it into split would break MP.

MY DOUBT: `readX/Y/Z` are pure COORDINATE reads off `split w` (an index relabel of w). There is no
`paramsSymm w` MATRIX visible at the reading site — the frame `deepestPoint_frame` is a matrix
conjugation on LAYER matrices. For `framedParams(split w) s = P_s · (paramsSymm w)_s · Q_s` to hold,
the gauge blocks `readX/Y/Z(split w)` would have to BE the gauge blocks of the frame-conjugated layer
`P_s · (paramsSymm w)_s · Q_s`. Is that achievable by "applying the frame in framedLayer", given the
reading is coordinate-algebraic and `split` is a bare relabel that does NOT know about the layer
matrices? Or does the round-trip require `split` itself to encode the gauge decode of the
frame-conjugated layers (i.e. the frame must be in the split/decode, contradicting "keep split frameless")?
</task>

<output_contract>
1. VERDICT (one line): is "frame into framedParams's reading, split frameless" SOUND and SUFFICIENT to
   close the cert, or does the frame genuinely need to be in the split/decode (escalate)? Pick one.
2. THE ROUND-TRIP: state precisely what identity must hold to close the cert, and WHERE the frame must
   be applied for it to hold by construction. If "in the reading", give the exact revised `framedLayer`/
   `framedParams` shape (what does the frame multiply, and how does a coordinate read of `split w`
   become a frame-conjugated layer block?). If this is impossible without the frame in split, say so
   and explain the architectural consequence for MP.
3. THE CLOSING LEMMA: the single load-bearing lemma name + statement that bridges
   `framedParams(split w)` and `P_s · (paramsSymm w)_s · Q_s` (or the corrected object). Flag what it
   needs (e.g. a `gaugeDecode round-trip` lemma, or `paramsEquivFlat`/`split` defeq facts).
4. IMPACT on `deepestEPivot_regSlice_fderiv_id` (deriv-fm's open #91): it reads off the SAME
   framedParamsReg. Does putting the frame in the reading change its derivative-at-0 (the frame is
   CONSTANT, evaluated at the fixed deepest point — is it a constant linear pre/post-comp that leaves
   the strict-derivative-at-0 = id, or does it alter it)?
5. CHEAPEST DISCRIMINATING CHECK before I spend implementation effort.
Be concise. Rank by load-bearing-ness. Flag inference vs. fact explicitly.
</output_contract>

<grounding_rules>
You do NOT have the repo. Reason from the objects above as stated. Where you must assume a definitional
fact (e.g. how `split` relates `paramsEquivFlat`/the gauge decode), FLAG it as an assumption I must
verify, and say which file/decl to check. Do not invent Mathlib lemma names without flagging them as
"verify-exists".
</grounding_rules>
