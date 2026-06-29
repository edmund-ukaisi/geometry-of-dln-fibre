<task>
Lean 4 / Mathlib formalisation of deep-linear-network RLCT geometry. I am wiring an L=2 diffeo bridge.
Decide ONE precise mathematical question: how to discharge two block-triangularity hypotheses for the
ENDPOINT frames, given the constraints below. This is a pen-and-paper truth-value question, not a Lean
tactics question.

## Objects (matrices over ℝ; "corner split" = split each square index Fin n into Fin r ⊕ Fin (n−r))
- `deepestPoint s` (s = layer 0 or 1, L=2): the deepest critical point's layer matrices, each rank r.
  Layer 0: its last (H1 − r) COLUMNS vanish (tail-cols-zero). Layer 1 (=last): its last (H1 − r) ROWS
  vanish (tail-rows-zero).
- Producer frames `Pf s, Qf s` (per-layer change of basis, units) from a GENERIC rank-normal-form
  routine. KNOWN facts about them (the "bundle"):
  - hNF: `Pf s · deepestPoint s · Qf s = corM` where corM = diag(I_r, 0) (the block-normal corner).
  - boundary triviality: `Qf 0 = I` (layer 0 right-frame is identity), `Pf 1 = I` (layer 1 left-frame
    identity).
  - hcorner: reindex( deepestPoint 1 · Qf 1 ) (corner split) = fromBlocks I_r 0 0 0.
  - The deepest point's layer-0 leading r×r block (top-left submatrix) is INVERTIBLE
    (`deepestPoint_leadingBlock_isUnit`).
  - CRUCIAL: the producer's `Pf 0` is a GENERIC basis-change unit — it has NO block-triangular
    guarantee in general (a rank-r tail-cols-zero matrix can carry its rank in lower rows, so the
    left-normalizer that diagonalizes it need not be block-lower).
- `endpointP0 = Pf 0` (the left endpoint frame), `endpointQL = Qf 1` (the right endpoint frame).
- `Score(w) := frobSq of the (2,2)-Schur complement of reindex( endpointP0 · (prod(w) − B) · endpointQL )`
  in the corner split, where `prod(w)` is the layer-product at chart point w, B the target. So Score is
  DEFINED using endpointP0 = Pf 0 and endpointQL = Qf 1 explicitly.

## The two hypotheses I must discharge (the diffeo bridge `_impl` requires them):
- hPtri: reindex(endpointP0) (corner split, both sides).toBlocks₁₂ = 0   [Pf 0 is block-LOWER]
- hQtri: reindex(endpointQL) (corner split, both sides).toBlocks₂₁ = 0   [Qf 1 is block-UPPER]

A banked exact-rational check established: the diffeo bridge's reg-energy preservation (E2) is FALSE at
general endpoint frames and TRUE iff endpointP0 block-lower AND endpointQL block-upper (the moved core
(2,2) block leaks into the reg-read blocks otherwise). And a decorrelated certificate ("genm-frameadj")
concluded: "thread hNF/hcorner — it's exactly what makes the reads-only object EQUAL the endpoint
conjugation; the {12}-leak vanishes at p11 = I_r ALONE (the corner's leading-r columns identity), with
the off-diagonal d' free." There are explicit BANKED block-triangular normalizers available:
`blockLower_left_normalizer A11 A21 [Invertible A11]` produces P = [[A11⁻¹,0],[−A21·A11⁻¹, I]] with
P·[[A11,0],[A21,0]] = [[I,0],[0,0]], block-lower; and a dual `blockUpper_right_normalizer`.

## The tension to resolve
hPtri/hQtri are NOT TRUE for the producer's generic Pf 0 / Qf 1 as-is. Two candidate resolutions:
(a) "reads-match": keep Score keyed to the producer Pf 0 / Qf 1, and prove hPtri/hQtri-equivalent facts
    hold because hNF/hcorner force the reads to match a triangular frame's reads (i.e. the producer
    frame, while not literally block-triangular, has the SAME corner-split reads as some triangular
    frame on the relevant product). PROBLEM: hPtri/hQtri are literal statements about Pf 0 / Qf 1
    themselves (toBlocks₁₂ = 0), not about reads of a product — so this seems to require Pf 0 LITERALLY
    block-lower, which is false.
(b) "re-key Score": do NOT pass the producer Pf 0 / Qf 1 to the bridge. Instead CONSTRUCT triangular
    endpoint frames P0' (block-lower, via blockLower_left_normalizer on the leading block) and Q1'
    (block-upper) and pass THOSE. Then hPtri/hQtri hold by construction. PROBLEM: Score is defined via
    endpointP0 = Pf 0; substituting P0' changes Score's value unless Score(via P0',Q1') = Score(via
    Pf 0, Qf 1). Need: are these two Scores EQUAL? (Both compute the (2,2)-Schur of a conjugated
    residual; conjugating by different units changes the (2,2)-Schur in general, BUT both P0/Pf0 carry
    the SAME deepest layer to the SAME corner, so the residual reindex may coincide on the relevant
    blocks.)
</task>

<output_contract>
1. VERDICT: which resolution (a) or (b) — or a third I missed — is the mathematically correct/feasible
   one. One paragraph.
2. If (b): state PRECISELY the equality that must hold (Score-via-triangular = Score-via-producer) and
   whether it is TRUE, with the 1-2 line reason (use hNF + the fact that both frames send deepestPoint·
   to the same corner). If it can FAIL, give the obstruction.
3. The MINIMAL set of facts needed to discharge hPtri AND hQtri AND the Score-equality (name them in
   terms of the bundle facts above: hNF / hcorner / leadingBlock-invertible / boundary-triviality /
   the normalizers).
4. A 3-5 step proof sketch (pen-and-paper, block algebra) for the chosen resolution.
5. Any landmine: a place where the corner-split reindex, the +1 in the Schur (toBlocks₁₁ + 1)⁻¹, or the
   "− B" shift breaks the argument.
</output_contract>

<grounding_rules>
This is a pure block-matrix-algebra adjudication. State each claim as either (i) a block-algebra
identity you can justify in one line, or (ii) an inference/assumption you cannot verify from what I gave.
Flag (ii) explicitly. Do not invent Lean lemma names. If resolution (a) is literally impossible (because
hPtri is a statement about Pf 0 itself), say so plainly rather than hedging.
</grounding_rules>
