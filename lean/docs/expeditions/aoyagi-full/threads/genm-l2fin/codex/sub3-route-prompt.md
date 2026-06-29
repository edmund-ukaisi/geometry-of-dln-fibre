<task>
Lean 4 + Mathlib v4.29 formalisation. I am closing one `sorry` ("sub-3") in a banked
foundation. I need you to confirm the EXACT instantiation route and flag any step that
is NEW MATH rather than mechanical reindex/block bookkeeping. This is a continuation of
a thread that already banked 8 helpers + the abstract entry-point lemma; my job is the
final instantiation brick.

## The sub-3 target (to close)
```
theorem deepestEFull_sq_sum_psiSplitRawL2_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s, r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : (reindex (rThr) (rThr) (endpointP0 H hL Pf)).toBlocks₁₂ = 0)   -- block-LOWER
    (hQtri : (reindex (pThr) (pThr) (endpointQL H hL Qf)).toBlocks₂₁ = 0)   -- block-UPPER
    (q : DeepestSplit H r (deepestNGauge H r)) :
    (∑ i, (deepestEFull H r hr hL J Pf Qf (psiSplitRawL2 H r hr hL q) i) ^ 2)
      = ∑ i, (deepestEFull H r hr hL J Pf Qf q i) ^ 2
```
The map `psiSplitRawL2 q = psiSplitRawL2Core q` at L=2 (a `dite`). The "joint move"
edits ONLY the last-layer reg block Y (→ l2Y1p) and the last-layer core T (→ l2T1p) of
the gauge; every other read (X, Z, all non-last layers, the core at non-last layers) is
FIXED. I have matrix-level readbacks proving exactly this:
- readX_psiSplitRawL2Core_eq, readZ_psiSplitRawL2Core_eq  (= original, all s)
- readY_psiSplitRawL2Core_of_ne_eq (= original, s ≠ last)
- readY_psiSplitRawL2Core_last_eq (= l2Y1p at last)
- coreRead_psiSplitRawL2Core_of_ne (= original, s ≠ last)
- coreRead_psiSplitRawL2Core_last (= l2T1p at last)
- framedParamsPivot_psiSplitRawL2Core_of_ne (framedParamsPivot ψq s = framedParamsPivot q s, s ≠ last)

## The banked abstract entry point (consume VERBATIM)
```
theorem deepestEFull_sq_sum_eq_of_resid_blocks (H r ...) (J Pf Qf)
    (q₁ q₂ : DeepestSplit ...) (A₁ A₂ : Params H)
    (hframe₁ : ∀ s, framedParamsPivot H r hr hL J Pf Qf q₁ s = Pf s * A₁ s * Qf s)
    (hframe₂ : ∀ s, framedParamsPivot H r hr hL J Pf Qf q₂ s = Pf s * A₂ s * Qf s)
    (hinterface : ∀ s (hs : (s:ℕ)+1 < L), Qf s = 1 ∧ Pf ⟨s+1,_⟩ = 1)
    (hS3b : reindex (rThr) (pThr) (endpointP0 Pf * B * endpointQL Qf) = fromBlocks 1 0 0 0)
    (h11 h12 h21 :  -- the three residual {11,12,21} block equalities:
       (reindex (rThr)(pThr) (endpointP0 Pf * (prod A₁ - B) * endpointQL Qf)).toBlocksᵢⱼ
     = (reindex (rThr)(pThr) (endpointP0 Pf * (prod A₂ - B) * endpointQL Qf)).toBlocksᵢⱼ) :
    (∑ i, (deepestEFull ... q₁ i)^2) = ∑ i, (deepestEFull ... q₂ i)^2
```
It internally does: deepestEFull_sq_sum_eq_blocks (energy = sum of reindexed framed-product
{11,12,21} blocks squared) + framedReindexProd_corner_split (corner-split via the telescope
`endpoint_telescoping_eq`, B-normalized by hS3b) on BOTH q₁,q₂, then h11/h12/h21 close it.

## Banked helper for the geometric content
```
theorem framed_regBlocks_eq_of_mid (a c DP e f DQ : ...) (A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : ...)
    (hA : A₁ = A₂) (hB : B₁ = B₂) (hC : C₁ = C₂) :
    (fromBlocks a 0 c DP * fromBlocks A₁ B₁ C₁ D₁ * fromBlocks e f 0 DQ).toBlocks₁₁ = (… A₂ …).toBlocks₁₁
    ∧ (… {12} …) ∧ (… {21} …)
```
i.e. block-LOWER P (= fromBlocks a 0 c DP) times M times block-UPPER Q (= fromBlocks e f 0 DQ):
the {11,12,21} blocks of P·M·Q depend on M only through M's {11,12,21}. So two middles M₁,M₂
agreeing on {11,12,21} give framed products agreeing on {11,12,21}.

## reindex_mul_fromBlocks (the raw 2-layer block read)
For a 2-layer product reindex eR eC (G0·G1), with eMid the running-width split:
{11} = A0·A1 + Y0·Z1 ; {12} = A0·Y1 + Y0·T1 ; {21} = Z0·A1 + T0·Z1 ; {22} = Z0·Y1 + T0·T1
(A,Y,Z,T = toBlocks 11,12,21,22 of each reindexed layer).

## The math (what I believe; CONFIRM or CORRECT)
For sub-3: instantiate the entry point with q₁ = psiSplitRawL2 q, q₂ = q, A₁ = Aψ, A₂ = Aq
where Aψ/Aq are abstract Params H. The h11/h12/h21 residual block equalities reduce
(reindex additive; the common `-B` term reindexes to `fromBlocks 1 0 0 0` identically on both
sides by hS3b, so it cancels) to: reindex(endpointP0·prod Aψ·endpointQL) and
reindex(endpointP0·prod Aq·endpointQL) agree on {11,12,21}. By the telescope frame
(endpoint_telescoping_eq, from hframeψ/hframeq/hinterface) these equal reindex(prod(framedParamsPivot ψq))
and reindex(prod(framedParamsPivot q)). The {11,12,21} agreement is the E2/leak-kill:
the last-layer move changes the per-layer middle's {12}=Y (→Y1') and {22}=T (→T1') only;
- {11} = A0·A1+Y0·Z1 and {21}=Z0·A1+T0·Z1 are Y1,T1-free ⟹ trivially preserved (X,Z,A,T0 fixed);
- {12} = A0·Y1+Y0·T1 = P01 is preserved by e2_regPreserve (A0·Y1'+Y0·T1' = A0·Y1+Y0·T1 with
  Y1' = Y1 + A0⁻¹·Y0·(T1−T1')).

## My concern / the question
The entry point wants the residual blocks expressed via `framed_regBlocks_eq_of_mid` whose
framing is fromBlocks-LOWER P and fromBlocks-UPPER Q. But in the residual the frame
endpointP0/endpointQL is ALREADY MULTIPLIED IN (it's `reindex(endpointP0·(prodAψ−B)·endpointQL)`),
NOT a separate fromBlocks frame around a bare `reindex(prod Aψ)`. So to apply
framed_regBlocks_eq_of_mid I must FACTOR the reindex of the triple product back into
reindex(endpointP0) · reindex(prod Aψ) · reindex(endpointQL) (via reindex_mul_split), THEN
write reindex(endpointP0) = fromBlocks a 0 c DP (hPtri gives toBlocks₁₂=0) and
reindex(endpointQL) = fromBlocks e f 0 DQ (hQtri gives toBlocks₂₁=0).
</task>

<output_contract>
1. CONFIRM or CORRECT the overall route for sub-3 (q₁/q₂/A₁/A₂ instantiation + the
   reduction of h11/h12/h21 to the {11,12,21} agreement of reindex(prod(framedParamsPivot ψq))
   vs reindex(prod(framedParamsPivot q))).
2. State the EXACT lemma chain to prove `reindex(prod(framedParamsPivot ψq))` agrees with
   `reindex(prod(framedParamsPivot q))` on {11,12,21}. Specifically: should I (a) factor the
   reindexed triple product and apply framed_regBlocks_eq_of_mid with the frames being
   reindex(endpointP0)/reindex(endpointQL), middle = reindex(prod Aψ)/reindex(prod Aq); or
   (b) work directly with reindex(prod(framedParamsPivot ...)) via reindex_mul_fromBlocks at
   L=2 (prod(framedParamsPivot) = framedParamsPivot 0 · framedParamsPivot 1)? Which is fewer casts?
3. For whichever route: enumerate the per-block obligations and which banked readback /
   e2_regPreserve discharges each. Flag explicitly any step that is NEW MATH (a matrix identity
   not reducible to the listed readbacks + e2_regPreserve + reindex_mul_fromBlocks bookkeeping).
4. The hardest cast risk: at L=2, prod(framedParamsPivot) is a 2-factor product over running
   widths H 0, H 1, H 2 with finCongr layer reindexes. The {11,12,21} of the FULL product read
   the SECOND factor's blocks (which carry the last-layer Y/T change). Confirm whether the
   {11},{21} of the full 2-factor product are genuinely Y1,T1-free (they pair first-factor
   {11,21} with second-factor {11} only — i.e. need second factor {11}=X1-block unchanged,
   which holds since readX is fixed), and whether {12} genuinely needs e2_regPreserve.
   Give the explicit block-multiply formula for the full L=2 framed product's {11,12,21}.
Keep it under ~600 words. Mark inference vs. certainty.
</output_contract>

<grounding_rules>
You do not have the repo. Reason from the signatures given. Where you must assume a
Mathlib lemma name, say "assumed name". Distinguish "this is mechanical given X" from
"this requires a new identity". If the route as I described it has a GAP (e.g. the
abstract A₁/A₂ can't be tied back to framedParamsPivot without an extra lemma), say so —
that is the kill-condition I am checking for.
</grounding_rules>
