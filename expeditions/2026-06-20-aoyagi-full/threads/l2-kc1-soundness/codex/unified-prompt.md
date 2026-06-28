<task>
Lean4/Mathlib soundness sketch review. I must strengthen a BANKED existence proof (`deepestPoint_exists`,
"PROVEN 484/484") to emit two boundary-alignment facts, WITHOUT re-opening its soundness-critical
kernel/range/Sigma (":337") decomposition. Verdict needed: is my insertion ADDITIVE (block_elimination
& its :337 decomposition reused VERBATIM) or does it RESTRUCTURE :337 (→ I STOP+report)?

## The construction (source-verified facts)
- `block_elimination B hB : ∃ P Q, IsUnit P ∧ IsUnit Q ∧ P·B·Q = corner` (corner=[I_r|0;0|0]). Its
  proof builds bKer/bRange/bDomQuot/bCoker bases → bDomS/bCodS → Sigma → hSigma (the :337 region) → P,Q.
- `deepestPoint_exists` (r>0, L≥2) calls block_elimination to get P,Q, sets U := P⁻¹·embM (a×r),
  V := projM·Q⁻¹ (r×b), notes B=U·V, and builds the deepest point as `wLayers H r U V`:
    layer0 = U·projM (a×H₁),  last layer = embM·V (H_{L-1}×b),  interiors = corM.
- KEY FACT (verified): `wLayers H r U V`, `prod_wLayers_ge2` (prod = U·V = B), and the rank/shape parts
  of `IsDeepLayers` are proved for ARBITRARY U,V with B=U·V and rank U = rank V = r. They do NOT depend
  on U,V coming from block_elimination. block_elimination is used ONLY to PRODUCE one factorization.

## What KC1+KC2 need (2 new IsDeepLayers conjuncts, both statements about wLayers' boundary entries)
- KC1: layer0's leading r×r block invertible. layer0 = U·projM, so its top-left r×r = top-r-rows of U.
  ⟺ U's top r rows independent.
- KC2: last layer's top-r-rows' front r columns a pivot set. last layer = embM·V, so ⟺ V's front r
  columns independent.

## My proposed insertion (the sketch to vet)
Because wLayers is already U,V-parametric, I do NOT touch block_elimination or :337. Instead:
(1) Prove an EXISTENCE lemma: for B rank r, ∃ U (a×r) V (r×b) with B=U·V, rank U=rank V=r, AND U's top r
    rows independent AND V's front r cols independent — PROVIDED B is "boundary-aligned" (a row+column
    permutation WLOG: permute B's output rows so col(B) is in general position vs the first r coords, and
    B's input cols similarly). This is a NEW factorization-existence lemma, NOT block_elimination.
(2) Feed that aligned (U,V) into `deepestPoint_exists` (which already accepts any U,V via wLayers), and
    add the 2 alignment facts as new ∧-conjuncts of IsDeepLayers (statements about wLayers boundary
    entries — provable directly from "U top rows indep"/"V front cols indep").
(3) The row+column permutation WLOG lives at the HEADLINE (rlct_infimum_rowPerm_eq + the banked
    rlct_infimum_colPerm_eq), reducing general B to a boundary-aligned Bp.

## Questions (answer each crisply)
1. ADDITIVITY: under this plan, is block_elimination / hSigma / the bKer/bDomS/quotKerEquivRange/Sigma
   decomposition TOUCHED at all? My claim: NO — I bypass block_elimination's .choose for the U,V used by
   wLayers, supplying an aligned factorization from a SEPARATE existence lemma; block_elimination is
   reused verbatim only where the OLD deepestPoint_exists still needs it (or dropped if the aligned
   factorization subsumes it). Confirm or correct.
2. ALIGNED-FACTORIZATION EXISTENCE: for B rank r with col(B) in general position vs first r coords (and
   row(B) similarly) — i.e. after the row+col WLOG — does an aligned factorization B=U·V (U top-r rows
   indep, V front-r cols indep) always exist? Give the construction (e.g. U = first r cols of a chosen
   basis matrix of col(B) with invertible leading minor; V = the matching coords). Is "general position"
   exactly what the row+col permutation achieves?
3. IsDeepLayers PRESERVATION: the existing conjuncts are (fibre membership: prod=B; per-layer rank r;
   interior=corM; layer0 last-cols-zero; last-layer last-rows-zero). Do these ALL still hold for the
   aligned (U,V)? My claim: YES — they hold for any U,V with B=U·V rank r (the zero-shapes come from
   projM/embM, B-independent; rank from rank U/V; interior corM is U,V-independent). Confirm.
4. The 2 NEW conjuncts (U top-r-rows indep ⟺ layer0 leading block invertible; V front-r-cols indep ⟺
   last-layer front-cols pivot): are these STRICTLY ADDITIVE ∧-clauses (provable from the aligned
   factorization's properties), introducing no obligation on the OTHER conjuncts? Confirm.
5. VERDICT: ADDITIVE (no :337 rewrite) or RESTRUCTURING? If you see a place where supplying the aligned
   U,V forces re-proving hSigma or the decomposition, name it precisely — that's my STOP trigger.
</task>

<output_contract>
Five numbered answers, crisp. Each a yes/no + one-line justification. End with a one-word VERDICT:
ADDITIVE or RESTRUCTURING, and if RESTRUCTURING, the exact lemma that breaks.
</output_contract>

<grounding_rules>
Distinguish what you can VERIFY from the facts I gave vs what you INFER. If a claim of mine ("wLayers is
U,V-parametric", "zero-shapes are B-independent") would need checking the actual Lean to confirm, say so
and state the conditional. Do not invent Mathlib lemma names.
</grounding_rules>
