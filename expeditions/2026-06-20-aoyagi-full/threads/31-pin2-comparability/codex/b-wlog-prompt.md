<task>
Adjudicate, DEFINITIVELY, which of two repair routes for a Lean RLCT formalisation is SOUND and
LESS-Lean, given refined cost info. Concise (<500 words). Reason from the stated structure.
</task>

<context>
Deep-linear-net loss `dlnLoss H B (A) = ‖∏A_s − B‖²_F`, B a rank-r target (H0×H_L). A gauge chart at a
"deepest point" w0 computes the local RLCT. A producer conjunct (b) `∑deepestEFull²(w) = Sreg(w)` needs
a column-pivot split J = B's pivot columns (generically NON-front). Two routes:

A' (pointwise comparability, in-place): restate (b) as `∑deepestEFull² ≍ Sreg`. The formaliser found this
   rests on TWO unbuilt several-hundred-LoC pieces: (1) a corrected Pπ-telescope `prod(framedParamsPivot
   (split w)) = P0·∏A(w)·QL·Pπ` (the clean endpoint_telescoping_eq is INAPPLICABLE — the last-layer frame
   carries a non-trivial column permutation Pπ, refuting the clean telescope), and (2) the FACT2 reindex
   identity `reindex(rThr,pivotThr J)(M·Pπ)=reindex(rThr,rThr)(M)` (only pen-paper verified). Then a
   fixed-map Frobenius comparability assembles (b) GIVEN (1)+(2).

B (front-pivot WLOG): use rlctAt-invariance `rlctAt(dlnLoss H B) = rlctAt(dlnLoss H (B·Π))` where Π is a
   column permutation bringing B's rank-r pivots to FRONT. Then for (B·Π, J'=front): pivotThr J' = rThr,
   no Pπ, the CLEAN telescope applies, and (b) is an EXACT EQUALITY `∑deepestEFull²=Sreg` (no
   comparability, no FACT2, no Pπ-telescope). The headline invokes a FRESH `deepest_gauge_construction`
   for (B·Π, J'=front) and transfers via the rlctAt-invariance.

Verified exactly (sympy): the loss identity `dlnLoss H B (A) = dlnLoss H (B·Π) (τ_Π A)` where
τ_Π: A ↦ (A with last layer ·Π), and τ_Π is a coordinate permutation (|det|=1, measure-preserving).
Rank(B·Π)=rank(B)=r; B·Π has front pivot.
</context>

<questions>
1. Is B SOUND end-to-end? Specifically the rlctAt-invariance: rlctAt is a LOCAL invariant at a point.
   `rlctAt(dlnLoss H B) at w0(B)` vs `rlctAt(dlnLoss H (B·Π)) at w0(B·Π)`. The MP coordinate change τ_Π
   maps params→params with |det|=1. Does τ_Π map w0(B) (deepest point of B) to w0(B·Π) (deepest point of
   B·Π)? i.e. is the deepest-point construction τ_Π-equivariant (deepest(B·Π) = τ_Π(deepest(B)))? If yes,
   the local RLCTs at corresponding points are equal by the MP germ-invariance. If the deepest points
   DON'T correspond under τ_Π, what bridges them? (The headline RLCT is the GLOBAL min over the loss-zero
   set; if τ_Π is a global MP diffeo it maps the whole loss-zero set of B to that of B·Π, so the global
   min RLCT is preserved regardless of which deepest point — confirm this is the clean argument.)
2. Is B now LESS-Lean than A'? A' = the unbuilt Pπ-telescope (several hundred LoC, the clean telescope
   inapplicable) + FACT2 + fixed-map Frobenius. B = the loss-identity lemma (sympy-exact, ~mechanical) +
   |det Π|=1 MP + rlctAt-invariance-under-MP (is THIS banked? `rlctAtOn_comp_homeomorph` / measure-
   preserving comp — likely yes) + a FRESH chart invocation for B·Π (REUSES deepest_gauge_construction,
   no new geometry) + the front-pivot existence `∃Π, (B·Π) front-pivot`. Rank A' vs B by Lean cost.
3. The Π-frame caveat: invoking a FRESH chart for B·Π means Π is NOT absorbed into an existing QL (the
   chart computes its own frames for B·Π). Does this fully AVOID the earlier caveat ("Π must be absorbed
   into QL, QL need not commute with Π")? Confirm or give the precise residual.
</questions>

<output_contract>
1. Q1 SOUND/not + the deepest-point-correspondence resolution (τ_Π-equivariant OR global-loss-zero-set
   argument). 2. Q2 ranked: B vs A' Lean cost, decisive. 3. Q3 caveat fully avoided / residual.
End with: "The sound, less-Lean route is [B / A'] because ___; B's rlctAt-invariance rests on [banked X /
unbuilt Y]." Mark exact vs inference.
</output_contract>
