<task>
Lean 4 + Mathlib, deep-linear-network RLCT formalisation. I need a DIAGNOSIS of the cleanest way to
state + prove "O1" — the per-node step of a recursive cover that proves the binding identity
  rlctAtOn (dlnLoss M 0) deepest = ½·minAdm(M)       [R1 core RLCT identity, the BINDING goal]
for a general dimension vector M : Fin (L+1) → ℕ. I must NOT build a route that duplicates existing
machinery. Help me pick the decomposition.

WHAT EXISTS (committed, green):
1. descentStep (my seam, banked): for a NON-LEAF node, given a RouteMNodeDescent datum,
     rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) (fun _=>0)
   where S.red = schurState M (the Schur-reduced widths, M_0,M_1 each −1), nReg = the regular-block
   count. This composes two banked lemmas: schur_straighten_squeeze_of_data (the squeeze → nReg/2 +
   rlctAtOn(G²)) and ReducedTransport.descent (the det-1 MP reindex rlctAtOn(G²)=rlctAtOn(dlnLoss S.red 0)).
   The datum carries Gne (germ-nonvanishing) which FAILS at degenerate leaves, so the datum is
   inhabitable only at non-leaf nodes.
2. flatCore is the post-blow-up presentation of dlnLoss M 0 (the (2,2,2) anchor: dlnLoss = myF222 ∘ e222,
   and rlctAtOn(dlnLoss H222 0) deepest = rlctAtOn myF222 0, via a measure-preserving transport
   rlctAtOn_dlnLoss222_transport). So at the anchor, rlctAtOn(dlnLoss M 0) deepest = rlctAtOn flatCore (0,0)
   by an MP transport.
3. resolution_value_of_atlas (committed): given IsResolutionAtlas (a 4-conjunct cover obligation: A
   admissible, S surjective/exhaustive, K mult-1, C threshold=½codim), proves the PURE VALUE identity
   ⨅_paths monomialThreshold = ofReal(lambdaCore M) = ½·minAdm. This is the VALUE layer (a ⨅-rearrangement).
4. IsRouteMCover (the COVER layer, #104 still PENDING): the structure whose cover_le/cover_ge_div fields
   bound ∫⁻|F|^{−c'} above/below by the leaf monomial sum, giving rlctAtOn = ⨅ monomialThreshold. The
   abstract reductions routeM_coverLe_of_finiteness / routeM_coverGeDiv_of_boxDiverges exist.
5. lambdaCore M = ½·minAdm definitionally; minAdm = (Adm M).inf' Mval.
6. The recursion measure: chainRel (ΣM strict decrease), chainRel_wf; ChainDimSplit.redM_chainRel
   (schurState descends). WellFounded.fix is available.
7. The chain (2,2,2)→(1,1,2)→(0,0,2)-LEAF terminates (schurState decrements M_0,M_1 until some M_s=0).
   nReg = minAdm(M) − minAdm(schurState M), verified nonneg-integer. lambdaCore(2,2,2)=3/2 = 2/2+1/2+0.

THE TWO CANDIDATE ROUTES for "rlctAtOn(dlnLoss M 0) = ½·minAdm":
- (RECURSION route, O1/O2/O3): iterate descentStep. O1 = per-node: rlctAtOn(dlnLoss M 0) deepest =
  nReg/2 + rlctAtOn(dlnLoss S.red 0) 0 (lift descentStep from flatCore to dlnLoss via the MP transport).
  O2 = WellFounded.fix on chainRel threading O1 to the leaf. O3 = the leaf base (rlctAtOn(dlnLoss leaf)=0
  / the degenerate Morse value) + summing the nReg/2's = ½·minAdm (the telescoping
  Σ nReg_k/2 = ½·Σ(minAdm_k − minAdm_{k+1}) = ½·minAdm since the leaf minAdm=0).
- (ATLAS route): build IsResolutionAtlas + IsRouteMCover directly (the chart-tree cover), get
  ⨅ monomialThreshold = ½·minAdm from resolution_value_of_atlas, and rlctAtOn = ⨅ from the cover.

QUESTION I'm resolving: are these DUPLICATE routes, or COMPLEMENTARY? My read: the RECURSION route
(descentStep) is the cleaner proof of the COVER (it avoids the global chart-tree (S)-surjectivity
obligation — the recursion's well-foundedness replaces exhaustiveness). But I worry it (a) duplicates
the atlas value-layer, or (b) still needs the per-node flatCore presentation (the blow-up CoV) which is
the same plumbing the atlas needs. Which route minimizes NEW work given what's committed?
</task>

<output_contract>
Terse, these sections:

1. ROUTE VERDICT (1 para): RECURSION (descentStep) vs ATLAS — which is the lower-new-work route to
   rlctAtOn(dlnLoss M 0)=½·minAdm, given the committed machinery? Are they duplicate or complementary
   (e.g. recursion proves the cover, atlas proves the value, and they meet at ⨅=½·minAdm)? If recursion
   subsumes the atlas's (S)-surjectivity, say so (that's a big win — (S) is the open hard obligation).

2. O1 STATEMENT (the cleanest Lean shape): exactly what should O1 say? Candidates:
   (a) rlctAtOn (dlnLoss M 0) deepest = nReg/2 + rlctAtOn (dlnLoss (schurState M).red 0) 0  [per-node, lift descentStep via MP transport]
   (b) a cover_le/cover_ge_div per-node inequality feeding IsRouteMCover recursively
   (c) something else.
   Which, and what HYPOTHESES (the RouteMNodeDescent datum? a non-leaf hyp? the MP transport dlnLoss=flatCore∘e)?
   Flag if O1 needs a per-node "dlnLoss M 0 = flatCore ∘ (blow-up chart)" presentation as a hypothesis
   (the producer obligation) vs whether it's derivable.

3. THE TELESCOPE (O3): is Σ_k nReg_k/2 = ½·minAdm(M) a clean telescope given nReg_k = minAdm(M_k) −
   minAdm(schurState M_k) and the leaf minAdm=0? Any subtlety (the leaf's own rlctAtOn=0 vs ⊤; whether
   the degenerate-boundary lemma #70 "rlctAt(deepest)=nReg/2 at a leaf" is the base case)?

4. THE TRAP (1 para): the biggest risk in the recursion route. Candidates: the per-node MP transport
   (dlnLoss=flatCore∘chart) is itself the formaliser-weeks plumbing (so O1 doesn't save work); OR the
   leaf base case rlctAtOn=⊤ (degenerate) breaks the telescope; OR a mismatch between "deepest point of
   dlnLoss M 0" and "(0,0) the flatCore anchor". Which is the real risk + how to de-risk it cheaply
   (numeric or a small lemma) BEFORE the formaliser-weeks grind.
</output_contract>

<grounding_rules>
You cannot see my files — flag inference vs the facts I gave. If the recursion route does NOT subsume
the atlas (S)-obligation (i.e. it still needs global exhaustiveness somewhere), SAY SO — that would
mean O1 doesn't buy the win I hope for. Do not invent Mathlib lemma names; describe the shape.
</grounding_rules>
