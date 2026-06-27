<task>
Adjudicate ONE soundness/naming question for a Lean 4 formalisation of Lehalleur–Rimányi Lemma 4.6's
locally-trivial bundle. Be decisive.

SETUP. The bundle is `mult⁻¹(B) → Mat^{=r}` over the rank-EXACTLY-r locus. I have, in Lean, axiom-clean:
- `sweepSigmaRing k d r = O(Σ̄^r)` = coordinate ring of the CLOSURE `Σ̄^r` (= MvPolynomial ⧸
  vanishingIdeal(Σ^r), and vanishingIdeal(Σ^r) cuts the CLOSURE, which includes rank-<r boundary
  points). The base of my charts.
- per-pivot charts `D(chartDsigAt s t)` ⊆ Spec(sweepSigmaRing), localizing elements = classes of the
  (s,t) deep r×r minors `ΔPdeepAt s t`.
- per-pivot trivializations `e_{s,t} : Away(chartDsigAt s t) ≃ₐ[k] SchurLoc ⊗ sweepFibreRing`, all in
  the SAME standard fibre (thread 22).
- the overlap transition cocycle over sweepSigmaRing (banked awayOverlapTransition; laws inherited).
- the intertwining: the transition between trivializations factors through the base gauges (e_β cancels).
- THE COVER I proved (point-set): every point x of `sweepSigma` (= the rank-=r locus Σ^r, a SET of
  closed points) has SOME (s,t) with `eval x (ΔPdeepAt s t)` a unit (≠0). Via
  exists_invertible_minor_of_rank applied to mult at a rank-=r point.

THE SUBTLETY I FOUND. The scheme-theoretic cover `span {chartDsigAt s t} = ⊤` in sweepSigmaRing
(equiv. `⨆ basicOpen(chartDsigAt s t) = ⊤` = the principal opens cover ALL of Spec(sweepSigmaRing))
is FALSE: sweepSigmaRing = O(Σ̄^r) is the ring of the CLOSURE, and at a rank-<r boundary point of the
closure, ALL r×r minors vanish — so the chartDsigAt do NOT cover those boundary points. The charts
cover exactly the OPEN rank-=r locus Σ^r ⊂ Σ̄^r, not the closure. My point-set cover (over Σ^r) is
correct and honest; the span=⊤ over O(Σ̄^r) is genuinely false.
</task>

<output_contract>
Answer terse, decisively:

1. IS MY SUBTLETY CORRECT? Confirm or refute: is `span {chartDsigAt} = ⊤` over O(Σ̄^r) genuinely
   FALSE (because the closure has rank-<r points where all minors vanish), so the honest cover is the
   point-set cover of the OPEN rank-=r locus, NOT a unit-ideal statement over the closure's ring?

2. DOES THE BUNDLE EARN `locallyTrivial`? Given that the bundle is OVER the open rank-=r locus Mat^{=r}
   (an open subscheme of Σ̄^r), and I have: point-set cover of Σ^r + per-pivot trivializations +
   coherent transition cocycle + intertwining — is this GENUINELY a locally trivial bundle over the
   rank-=r locus? Or is there still a gap (e.g. I'd need to localize sweepSigmaRing at the rank-=r
   open, or prove span=⊤ over O(Mat^{=r}) which is a localization where it WOULD hold)?

3. THE HONEST HEADLINE NAME. Given all the above, what should I name the assembled Lean object? Rank
   these by honesty:
   (a) `…locallyTrivial…` bare — only if genuinely earned;
   (b) `…locallyTrivialOnRankLocus…` / `…LocalProductAtlasWithCover…` — atlas + point-set cover over
       the rank-=r locus, NOT claiming span=⊤ over the closure;
   (c) `…LocalProductAtlas…` — atlas + coherent transitions, cover disclaimed.
   Which is the maximally-honest name I can use WITHOUT overclaiming, given I have the point-set cover
   but NOT span=⊤ over the closure ring (which is false anyway)?

4. WHAT IS THE PRECISE RESIDUAL to a bare scheme-theoretic `locallyTrivial`? Is it "localize
   sweepSigmaRing at the rank-=r open and prove span=⊤ there" (a Nullstellensatz argument over the
   OPEN, where it holds)? Estimate whether that's a clean further rung or itself subtle.
</output_contract>

<grounding_rules>
You cannot see the files; flag inference vs derivation. The key question is the closure-vs-open
subtlety and whether my point-set cover honestly supports a `locallyTrivial`-family name. If a bare
`locallyTrivial` over the closure's ring is genuinely false/unearned, say so plainly — I will name it
the honest restricted thing rather than overclaim.
</grounding_rules>
