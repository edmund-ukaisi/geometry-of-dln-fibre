1. **Yes, your subtlety is correct.**  
`span {chartDsigAt s t} = ⊤` in `sweepSigmaRing = O(Σ̄^r)` is genuinely false, except degenerate cases. On the rank-`< r` boundary of `Σ̄^r`, every `r × r` minor vanishes, so no `D(chartDsigAt s t)` contains those points. The honest cover is of the open rank-exactly-`r` locus `Σ^r`, not all of `Spec O(Σ̄^r)`.

2. **The bundle earns “locally trivial” only over the rank locus.**  
Mathematically: yes, the data you list is exactly a locally trivial bundle over `Mat^{=r}` / `Σ^r`, provided the base is that open locus.  
Lean-formally: do not state bare local triviality over `Spec(sweepSigmaRing)` or via `span = ⊤` there. That is false. If your `locallyTrivial` predicate’s base is the restricted open locus and accepts a point-set/open-subspace cover, then it is earned. If it requires a unit-ideal affine cover of the base ring, you still need the restricted/localized base ring statement.

3. **Honest name ranking.**

Best:

`…locallyTrivialOnRankLocus…`

Also honest:

`…LocalProductAtlasWithCover…`

Less precise but acceptable if documented:

`…LocalProductAtlas…`

Avoid:

`…locallyTrivial…` bare, unless the name’s namespace/type already makes clear that the base is `Mat^{=r}` and not `Σ̄^r`.

So the maximally honest name is:

`…locallyTrivialOnRankLocus…`

or, if the object is not yet packaged as the library’s actual `locallyTrivial` structure:

`…localProductAtlasWithCoverOnRankLocus…`.

4. **Precise residual to bare scheme-theoretic `locallyTrivial`.**  
You need to move the base from `O(Σ̄^r)` to the open rank-`r` locus and prove the minors cover there:

```lean
⨆ s t, basicOpen (chartDsigAt s t) = rankExactOpen
```

or equivalently after restricting/localizing to `Mat^{=r}`:

```lean
span { image of chartDsigAt s t } = ⊤
```

That statement is true. It is a clean further rung conceptually: the ideal of all `r × r` minors cuts out the complement of the rank-`< r` locus inside the closure. In Lean it may be technically nontrivial because it wants the formal bridge between rank conditions, vanishing ideals/radicals, and opens of `Spec`; but it is not a new mathematical subtlety.