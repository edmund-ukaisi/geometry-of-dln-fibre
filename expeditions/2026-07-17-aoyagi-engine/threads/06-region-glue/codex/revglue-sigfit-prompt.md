# Decorrelated review: does a helper's signature exactly discharge a target obligation, and is a consumed hypothesis-tuple neither too strong nor too weak?

You are an independent Lean-4/Mathlib reviewer. I give you exact signatures (verbatim). Judge TYPE-LEVEL fidelity only; do not trust my prose. Answer each question with FIT / MISMATCH (+ the exact discrepancy).

## Q1 — one-line discharge fit

TARGET obligation (I must NOT edit it):

```lean
variable {L : ℕ}   -- file scope
theorem region_glue (M : Fin (L + 1) → ℕ)
    (hbridge : ChartBridge M (resolutionOf M)) (c' : ℝ)
    (hrat : ∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), c' < (e : ℝ) / 2) :
    routeMLayerBoxIntegral M c' 1 < ⊤
```

Proposed HELPER (in the same namespace `DLNFibre.DLN.RLCT.Engine`, both files `open DLNFibre.DLN.RLCT`):

```lean
theorem region_glue_of_chartBridge {L : ℕ} {M : Fin (L + 1) → ℕ} (t : ResolutionTree M)
    (hbridge : ChartBridge M t) (c' : ℝ)
    (hrat : ∀ e ∈ ResolutionTree.terminalExponents t, c' < (e : ℝ) / 2) :
    routeMLayerBoxIntegral M c' 1 < ⊤
```

Proposed discharge body: `region_glue_of_chartBridge (resolutionOf M) hbridge c' hrat`.

Question: with `t := resolutionOf M`, does the helper's hypothesis list and conclusion match `region_glue`'s EXACTLY (so the one-liner elaborates)? Any implicit/explicit binder mismatch, any place where `t` fails to unify with `resolutionOf M` in `hbridge`/`hrat`/conclusion?

## Q2 — consumed per-leaf tuple: not-too-strong, not-too-weak

The per-leaf lemma consumed by the assembly:

```lean
theorem leaf_chart_image_lintegral_lt_top {M : Fin (L + 1) → ℕ} (l : LeafData (L := L) M)
    (c' : ℝ) (hc' : 0 < c')
    (hsrcM : MeasurableSet l.srcBox)
    (hbdd : ∃ R : ℝ, 0 < R ∧ l.srcBox ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R)
    (hdcInj : Function.Injective l.divCoord) (hrcInj : Function.Injective l.resCoord)
    (hdisj : Disjoint (Set.range l.divCoord) (Set.range l.resCoord))
    (hnull : ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn l.chartMap (l.srcBox \ N))
    (hlp : LeafPullback l) (hlj : LeafJacobian l)
    (hdivExp : ∀ k, c' < (l.divExp k : ℝ) / 2)
    (hres : 0 < l.resRank → c' < (l.resRank : ℝ) / 2) :
    ∫⁻ A in l.chartMap '' l.srcBox, ENNReal.ofReal (frobSq (prod M A) ^ (-c')) < ⊤
```

The ChartBridge per-leaf clause it is fed FROM (destructured in order):

```lean
(∀ l ∈ ResolutionTree.leaves t,
  MeasurableSet l.srcBox ∧
    (∃ R : ℝ, 0 < R ∧ l.srcBox ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R) ∧
    Function.Injective l.divCoord ∧ Function.Injective l.resCoord ∧
    Disjoint (Set.range l.divCoord) (Set.range l.resCoord) ∧
    (∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn l.chartMap (l.srcBox \ N)) ∧
    LeafPullback l ∧ LeafJacobian l)
```

`terminalExponents t = (leaves t).flatMap (fun l => (List.finRange l.numDiv).map l.divExp ++ (if 0 < l.resRank then [l.resRank] else []))`.

Questions:
- (a) Are the eight ChartBridge per-leaf conjuncts EXACTLY the eight non-ratio hypotheses of `leaf_chart_image_lintegral_lt_top` (same statement, same order for a plain `obtain ⟨…⟩`)? Any conjunct that is STRONGER in the lemma than the bridge supplies (would make the assembly unable to discharge it), or WEAKER (would be a soundness hole)?
- (b) The two ratio hypotheses `hdivExp`/`hres` are NOT in ChartBridge; the assembly derives them from `hrat` over `terminalExponents t` for a leaf `l ∈ leaves t`. Given the `terminalExponents` definition above, is `l.divExp k` provably a member (via flatMap→append-left→map), and is `l.resRank` provably a member under `0 < l.resRank` (via flatMap→append-right→`if_pos`→singleton)? Any exponent the lemma needs bounded that is NOT in `terminalExponents` (a missed threshold)?

Be terse. For each sub-question: FIT or MISMATCH + one-line reason.
