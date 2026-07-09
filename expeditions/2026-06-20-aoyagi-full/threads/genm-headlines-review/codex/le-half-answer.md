Verdict: I do **not** see the alleged finiteness leak. The extracted `≤` lemma is structurally sound.

**Q3**

**Yes, the `≤` direction is genuinely divergence-only.**

FACT: `rlctAtOn` is defined as a supremum of admissible exponents: exponents `c' : NNReal` for which there exists an open neighborhood `Ω` of the point with `|F|^{-c'} · 1` integrable on `Ω`. See [Rlct.lean](/home/ubuntu/workspace/genm-r1frontcharge-wt/lean/DLNFibre/DLN/RLCT/Foundations/Rlct.lean:138) and [S1Cover.lean](/home/ubuntu/workspace/genm-r1frontcharge-wt/lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean:64).

So to prove

```lean
rlctAtOn F 0 ≤ t
```

it is enough to prove: every admissible `c'` satisfies `(c' : ℝ≥0∞) ≤ t`. That is exactly `rlctAtOn_le_of_adm_le`.

Here `t = ⨅ i, monomialThreshold ...`. If an admissible `c'` had `t < c'`, then `exists_lt_of_ciInf_lt` gives a leaf `i` with

```lean
monomialThreshold_i < c'
```

hence `monomialThreshold_i ≤ c'`. The divergence payload `hge` then says `|F|^{-c'}` is **not** integrable on any open `Ω ∋ 0`, contradicting admissibility. No finiteness estimate is used.

FACT: the extracted proof in [HeadlineGenBounds.lean](/home/ubuntu/workspace/genm-r1frontcharge-wt/lean/DLNFibre/DLN/RLCT/Validate/HeadlineGenBounds.lean:41) is literally the original `≤` branch from [RouteMBridge.lean](/home/ubuntu/workspace/genm-r1frontcharge-wt/lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean:79), minus `hcover.cover_ge_div`.

The finiteness field `cover_le`, measurability of `F`, openness of `U`, and `U ∋ 0` are only used in the reverse direction `t ≤ rlctAtOn F 0`, where one must exhibit integrable neighborhoods below threshold.

Vacuity check:

- Not vacuous from `rlctAtOn`: it is not defined so `rlctAtOn ≤ t` is automatic. It can be `⊤`.
- Not empty-index vacuous: the extracted lemma keeps `[Nonempty ι]`.
- Degenerate caveat: if all thresholds are `⊤`, then `⨅ = ⊤` and the result is the trivial `rlctAtOn F 0 ≤ ⊤`; the divergence premise is then mostly vacuous for finite `c'`. That is a weak degenerate case, not a soundness flaw. Downstream, `routeLayerAtlas_value_eq_lambdaCore` identifies the infimum with a finite intended value under `hpos`.

INFERENCE: downstream `r1_resolution_general_le` is hbox-free provided the accepted achiever-divergence theorem is hbox-free. The visible source path uses `routeMCore_box_diverges_achiever_full'`, `routeM_coverGeDiv_of_boxDiverges`, transport, and threshold valuation; I found no `RouteMBoxThresholdFinite`/`cover_le` dependency in that lane.

**Q4**

**Yes, dropping `[Fintype ι]` is sound for the `≤` branch.**

FACT: Mathlib’s lemma is:

```lean
theorem exists_lt_of_ciInf_lt [Nonempty ι] {f : ι → α}
    (h : iInf f < a) : ∃ i, f i < a
```

at [Indexed.lean](/home/ubuntu/workspace/genm-r1frontcharge-wt/lean/.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean:360). It requires `[Nonempty ι]`, not `[Fintype ι]`.

Dropping `Fintype` does **not** change the meaning of

```lean
⨅ i : ι, monomialThreshold ...
```

Lean’s `⨅` is `iInf`; it is not rewritten into a finite `Finset.univ.inf` just because `[Fintype ι]` exists. For finite `ι`, it is the same object as in the original bridge. For infinite nonempty `ι`, it is the genuine infimum, possibly not attained, and `exists_lt_of_ciInf_lt` is exactly the lemma needed for the non-attained case.

The full equality still needs `[Fintype ι]` because the `≥` branch has the finite sum

```lean
∑ i : ι, ...
```

and finite-sum finiteness. The `≤` branch does not.

So: no hidden finite-cover gate in the extracted upper bound. The only thing to police is the strength/truth of the supplied `hge`; the extraction itself is clean.