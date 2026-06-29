**Verdict**

(A) is **not** realistically a single bounded module. **Fact from your description:** the worked proofs rely on `decide`-built `Fin N ≃ FlatIdx M` equivalences and explicit coordinate partitions. Uniformizing that at opaque widths is exactly the hard part.

Single most likely blocker: proving that the opaque-width flat coordinate equivalence, shear coordinate layout, and `phiL2`/`coreShear` coordinates all agree definitionally or propositionally enough to recover the peeled rate and box containment. That is not just “construct an equivalence”; it is a uniform indexing API plus many transport lemmas. **Estimate:** likely 1.5k-3k LoC, possibly more if `FlatIdx M`/ambient-dimension arithmetic is not already normalized by local lemmas. **INFERENCE:** Mathlib will not save much here beyond generic `Fin`/`Equiv` plumbing; the main cost is repo-specific coordinate bookkeeping.

(B) is a good one-module bedrock deliverable, not vacuous, if the structure is placed at the right abstraction boundary.

Even though `smearedL2` already takes the loose hypotheses, bundling them as

```lean
SmearedAchieverChart M
```

does real work because it turns a long, fragile per-family application spine into a named residual theorem:

```lean
routeMCore_box_diverges_of_smearedChart
```

That gives you a stable target for arbitrary-width chart construction, matches the existing `NodeAchieverChart M` pattern, makes worked instances reusable as evidence of non-vacuity, and lets the global `hSmeared` branch reduce to exactly one missing object per `M`. The deliverable is mainly architectural, but it advances the leg by closing the M-agnostic assembly and isolating the only remaining geometric construction.

Sharpest verify-first risk: **rank/pivot degeneracy**, especially regimes where the intended `r`-row pivot block cannot be chosen with the required nonzero/invertible pole data.

Most dangerous case: `M0 < r`, if the construction implicitly needs an `r × r` full-rank minor of `P₁ = A0 ∘ top r cols`. Then the rational-pole shear cannot be verified through the same interface. This is **inside `BoundarySmeared` unless your definitions force `r ≤ M0` from `deepRank`/compressed-rank data**. So this is the first regime I would audit.

Lower-risk degeneracies:

- `s = 0`: likely inside `BoundarySmeared` only when `r < M1`. The shear may become trivial, but the chart should still close if the interface permits empty blocks. **INFERENCE.**
- `r = 0`: then `deepRank = 0`; `BoundarySmeared` means `M1 > 0`. The rate/positivity may degenerate because `∑ᵢⱼ((P₁·H̄)ᵢⱼ)²` could be an empty sum unless there is another positive factor. This is a serious edge case if not excluded. **INFERENCE.**

Plan impact: I would choose (B), but define the chart fields so they explicitly expose the nondegeneracy needed for the pole/rate. Then separately audit whether `BoundarySmeared` implies those fields are constructible in all regimes.