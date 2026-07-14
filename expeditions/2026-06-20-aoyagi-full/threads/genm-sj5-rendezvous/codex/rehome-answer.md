## 1. FRAME-STRIP SOUNDNESS

Sound, given the stated bodies. Ordinary hypotheses cannot influence the proof invisibly if neither the proof term nor any called theorem uses them.

Double-check only:

- The declared types of `Zf`, `hZfMeas`, `hpiv`, and the conclusion do not mention `m` or `e'`.
- No stripped binder is an instance binder used implicitly.
- Implicit arguments to the two `pivotDomLHS_lt_top_of_*` calls do not infer data from the stripped frame.

Adding `hu : 1 ≤ u` and replacing the `u = 0` split by the forward proof is sound. All callers must now provide `hu`.

## 2. RE-HOME ARCHITECTURE

R is a valid downstream sink. There is no cycle in:

`PivotFin + GoodConnector + WaistConnector → R → HeadlineL1Mint`.

Two gaps need checking:

- R must itself import whatever defines `DecoratedDescent` and `decoratedBaseHyp_faithful`; imports of `HeadlineL1Mint` are not visible while compiling R. Alternatively, export only `decoratedStepHyp_dispatch_R` from R and assemble `DecoratedDescent` in the headline.
- The plan does not explain how R supplies WaistConnector’s `hred`. This is a real gap unless a retained sorry-free theorem provides it.

Also unverified from the supplied information: the construction of `hsector`, and that `pivotPeel_domination` matches the exact old `headSplit_pivotDom` conclusion after unfolding/rewrite.

For the listed deletions, the described dependency slice is safe after refactoring `(d)`. Repository-wide safety still requires a reference search/build.

Ranking:

1. Parameterize `deeperFlag_spineToCore` over the head-split domination fact and pass that parameter through `deeperFlag_shell_le`.
2. Copy the ~120 lines into R.

Parameterization preserves the upstream combinatorial proof, avoids duplication, and introduces no import cycle.

## 3. WAIST/(d) KNOT

Endorse option (ii): dependency inversion is the clean solution. Prefer a callback specialized to the good-case statement Waist actually needs, capturing the existing `hIH`, rather than a larger global theorem hypothesis.

The callback must operate at the same `L` on

`M ∘ Fin.rev : Fin (L + 1 + 1 + 1) → ℕ`

and use the same `hIH`; there is no induction decrease here. This is nevertheless acyclic because clean `(d)` is proved independently of `(c)`.

After this refactor, the old DecoratedStep `(d)` stub can also be deleted, assuming no remaining references.

## 4. DEGENERATE `hnd`

Sound mathematically.

From `¬ ∀ i, 1 ≤ M i`, obtain an `i` with `M i = 0`. Then:

- If `i = 0`, the head factor in `M 0 * tailInf` is zero.
- If `i ≥ 1`, that coordinate occurs in the tail, so the tail infimum is zero.

Thus no index is missed, including the final coordinate. Since `Fin (L+3)` has a nonempty tail, there is no empty-tail edge case. Consequently `minAdm M = 0`, hence `carrierThreshold M = 0`, and the quantified condition `c' < 0` is impossible.