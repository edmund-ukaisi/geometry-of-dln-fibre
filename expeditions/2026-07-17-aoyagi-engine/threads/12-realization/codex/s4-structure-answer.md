The target is not provable as stated: it needs positive widths. For example, with `L = 2`, `M = (1,1,0)`, the unique minimizer is `tStar M = (1,0)`, but the oracle creates only `(0,0)` before the zero-width rollover. A natural repair is

```lean
(hM : ∀ i, 0 < M i)
```

equivalently `0 < widthMinUpto M L`.

1. Top-level existence proof

Use well-founded induction on the state:

```lean
(conRel_wf M).induction
```

with induction property

```lean
OracleInv M s → SteerInv M a s →
  ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) s),
    ∃ k, l.divProfile k = a
```

where `a := tStar M`. Do not induct on the layer: `case11` leaves both `layer` and `cleared` unchanged. Fuel would only repackage `conRel`.

Factor one new generic lemma:

```lean
childLeaves_subset
  (hoc : conOracle M s = .step node children ...)
  (hc : c ∈ children) :
  leaves (buildTree M (conOracle M) c.child) ⊆
    leaves (buildTree M (conOracle M) s)
```

Its proof reverses the branch part of `leaves_isFullMono`, using `buildTree_step`, `edgesLeaves_eq`, `List.mem_flatMap`, and `List.mem_map`; see [EngineConstruction.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/t01-r2/lean/DLNFibre/DLN/RLCT/Engine/EngineConstruction.lean:440) and [the WF template](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/t01-r2/lean/DLNFibre/DLN/RLCT/Engine/EngineConstruction.lean:2461).

Invert `conOracle` inline:

- rollover/case-2: take the unique child;
- case-1 target `ℓ`: take child 1 iff `ℓ > a ⟨s.layer,…⟩`, otherwise child 2;
- `chooseMin = none`: contradict `chooserTotalOnChain_of_sameLevel s inv.slc`;
- terminal: discharge from the terminal phase of `SteerInv`.

The selected children really are present in `case1Decision` in that order. However, child 1 is the exponent-bumped record, not literally `s.stepCase11 f`; its profile fields are the same. See [case1Decision](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/t01-r2/lean/DLNFibre/DLN/RLCT/Engine/EngineConstruction.lean:2028).

2. Anchor invariant

A single assertion

```lean
∃ k, divProfile k = truncatedTarget ∧ divTilde k = ...
```

is too weak: it does not force the anchor to be pulled when `cleared = a^S`. Use a three-phase predicate.

Let

```lean
cut a S q p := if p.val < S then a p else q
```

with Lean’s `S = s.layer`.

- `pre`:

  - `S < L`;
  - `a p = runMinWidth M p` for `p.val < S`;
  - `s.cleared ≤ a ⟨S,…⟩`;
  - every level `m < s.cleared` is occupied.

- `anchored`:

  - a birth witness `b ≤ S` with
    `a b < widthMinUpto M (b.val + 1)`;
  - full level coverage
    `∀ m ≤ a ⟨S,…⟩, ∃ k, s.divTilde k = m`;
  - an anchor `k` and level `q` with
    `s.divProfile k = cut a S q` and `s.divTilde k = q`;
  - either `q = a S` (“landed”), or
    `S > 0`, `q = a (S-1)`, `a S < q`, and `s.cleared ≤ a S` (“pending”).

- `done`:

  - `L ≤ s.layer`;
  - `∃ k, s.divProfile k = a ∧ s.divTilde k = 0`.

Before the WF proof, establish the profile lemma:

```lean
a ∈ Adm M → Clearable M a →
(∀ i, 0 < M i) →
a b < widthMinUpto M (b+1) →
b ≤ d →
a d < widthMinUpto M (d+1)
```

Otherwise a later equality with the envelope, followed eventually by the last-coordinate descent to zero, contradicts `Clearable`.

Obligations then factor cleanly:

- Base: `conRoot` satisfies `pre`.
- Birth: case-2 at `cleared = a S` appends `cut a S (a S)`; pre-coverage plus the new level gives anchored coverage.
- Case-1(1): if the selected index is not the anchor, transport the anchor unchanged; if it is the anchor, level coverage plus minimality of the occupied target proves `cleared = a S`, hence `setTail` produces `cut a S (a S)`.
- Case-1(2)/case-2: transport the old anchor as `Fin.castSucc k`.
- Rollover: landed becomes the next layer’s pending anchor; a pending anchor cannot roll over because of the strict post-birth width margin.
- Terminal: use `mem_t0Indices`/`List.get_of_mem` to reindex the state anchor into `leafOfState`’s analytic divisor list; see [leafOfState](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/t01-r2/lean/DLNFibre/DLN/RLCT/Engine/EngineConstruction.lean:1754).

3. Pull-ordering brick

No single banked lemma proves “lands exactly at `a^S`”.

- `chooserTotalOnChain_of_sameLevel` only rules out the fallback.
- `chooseMin_spec.1` says the selected index is at the target level.
- `chooseMin_spec.2` says the selected profile is least among that level.
- `step1_dominates` proves a level-`ℓ` profile dominates already-cleared profiles; it does not prove `J = a^S`.
- `LiveHeadDom` is an invariant consumed by `step1_dominates`, not the exact-landing result.

The missing exactness lemma is the level-coverage argument:

```text
if J < a^S, coverage supplies a divisor at level J+1 ≤ a^S;
since target is the least occupied eligible level, target ≤ a^S;
therefore an anchor at target > a^S cannot be selected.
```

Thus when the tracked anchor is selected, `J = a^S`. Tracking its actual `Fin` index avoids proving that it is already Def-4-least: smaller same-level choices take case-1(1), while the anchor remains. Well-founded descent guarantees this cannot continue forever. The banked o4 machinery is still used indirectly through `OracleInv` preservation.

4. Ranked risks

1. Certain: the theorem is false without positive widths. This is the first required repair.
2. High: the cert’s anchor-only invariant omits level coverage and the post-birth strict-width lemma. This is where an implementation following the prose literally will dead-end.
3. Medium: child 1 is exponent-bumped rather than literally `stepCase11`; append transitions also change anchor indices via `Fin.castSucc`.
4. Low: dependent inversion of `conOracle`. Existing proofs such as `OracleInv_conOracle_stepChildren` already provide the exact branch-reduction template.

The `R(a)` child-membership itself is not a serious risk: both case-1 children are literal entries of `case1Decision`’s emitted list.