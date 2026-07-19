Verdict: the stated theorem is false without a positivity hypothesis, so no invariant can satisfy the requested contract as written.

For `L = 2`, take `M = ![2, 2, 0]`. Every admissible profile is `(t,0)` and
`Mval M (t,0) = (2-t)^2`, so uniquely `tStar M = (2,0)`. The tree creates `(0,0)` and `(1,1)` in layer `0`, then the zero rollover threshold at layer `1` forces immediate rollover. Thus `(2,0)` never appears. Notice `flatDim M = 4`, so `0 < flatDim M` is not sufficient.

Add, for example,

```lean
(hpos : 0 < widthMinUpto M L)
```

equivalently all widths are positive. The certificate’s battery used positive widths only.

## 1. Invariant

The clean invariant is a three-phase disjunction. It does not name the birth layer.

```lean
def BeforeBirth (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ)
    (s : ConState L) : Prop :=
  ∃ hm : s.layer < L,
    (∀ i : Fin L, i.val < s.layer →
      a i = runMinWidth M i) ∧
    s.cleared ≤ a ⟨s.layer, hm⟩ ∧
    (∀ q : ℕ, q < s.cleared →
      ∃ k : Fin s.numDiv, s.divTilde k = q)

def AfterBirth (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ)
    (s : ConState L) : Prop :=
  ∃ hm : s.layer < L,
    -- Every remaining target coordinate is strictly below its envelope.
    (∀ i : Fin L, s.layer ≤ i.val →
      a i < runMinWidth M i) ∧
    -- Every low level that must protect the anchor is occupied.
    (∀ q : ℕ, q ≤ a ⟨s.layer, hm⟩ →
      ∃ k : Fin s.numDiv, s.divTilde k = q) ∧
    ∃ A : Fin s.numDiv,
      (∀ i : Fin L, i.val < s.layer →
        s.divProfile A i = a i) ∧
      (∀ i : Fin L, s.layer ≤ i.val →
        s.divProfile A i = s.divTilde A) ∧
      a ⟨s.layer, hm⟩ ≤ s.divTilde A ∧
      s.divTilde A < widthMinUpto M s.layer ∧
      (s.divTilde A = a ⟨s.layer, hm⟩ ∨
        s.cleared ≤ a ⟨s.layer, hm⟩)

def RealizationDone (a : Fin L → ℕ) (s : ConState L) : Prop :=
  s.layer = L ∧
    ∃ A : Fin s.numDiv,
      s.divProfile A = a ∧ s.divTilde A = 0

def RealizeInv (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ)
    (s : ConState L) : Prop :=
  OracleInv M s ∧ NumDivInv M s ∧
    (BeforeBirth M a s ∨ AfterBirth M a s ∨ RealizationDone a s)
```

Why these clauses are the right ones:

- `conRoot` satisfies `BeforeBirth`: the prefix and `q < 0` clauses are vacuous.
- `q < cleared` records the levels already created before birth. A case-1(2) or case-2 append creates level `cleared`, so it extends this interval.
- A case-2 at `cleared = a(layer)` changes `BeforeBirth` into `AfterBirth`; its new divisor has the envelope head and tail `a(layer)`.
- The anchor status
  ```lean
  a_m ≤ τ ∧ τ < widthMinUpto M m ∧ (τ = a_m ∨ J ≤ a_m)
  ```
  is the missing strengthening of the proposed interval invariant.
- At rollover, `a_m < widthMinUpto M (m+1) ≤ J`. Hence the `J ≤ a_m` alternative is impossible, forcing `τ = a_m`. This supplies the newly exposed head coordinate.
- At `layer = L`, the first two phases are impossible, so `RealizeInv` yields `RealizationDone`.

The needed arithmetic helper should be isolated:

```lean
lemma clearable_suffix_lt_runMinWidth
    (ha : a ∈ Adm M) (hc : Clearable M a)
    (hpos : 0 < widthMinUpto M L)
    {b : Fin L} (hb : a b < runMinWidth M b) :
    ∀ i : Fin L, b ≤ i → a i < runMinWidth M i
```

It follows by taking the first later coordinate where equality with the envelope reappears and then the first subsequent strict departure. `Clearable` would force the earlier non-envelope coordinate to equal its envelope.

This design verifies the user’s rollover diagnosis: head equality is trivial through all non-rollover transitions; rollover is the only transition extending the head range.

## 2. Induction

Use `(conRel_wf M).induction`, exactly as in [`leaves_isFullMono`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/t06-s4/lean/DLNFibre/DLN/RLCT/Engine/EngineConstruction.lean:2461).

A layer/cleared recursion is worse: case-1(1) changes neither field and terminates through `pendingCount`, already encoded in `conRel`.

Factor one navigator lemma:

```lean
theorem exists_steered_child
    (ha : a ∈ Adm M) (hc : Clearable M a) (hpos : 0 < widthMinUpto M L)
    (hinv : RealizeInv M a s)
    {node children hnode hlayer hstep}
    (hoc : conOracle M s =
      ConDecision.step node children hnode hlayer hstep) :
    ∃ c ∈ children, RealizeInv M a c.child
```

Reduce `conOracle` using the same branch equations as
`OracleInv_conOracle_stepChildren`:

- rollover/case-2: choose the singleton child;
- case-1 with target `ℓ`: choose the first child if `a(layer) < ℓ`, otherwise the second;
- `chooseMin = none` is impossible from `hinv.1.slc` and
  `chooserTotalOnChain_of_sameLevel`.

The WF induction applies the IH to `c.child c.hdesc`, then inserts its leaf using `buildTree_step`, `edgesLeaves_eq`, `List.mem_map`, and `List.mem_flatMap`.

At a terminal decision, use `conOracle_terminal_leaf`. `NumDivInv` plus the terminal anchor gives `0 < flatDim M` via `numDiv_le_flatDim_of_inv`; then the already-added `leafOfState_carries` reads the anchor from `t0Indices`.

## 3. Pull-ordering brick

Do not require `A = f`, and do not switch to `f` in general.

- If `f ≠ A`, case-1(1) changes only `f`; retain `A`.
- If `f = A`, the low-level occupancy clause proves the pull happens at exactly `J = a_m`:

  If `J < a_m`, level `J+1` is occupied and lies in `occ`. Therefore the minimum target is `≤ J+1 ≤ a_m`, contradicting that the steered case-1(1) target is `τ > a_m`. Hence `a_m ≤ J`; the anchor status supplies `J ≤ a_m`.

Switching to `f` would require `divProfile A ≤ divProfile f`. `chooseMin_spec` gives only the reverse inequality. `SameLevelChainInv` supplies comparability, not equality; `LiveHeadDom` applies only to strict level inequalities; `step1_dominates` also compares different levels. `tStar`’s `Mval` minimality does not supply this state-local order.

Thus the core facts are:

1. the new `LowCover` clause;
2. the minimum property of `occ.min?`;
3. `(chooseMin_spec s target hf).1`.

`step1_dominates` remains important indirectly inside the banked `OracleInv` preservation, but it is not the realization pull lemma.

## 4. Ranked risks

1. Certain: `tStar_realized` is false without `0 < widthMinUpto M L`. This must be repaired first.
2. High: the certificate omits `LowCover`. Reacting to arbitrary oracle emissions without tracking occupied low levels cannot prove that the anchor is pulled at the correct `J`.
3. Medium: `Clearable` must be converted into `clearable_suffix_lt_runMinWidth`; otherwise rollover preservation stalls.
4. Low: dependent child/index plumbing and the `leafOfState` positivity guard. Existing `OracleInv_conOracle_stepChildren`, `NumDivInv_conOracle_stepChildren`, and `leafOfState_carries` already provide the required infrastructure.

Recommendation: land the suffix-envelope lemma, the two phase-maintenance lemmas, `exists_steered_child`, and finally the WF leaf fold. Do not attempt one monolithic proof.