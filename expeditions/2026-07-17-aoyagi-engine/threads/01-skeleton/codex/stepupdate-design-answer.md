## 1. Output type

Rank: **(i) ≫ (ii) ≫ (iii)**.

```lean
structure RootLedger where
  numDiv   : ℕ
  divExp   : Fin numDiv → ℕ
  divTilde : Fin numDiv → ℕ
  cleared  : ℕ
```

- **(i) Core ledger — recommended.** `rootLedger child = stepUpdate ...` is rfl-class if the child root is populated directly from the returned ledger. Re-indexing is confined to `stepUpdate`, principally when appending a divisor.
- **(ii) Core plus support.** Technically rfl-class if the exact computed support term is stored in the child. But independently constructed children require lifting every `Fin numDiv` inside every `Finset`; this is the named balloon.
- **(iii) Full `StepData`.** Only rfl-class when the exact returned `StepData` is installed as a branch root. It is not a natural root type because leaves are not `StepData`. It also forces re-indexing of `bExp`, reconstruction of `bChain`, support, and unrelated residual-state fields.

There is an immediate carrier issue: `LeafData` has no `divTilde`, and its cleared value is currently synthesized as zero. An honest `rootLedger : ResolutionTree M → RootLedger` therefore requires adding the ledger—or at least `divTilde` and `cleared`—to `LeafData`. The cleanest definitional shape is for both `StepData` and `LeafData` to contain a `ledger : RootLedger` field. Flattened fields can probably remain rfl-class through structure eta, but literal elaboration needs a build check.

## 2. Determinism

Use an **explicit typed transition choice**, not a canonical search.

A canonical “first eligible divisor” silently changes the mathematics unless uniqueness has already been proved. `Classical.choose` would also obstruct computation of hand-written witnesses.

Illustrative shape:

```lean
structure Case11Choice (n : StepData M) (σ : ChartSubst M) where
  mergeIdx : Fin n.numDiv
  eligible :
    n.divTilde mergeIdx = n.cleared + σ.runLen
```

Package this into a case-indexed transition descriptor carried by an edge:

```lean
StepSubst (n : StepData M) (c : StepCase)
```

with `Case11Choice` only in `.case11`. Then retain the three-argument form:

```lean
stepUpdate (n : StepData M) (c : StepCase) (σ : StepSubst n c)
```

This is total on well-typed transitions and remains rfl-class. A plain `ℕ` field in the current nondependent `ChartSubst M` would require an invalid-index fallback and is not recommended.

For case 2, the new shared divisor should be definitionally **appended**, with index `Fin.last n.numDiv`; no target choice is needed. Likewise for the case-1(2) new divisor. If “shared” means a selectable generator subset, that needs a separate `sharedBy : Finset (Fin n.numGen)` field—but that belongs to the postponed support rung.

One further gap: the pasted rules do not determine case-1(2)’s new `divExp`/`divTilde`, or clearly state case 2’s new `divTilde`/`cleared`. A faithful total implementation needs those formulas or additional genuine chart-choice fields.

## 3. Support propagation

**STOP-AND-SURFACE on support. Proceed with the core ledger only.**

With the current carrier, adding a divisor changes `Fin numDiv`, so every stored support set must be transported through an embedding before adding the new index. Exact construction can make the final equality `rfl`, but that only hides the bookkeeping inside `stepUpdate`; it does not provide a simple or independently checkable semantic relation.

A future natural redesign is:

```lean
genDivExp : Fin numGen → Fin numDiv → ℕ
```

with `support` derived as the nonzero locus. Then support should not also be stored. That can become rfl-class, but it is a carrier redesign and should be a later rung, not smuggled into rung 1.

## 3b. Honest minimal rung 1

Use only `RootLedger` and:

```lean
def StepRel (n : StepData M) (e : Edge M n) : Prop :=
  rootLedger e.child = stepUpdate n e.case e.subst
```

Case 1(1) preserves `numDiv`, updates exactly `mergeIdx`, and changes its `divTilde` to `cleared`. Cases 1(2) and 2 append exactly one divisor.

This is faithful for the exponent/clearing ledger, though deliberately not for support or layer advancement. It:

- permits a closed hand-built `(2,2,4)` witness to reduce to finite arithmetic;
- rejects any extra or missing divisor immediately through `numDiv` equality.

## 4. Rfl-class discharge

For construction-produced children, target literal `rfl`.

For an independently hand-written closed witness:

- `rfl` works only if its functions normalize to exactly the same terms as `stepUpdate`;
- otherwise expect `simp [rootLedger, stepUpdate, witnessDefs]` followed by `decide`;
- deriving computable `DecidableEq` for the dependent ledger/function fields at v4.29 should be **verified**. A robust fallback is extensionality followed by finite case splitting.

Avoid `Classical.choose`, since it prevents reduction by `decide`.

For `Fin`:

- Do not write `0 : Fin n` when `n` is symbolic without a positivity witness.
- For closed indices prefer `⟨0, by decide⟩`.
- Append old entries by testing `i.val < oldNumDiv`; use the final case for the new entry. This avoids delicate dependent motives.
- `Fin.castSucc`/`Fin.last` are the expected conveniences, but exact v4.29 names should be **verified**.

## 5. Dummy-divisor rejection

Use case 1(1), because its update preserves `numDiv`. Give the child one additional divisor:

```lean
def badTree : ResolutionTree M :=
  .branch parent [badEdge]   -- badEdge.child has numDiv = parent.numDiv + 1

theorem badEdge_not_stepRel : ¬ StepRel parent badEdge := by
  intro h
  have hnum := congrArg RootLedger.numDiv h
  simp [StepRel, rootLedger, stepUpdate, badEdge, badChild] at hnum
```

After unfolding, `hnum` says `parent.numDiv + 1 = parent.numDiv`. The missing-divisor version is identical, using an appending case whose child fails to append.