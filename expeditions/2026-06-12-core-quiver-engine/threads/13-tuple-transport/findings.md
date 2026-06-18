---
title: "Thread 13 — Tuple transport of the barcode existence (rung 4 completion)"
status: open
topics: [formalisation, gabriel, barcode, tuple, transport, prop-3.1b, uniqueness]
created: "2026-06-13"
updated: "2026-06-13"
---

# Thread 13 — carrying the abstract-chain barcode down to concrete `Tuple`s

**Type:** formalisation (tide). **Environment:** MAIN checkout (isolation was flaky; landed here as
prior teammates did). Changes left **UNSTAGED/untracked** for the controller to commit — new module
only, aggregator untouched.

**Module:** `lean/DLNFibre/Core/Gabriel.lean` (namespace `DLNFibre.Core`, network-free, `Field k`).
**Build:** `lake build DLNFibre.Core.Gabriel` green (1795 jobs). `scripts/sorries`: **0 sorry / 0
#exit / 0 native_decide / 0 axiom**. `#print axioms` on the headlines → `[propext,
Classical.choice, Quot.sound]` (clean). Aggregator `DLNFibre.lean` **not** edited (controller wires).

## What this thread did

Instantiated the audited abstract-chain barcode existence (`Core.Barcode.hasBarcode_top`) at the
concrete chain of a matrix tuple — `V_i := Fin (d i) → k`, `f_i := (A i).mulVecLin` — and carried it
forward to:

1. **the existence half of Gabriel on `Tuple`** (predicate form),
2. **the completeness direction of Prop 3.1b** (`r_{ij} = #bars = cumul m̄`), and
3. **uniqueness of the Gabriel multiplicities** (`m̄ = diff (rank pattern)`), reusing
   `RankPattern.diff_cumul` verbatim.

(2) is exactly the statement disclaimed as out of scope in `IntervalModule` (which only did the
*constructed*-direct-sum side); it is now proved for an **arbitrary** tuple, with **no
change-of-basis matrix** — read straight off the barcode via a range-rank/bar-count identity.

## Landed (sorry-free), in dependency order

- `chainSpace`, `chainEdge` — the `V_i = k^{d_i}`, `f_i = mulVecLin (A_i)` chain of a tuple.
- `compMap_chainEdge` — **the bridge**: `compMap (chainSpace) (chainEdge) i j = (submult d A i j).mulVecLin`.
  Cast-free identification of the abstract-chain and matrix encodings (induction via
  `compMap_succ`/`submult_succ` + `Matrix.mulVecLin_mul`).
- `hasBarcode_tuple` — **existence half of Gabriel on `Tuple`** (predicate form): every tuple over a
  field has a `HasBarcode (fun _ ↦ ⊤)`.
- `rankPattern_eq_finrank_range_compMap` — `r_{ij} = finrank (range (compMap i j))` (ties `Submult`
  to the barcode world via `Matrix.rank`).
- `lineFamily_isSubrep`, `compMap_line_eq_of_alive` — a single line spans a subrep; transport along a
  bar (`compMap i t (line i) = line t` inside the interval). The two geometric sub-lemmas.
- `finrank_range_compMap_eq_card` — **abstract-chain headline**: for a chain carrying a barcode,
  `finrank (range (compMap i j)) = #{λ : birth λ ≤ i ∧ j ≤ death λ}`.
- `barcodeVertexBasis` (+ `_apply`) — **the lines alive at vertex `t` form a `Module.Basis` of
  `V_t`** (the change-of-basis `Q_t` columns; design §1.1).
- `exists_barcode_rankPattern` — **completeness (Prop 3.1b) on `Tuple`**: a Gabriel decomposition
  with `birth ≤ death`, the **Kostant dimension constraint** `#{alive at t} = d_t`, and
  `r_{ij} = #{λ : birth λ ≤ i ∧ j ≤ death λ}` at every `(i,j)`.
- `cumul_finsetSum`, `barMult`, `supported_barMult`, `cumul_barMult_eq_card` — the bar count is
  `cumul N` of the bar-multiplicity array (reuses `IntervalModule.singleDelta`/`cumul_singleDelta`).
- `rankPattern_eq_cumul_barMult` — **uniqueness**: `m̄` is supported, `m̄ = diff (cumul N m̄)`, and
  `(r_{ij} : ℤ) = cumul N m̄ i j`. So `m̄ = diff (rank pattern)` — the multiplicities are a function
  of the rank pattern (uniqueness half of Cor 2.9), via the already-formalised `diff_cumul`.

Witnesses: the `(2,2,2)` tuple over `ℚ` (`tupleWitnessQ`) fires `hasBarcode_tuple`, the rank-pattern
bridge, the completeness theorem, and the uniqueness theorem.

## Statement cards

> **Card 1 — existence half of Gabriel on `Tuple` (predicate form).**
> - **Lean:** `DLNFibre.Core.hasBarcode_tuple` (`lean/DLNFibre/Core/Gabriel.lean`, SHA pending controller commit)
> - **Signature.** `(d : Fin (N+1) → ℕ) (A : Tuple d) : HasBarcode (chainSpace k d) (chainEdge d A) (fun _ ↦ ⊤)`
> - **Gloss.** The concrete chain `k^{d₀} → ⋯ → k^{d_N}` of `mulVecLin` maps attached to any matrix
>   tuple over a field has a barcode: an internal direct sum of interval-module lines at every vertex.
> - **Proved.** The `HasBarcode` predicate (7 clauses) for the tuple chain, by instantiating
>   `hasBarcode_top` at `V_i = Fin (d i) → k`, `f_i = (A i).mulVecLin`.
> - **Assumed.** `Field k`.
> - **Cited.** none (Mathlib `Submodule`/`finrank` API only, in `Barcode`).
> - **Deferred.** the explicit base-change *object* `baseChange P A = ⊕ M^m` (see "Remains").
> - **Status.** sorry-free.

> **Card 2 — completeness of Prop 3.1b for an arbitrary tuple.**
> - **Lean:** `DLNFibre.Core.exists_barcode_rankPattern` (`…/Core/Gabriel.lean`, SHA pending)
> - **Signature.** `(d) (A : Tuple d) : ∃ M (birth death : Fin M → Fin (N+1)), (∀ λ, birth λ ≤ death λ)
>   ∧ (∀ t, #{λ : birth λ ≤ t ∧ t ≤ death λ} = d t) ∧ ∀ i j (hij : i ≤ j),
>   rankPattern d A i j hij = #{λ : birth λ ≤ i ∧ j ≤ death λ}`
> - **Gloss.** Every tuple has a Gabriel decomposition (bars with `birth ≤ death`) satisfying the
>   Kostant dimension constraint, whose rank pattern is recovered as the bar count at every `(i,j)`.
> - **Proved.** `r_{ij} = #{alive bars}` (= the *completeness* direction disclaimed in `IntervalModule`).
> - **Assumed.** `Field k`.
> - **Cited.** none new (Mathlib `finrank_span_eq_card`, `iSupIndep.linearIndependent`).
> - **Deferred.** none for this statement.
> - **Status.** sorry-free.

> **Card 3 — uniqueness of the Gabriel multiplicities.**
> - **Lean:** `DLNFibre.Core.rankPattern_eq_cumul_barMult` (`…/Core/Gabriel.lean`, SHA pending)
> - **Signature.** `(d) (A : Tuple d) : ∃ M birth death, Supported N (barMult M birth death)
>   ∧ diff (cumul N (barMult M birth death)) = barMult M birth death
>   ∧ ∀ i j (hij : i ≤ j), (rankPattern d A i j hij : ℤ) = cumul N (barMult M birth death) i j`
> - **Gloss.** The Gabriel bar-multiplicity array `m̄` is supported, equals `diff` of its own
>   cumulative form, and that cumulative form *is* the rank pattern — so `m̄ = diff (rank pattern)`.
> - **Proved.** the multiplicities are a function of the rank pattern (uniqueness half of Cor 2.9).
> - **Assumed.** `Field k`.
> - **Cited.** none new; **reuses** `RankPattern.diff_cumul` (the already-formalised Prop 3.1a inversion).
> - **Deferred.** none for this statement.
> - **Status.** sorry-free.

## Remains (the literal must-land — the explicit base-change object `g·A = ⊕ M^m`)

NOT landed: the equation `baseChange P A = intervalDirectSum L` (the iso *object* the rung-4 audit
form-note flagged). The geometric heart of it **is** landed as `barcodeVertexBasis` (the per-vertex
change-of-basis `Q_t`). What remains is bounded but **bureaucratic**, and was deprioritised against
the higher-value completeness+uniqueness payload (which serves the rank-pattern/orbit purpose of the
normal form without it):

1. **Reindex** `{λ // birth λ ≤ t ∧ t ≤ death λ} ≃ Fin (d t)` (cardinality `= d t` is the Kostant
   clause already in `exists_barcode_rankPattern`), turning `barcodeVertexBasis` into a
   `Fin (d t)`-indexed basis, hence a matrix `Q_t : Matrix (Fin (d t)) (Fin (d t)) k`.
2. **Invertibility** of `Q_t` (a basis matrix) ⇒ `P := fun t ↦ Q_t⁻¹` as a `BaseChangeGroup` unit.
3. **The normal form.** `(P • A)_t = Q_{t.succ}⁻¹ A_t Q_{t.castSucc}` sends each alive basis vector
   to the next (or `0`), i.e. is a 0/1 partial-permutation block matrix.
4. **Match to `intervalDirectSum L`.** Two frictions, both real:
   (a) the **dimension-vector cast** `foldDim L = d` (a ℕ-equality, provable from the Kostant clause)
   needed even to *type* `baseChange P A = intervalDirectSum L : Tuple d`; and
   (b) the **`finSumFinEquiv` block-reindexing** in `IntervalModule.dirSum`/`intervalDirectSum` —
   matching the barcode's per-vertex block order to the list-fold block order.

*Obstacle (probed, not assumed cheap).* Steps 1–3 are reachable; step 4 is where the cost sits — it
re-bundles a basis-indexed normal form into the *specific* `fromBlocks`/`finSumFinEquiv` packaging of
`intervalDirectSum`, with a dependent `Tuple`-over-`foldDim L` cast. This is the same "push the cast
to one bridge lemma" pattern as thread 06, but the bridge here is between two different block
encodings, not just an index shift. Recommend a **dedicated successor tide** for step 4 if the
explicit `g·A = ⊕ M^m` object is wanted; the orbit ↔ Kostant bijection (Cor 2.9, rung 4e) can also be
packaged directly from `exists_barcode_rankPattern` + `rankPattern_baseChange` + `cumulDiffEquiv`
without it (rank pattern is a complete `G_d`-invariant: `A ∼ B ↔ rankPattern A = rankPattern B`).

## Net

The rung-4 *content* on `Tuple` — existence (predicate), completeness (Prop 3.1b for arbitrary
tuples), and uniqueness of multiplicities — is bedrock and sorry-free. The explicit base-change
*object* is the one remaining piece; its geometric core (`barcodeVertexBasis`) is landed, the rest is
the `intervalDirectSum`/cast bookkeeping of step 4.
