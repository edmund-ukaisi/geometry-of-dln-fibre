---
title: "Thread 14 — Gabriel normal form + complete invariant (Cor 2.9)"
status: open
topics: [formalisation, gabriel, orbit, normal-form, complete-invariant, cor-2.9, base-change]
created: "2026-06-13"
updated: "2026-06-13"
---

# Thread 14 — the orbit normal form and the complete `G_d`-invariant (Cor 2.9)

**Type:** formalisation (tide). **Environment:** MAIN checkout (isolation was flaky; landed here as
prior teammates did). New module left **UNTRACKED** for the controller to commit — new module only,
aggregator (`DLNFibre.lean`) **untouched**, no committed module edited.

**Module:** `lean/DLNFibre/Core/Orbit.lean` (namespace `DLNFibre.Core`, network-free, `Field k`).
**Build:** `lake build DLNFibre.Core.Orbit` green (1796 jobs), **zero warnings**.
`scripts/sorries`: **0 sorry / 0 #exit / 0 native_decide / 0 axiom**. `#print axioms` on the three
headlines → `[propext, Classical.choice, Quot.sound]` (clean). 399 lines.

## What this thread did

Completed rung 4 (Le Halleur–Rimányi 2024, Cor 2.9) on the `Tuple d` encoding:

1. **The complete `G_d`-invariant** — `rankPattern A = rankPattern B ↔ ∃ g, g • A = B`. The rank
   pattern is a *complete* base-change invariant of type-A representations (THE headline of Cor 2.9).
2. **The Gabriel normal-form object** — every tuple is `G_d`-equivalent to a (reindexed) interval
   direct sum `⊕ M^{m̄}` of its own bars, in the **literal** `intervalDirectSum` form (the
   rung-4-audit form-note's must-land).

### The route (and why it sidesteps thread-13's blocker)

The hard direction `→` (equal rank patterns ⟹ same orbit) is built from the two tuples' barcodes
(`hasBarcode_tuple`):

- equal rank patterns force **equal bar-multiplicity arrays** `barMult` (via the already-formalised
  inversion `RankPattern.diff_cumul` — the `cumul barMult` agree on the lower triangle since they are
  both the rank pattern there, off-range they vanish by support);
- equal `barMult` ⟹ a `(birth, death)`-preserving **relabelling** `σ` of the two bar index sets
  (`Equiv.ofFiberEquiv` over the `(birth, death)` fibres, equal cardinalities);
- the barcode bases at each vertex (`Gabriel.barcodeVertexBasis`) `Basis.equiv`-transport along `σ`
  into an **intertwiner** `φ_t : k^{d_t} ≃ₗ k^{d_t}` of the two `mulVecLin` chains;
- `LinearMap.toMatrix'` turns `φ_t` into invertible matrices `P_t`, and the intertwining identity
  `φ_{t+1} ∘ A_t = B_t ∘ φ_t` becomes `B_t = P_{t+1} A_t P_t⁻¹`, i.e. `P • A = B`.

This **avoids the `finSumFinEquiv` block-matching** that thread-13 step 4 flagged as the bureaucratic
obstacle: the orbit equivalence is built abstractly via `Basis.equiv`, never by computing `P • A`'s
blocks against `intervalDirectSum`'s packaging. The normal-form **object** (target 2) then drops out
of the complete invariant applied to `A` and the interval direct sum of `A`'s bars — the only
`foldDim L = d` cast is handled by a clean `▸` transport (`rankPattern_transport`, proved by `subst`),
kept *off* the rank-pattern lemma it feeds.

## Landed (sorry-free), in dependency order

- `fin_castInt_inj` — `(x : ℤ) = (y : ℤ) → x = y` for `Fin (N+1)`.
- `barMult_eq_card_fiber` — `barMult M b e (a) (b) = #{λ : b λ = a ∧ e λ = b}` (integer array ↔ fibre card).
- `exists_barEquiv` — **the bar relabelling**: equal `barMult` (at every Fin pair) ⟹ `∃ σ : Fin M₁ ≃ Fin M₂` preserving `birth`/`death`.
- `unitOfLinearEquiv` (+ `_val`) — a linear automorphism of `k^m` as a `GLₘ = (Matrix _ _ k)ˣ` element (via `toMatrix'`).
- `baseChange_of_intertwine` — **intertwiner ⟹ base change**: `φ` intertwining the `mulVecLin` chains ⟹ `∃ P, P • A = B`.
- `rankPattern_eq_of_smul` — the easy direction (orbit-invariance), from `BaseChange.rankPattern_smul`.
- `orbit_of_rankPattern_eq` — **the crux** (`→` of the complete invariant), the construction above.
- `rankPattern_eq_iff_orbit` — **the complete `G_d`-invariant (Cor 2.9 headline)**.
- `rankPattern_transport`, `foldDim_eq_sum`, `foldDim_map_finRange`, `multiplicityArray_map_finRange`,
  `exists_cumul_barMult` — the realizability plumbing (the bar list of a barcode realizes `d` and its
  multiplicity array is `barMult = diff(rankPattern)`).
- `baseChange_normalForm` — **the Gabriel normal-form object** (target 2, must-land).

Witnesses (`(2,2,2)` over `ℚ`, `Gabriel.tupleWitnessQ`, with a genuine non-identity `GL₂(ℚ)` base
change `witnessBaseChangeQ`): the crux `orbit_of_rankPattern_eq`, the complete invariant
`rankPattern_eq_iff_orbit`, and the normal form `baseChange_normalForm` all fire on concrete matrix
tuples.

## Statement cards

> **Card 1 — the complete `G_d`-invariant (Cor 2.9).**
> - **Lean:** `DLNFibre.Core.rankPattern_eq_iff_orbit` (`lean/DLNFibre/Core/Orbit.lean`, SHA pending controller commit)
> - **Signature.** `(d) (A B : Tuple d) : (∀ i j (hij : i ≤ j), rankPattern d A i j hij = rankPattern d B i j hij) ↔ ∃ P : BaseChangeGroup d, P • A = B`
> - **Gloss.** Two composable matrix tuples have the same rank pattern `(r_{ij})` iff they lie in the same `G_d = ∏ GL_{d_v}` orbit. The rank pattern is a **complete** base-change invariant.
> - **Proved.** Both directions: `←` from `rankPattern_smul` (rank is conjugation-invariant); `→` from the barcode/`Basis.equiv` construction.
> - **Assumed.** `Field k`.
> - **Cited.** none new (Mathlib `Basis.equiv`, `LinearMap.toMatrix'`, `Equiv.ofFiberEquiv`); **reuses** `RankPattern.diff_cumul`, `Gabriel.hasBarcode_tuple`, `BaseChange.rankPattern_smul`.
> - **Deferred.** none for this statement.
> - **Status.** sorry-free.

> **Card 2 — the Gabriel normal-form object.**
> - **Lean:** `DLNFibre.Core.baseChange_normalForm` (`…/Core/Orbit.lean`, SHA pending)
> - **Signature.** `(d) (A : Tuple d) : ∃ (L : List (Fin (N+1) × Fin (N+1))) (h : foldDim L = d) (P : BaseChangeGroup d), P • A = h ▸ intervalDirectSum L`
> - **Gloss.** Every tuple is `G_d`-equivalent to a reindexing (along `foldDim L = d`) of the interval direct sum `⊕_{(a,b) ∈ L} M_{ab}` of its own bars. The right-hand side is manifestly a direct sum of interval modules; `L`'s multiplicity array is `barMult = diff(rankPattern A)` (the Kostant partition).
> - **Proved.** The genuine `G_d`-orbit normal form in the literal `intervalDirectSum` form (the rung-4-audit form-note's must-land), via the complete invariant.
> - **Assumed.** `Field k`.
> - **Cited.** none new; **reuses** `IntervalModule.rankPattern_intervalDirectSum_eq_cumul`, `orbit_of_rankPattern_eq`.
> - **Deferred.** none for this statement.
> - **Status.** sorry-free.

> **Card 3 — equal rank patterns ⟹ same orbit (the crux).**
> - **Lean:** `DLNFibre.Core.orbit_of_rankPattern_eq` (`…/Core/Orbit.lean`, SHA pending)
> - **Signature.** `(d) (A B : Tuple d) (h : ∀ i j (hij : i ≤ j), rankPattern d A i j hij = rankPattern d B i j hij) : ∃ P : BaseChangeGroup d, P • A = B`
> - **Gloss.** Two tuples with equal rank patterns are in the same `G_d`-orbit. The hard direction of Cor 2.9; the substantive new content.
> - **Proved.** the construction: barcodes → equal `barMult` → relabelling `σ` → `Basis.equiv` intertwiner `φ` → base change `P`.
> - **Assumed.** `Field k`.
> - **Cited.** none new; reuses `hasBarcode_tuple`, `barcodeVertexBasis`, `diff_cumul`.
> - **Deferred.** none for this statement.
> - **Status.** sorry-free.

## Remains (the orbit ↔ Kostant bijection as a packaged `Equiv`)

The orbit ↔ Kostant bijection's **content** is landed: orbits ↔ rank patterns (`rankPattern_eq_iff_orbit`,
the complete invariant), rank patterns ↔ Kostant arrays (`RankPattern.cumulDiffEquiv`, the
already-formalised `diff`/`cumul` bijection), and realizability — every Kostant partition of `d` is
realised by an interval direct sum over `d` — is exactly `baseChange_normalForm`'s target side. What is
**not** packaged is a single `Equiv` object between `MulAction.orbitRel.Quotient (BaseChangeGroup d)
(Tuple d)` and a subtype of realizable Kostant arrays. That packaging is quotient/`SuppArray`
bookkeeping (define the padded rank-pattern array, the descent to orbits, surjectivity from the normal
form); all three ingredients are in hand, so it is a self-contained successor tide, not a frontier.

## Net

Rung 4 is **complete in content**: the rank pattern is a complete `G_d`-invariant
(`rankPattern_eq_iff_orbit`), and every tuple has the explicit Gabriel normal form
(`baseChange_normalForm`, the literal `⊕ M^{m̄}`). Both bedrock, sorry-free, axiom-clean, with concrete
`(2,2,2)/ℚ` witnesses. The only remaining piece is the cosmetic packaging of the orbit↔Kostant
correspondence as a single `Equiv`.
