# Statement card — P2-R2 matrix minor-rank core (the Phase-2 CRUX)

**Thread:** 07-matrix-rank (foundation-lift Phase 2, the flagged crux rung — gets decorrelated review)
**Branch:** `expedition/foundation-lift-p2` (commit `97c3c262`, pushed to `origin`)
**Build:** `./scripts/lb DLNFibre` green at **3820 jobs** (warm baseline was 3819; the `+1` is the new
module). `scripts/sorries` clean (0 sorry / 0 #exit / 0 native_decide / 0 axiom). All seven moved
declarations are axiom-clean `[propext, Classical.choice, Quot.sound]` — verified against the full
built aggregator, addressed as `Matrix.*` (no stale `DLNFibre.Core.*` copies survive).

## What was done

Extracted the **general matrix minor-rank core** (lines ~44–150 + the bottom `rank_map_eq_of_injective`
block of `DLNFibre/Core/RankLocusClosed.lean`) into a new network-free module
**`DLNFibre/Core/Matrix/RankMinors.lean`** in namespace **`Matrix`** — mirroring the eventual Mathlib
home `Mathlib.LinearAlgebra.Matrix.Rank`. The whole core is **absent from Mathlib v4.29**: `Rank.lean`
carries the cardinal-rank submatrix bound (`cRank_submatrix_le`) and the unit/full-rank facts, but **no
minor-vanishing characterisation of `Matrix.rank`**.

The move was a **re-home + Mathlib-grade docstring pass**; **no signature, hypothesis, or proof step
changed**. The only edits to the proof bodies were dropping the `DLNFibre.Core.` qualifier on the
internal cross-references (they now resolve in-namespace) — see the `rank_map_eq_of_injective` note
below. Source-side: the matrix core was deleted from `RankLocusClosed.lean`, which now `import`s the
new module and tags its DLN-specific remainder to it.

## New module + signatures (all ns `Matrix`, `variable {k : Type u} [Field k]`, `open Submodule Module`)

`DLNFibre/Core/Matrix/RankMinors.lean` (175 LoC):

```
-- THE HEADLINE (the `↔`):
theorem rank_le_iff_forall_submatrix_det_eq_zero {p q r : ℕ} (A : Matrix (Fin p) (Fin q) k) :
    A.rank ≤ r ↔ ∀ (er : Fin (r + 1) → Fin p) (ec : Fin (r + 1) → Fin q),
      (A.submatrix er ec).det = 0

-- supports:
theorem rank_submatrix_le_rank {p q : ℕ} (A : Matrix (Fin p) (Fin q) k) {a b : ℕ}
    (f : Fin a → Fin p) (g : Fin b → Fin q) : (A.submatrix f g).rank ≤ A.rank
theorem det_eq_zero_of_rank_lt {p : ℕ} (A : Matrix (Fin p) (Fin p) k) (h : A.rank < p) : A.det = 0
theorem submatrix_det_eq_zero_of_rank_le {p q r : ℕ} {A : Matrix (Fin p) (Fin q) k}    -- the `→`
    (hr : A.rank ≤ r) (er : Fin (r + 1) → Fin p) (ec : Fin (r + 1) → Fin q) :
    (A.submatrix er ec).det = 0
theorem exists_injective_linearIndependent_rows {p q : ℕ} (A : Matrix (Fin p) (Fin q) k) {s : ℕ}
    (hs : s ≤ A.rank) : ∃ er : Fin s → Fin p, Function.Injective er ∧
      LinearIndependent k (fun i ↦ A.row (er i))
theorem exists_submatrix_det_ne_zero_of_le_rank {p q r : ℕ} (A : Matrix (Fin p) (Fin q) k)  -- the `←` core
    (hr : r + 1 ≤ A.rank) : ∃ (er : Fin (r + 1) → Fin p) (ec : Fin (r + 1) → Fin q),
      Function.Injective er ∧ Function.Injective ec ∧ (A.submatrix er ec).det ≠ 0

-- the consequence:
theorem rank_map_eq_of_injective {R S : Type*} [Field R] [Field S]
    {p q : ℕ} (B : Matrix (Fin p) (Fin q) R) (ι : R →+* S) (hι : Function.Injective ι) :
    (B.map ι).rank = B.rank
```

**English gloss.** Over a field, `A.rank ≤ r` iff every `(r+1)×(r+1)` submatrix has determinant `0`.
And matrix rank is preserved by the entrywise application of an injective ring hom between fields.

## The two directions of the headline `↔`

- **`→`** (`A.rank ≤ r ⟹ minors vanish`): `submatrix_det_eq_zero_of_rank_le`. A square `(r+1)`-submatrix
  has rank `≤ A.rank ≤ r < r+1` (`rank_submatrix_le_rank`, a `ℕ`-cast of `Matrix.cRank_submatrix_le`),
  hence is not full rank, hence `det = 0` (`det_eq_zero_of_rank_lt` — a non-unit square matrix over a
  field has det `0`). Mechanical.

- **`←`** (`minors vanish ⟹ A.rank ≤ r`, the CRUX, proved contrapositively via
  `exists_submatrix_det_ne_zero_of_le_rank`): if `r+1 ≤ A.rank`, exhibit a nonzero `(r+1)`-minor.
  (1) `exists_injective_linearIndependent_rows` extracts `r+1` linearly independent rows
  (`exists_linearIndependent'` gives a maximal independent row subfamily of cardinality `= A.rank` via
  `finrank_span_eq_card` + `rank_eq_finrank_span_row`; `r+1 ≤` that card gives a `Fin (r+1) ↪ κ` slice).
  (2) Apply the same row-extraction to the **transpose** of the resulting `(r+1)×q` block to pick `r+1`
  independent columns (`rank_transpose` ties column rank to the row block's rank `= r+1`). (3) The
  square `(r+1)×(r+1)` block has linearly independent columns, hence is a unit
  (`Matrix.linearIndependent_cols_iff_isUnit`), hence its det is nonzero (`isUnit_iff_isUnit_det`).

## Index generality of the `←` direction — CONFIRMED unchanged

The `←` direction compiles **at the same generality as the source**, byte-for-byte in the proof body
(only the namespace and surrounding `open` changed). The stated shape is:

- The full matrix is `A : Matrix (Fin p) (Fin q) k` with `{p q r : ℕ}` and `[Field k]`.
- The minor index maps are `er : Fin (r+1) → Fin p` and `ec : Fin (r+1) → Fin q` — **arbitrary
  functions**, no injectivity *demanded* of the caller in the `↔`. (The `→` direction needs none — a
  non-injective `er`/`ec` repeats a row/column, the det is `0`, so the criterion is unweakened by
  allowing them. The `←` direction *produces* injective maps, returned as bundled witnesses in
  `exists_submatrix_det_ne_zero_of_le_rank`, but they are existentially packed, not part of the `↔`.)
- The supports `exists_injective_linearIndependent_rows` are stated for a `Fin s` slice (used at
  `s = r+1` for rows and at the transpose for columns), again unchanged.

**General `Fintype` index — considered, NOT adopted.** A genuinely more general statement would index
`A` by arbitrary `[Fintype][DecidableEq] m`/`n` and the minor by `Fin (r+1) → m`/`n`. This is plausible
upstream-Mathlib-grade (`Matrix.rank`/`cRank_submatrix_le`/`linearIndependent_cols_iff_isUnit` are all
stated for `Fintype` indices), but the `←` proof leans on `Fintype.card_fin`/`Fin.card` rewrites
(`hBrank : B.rank = r+1` from `rank_matrix` + `card_fin`; the `Fin s ↪ κ` count) that would need
re-routing through `Fintype.card`. Per the brief ("don't risk the build"), I kept the `Fin`/`ℕ`
shape verbatim and **flag the `Fintype` generalisation as a clean follow-up**, not done here. The DLN
consumers all index by `Fin` (matrix dimensions `d j`/`d i`), so the `Fin` shape is exactly what they
need — no narrowing relative to prior use.

## `rank_map_eq_of_injective` — the one body edit

In `RankLocusClosed` this lemma lived in a separate `namespace Matrix` block at the bottom of the file
and called the bridge as `DLNFibre.Core.rank_le_iff_forall_submatrix_det_eq_zero`. Now that both live
together in `namespace Matrix` in `RankMinors.lean`, those two `rw` references became the in-namespace
`rank_le_iff_forall_submatrix_det_eq_zero` (the only proof-body change in the whole extraction). No
logic changed.

## Namespace / sibling-clash decisions

- **Namespace `Matrix`** (mirrors `Mathlib.LinearAlgebra.Matrix.Rank`) for a zero-surgery upstream
  move. Core consumers already `open Matrix`, so their bare references re-resolve in the new namespace
  with no edits; DLN consumers already used the `Matrix.` prefix.
- **Sibling-clash gate CLEAR.** `rg` over `.lake/packages/mathlib/` finds **none** of the seven names
  (`rank_le_iff_forall_submatrix_det_eq_zero`, `rank_map_eq_of_injective`, `rank_submatrix_le_rank`,
  `det_eq_zero_of_rank_lt`, `submatrix_det_eq_zero_of_rank_le`, `exists_submatrix_det_ne_zero_of_le_rank`,
  `exists_injective_linearIndependent_rows`) anywhere in Mathlib v4.29. All seven are genuinely new in
  the `Matrix` namespace.
- **`@[stacks …]` declined** (per the P1/P2-R1 precedent): no exact Stacks-tag match for the
  minor-vanishing rank characterisation.

## What stayed DLN-local + what re-pointed (L2 sweep)

**Stayed local in `RankLocusClosed.lean`** (the DLN-specific remainder, now tagged to the extracted
core): `eval_submult_genericTuple`, `minorPoly`, `eval_minorPoly`, `rankMinorSet`,
`mem_zeroLocus_rankMinorSet_iff`, `image_orbitRankLocus_eq_zeroLocus`,
`isZariskiClosed_orbitRankLocus`, `orbit_subset_orbitRankLocus`, `orbitSet_subset_orbitRankLocus`,
`vanishingIdeal_orbitRankLocus_le_orbitSet`, and the four `Witness` examples. (`genericTuple` itself
already lives in `Core.GenericTuple`.) `RankLocusClosed.lean`: 366 → 224 LoC.

**Re-pointed / swept** (full-aggregator build is the real test — L2):
- `DLNFibre.lean` aggregator — new import line appended (single-writer, append-only; not reordered).
- `DLNFibre/Core/RankLocusClosed.lean` — `import DLNFibre.Core.Matrix.RankMinors` added; matrix core
  removed; internal references (`rank_le_iff_forall_submatrix_det_eq_zero` &c.) resolve via `open Matrix`.
- `DLNFibre/Core/DeterminantalChartRing.lean`, `DLNFibre/Core/FibreRankBridge.lean` — Core consumers
  (`submatrix_det_eq_zero_of_rank_le`, `rank_le_iff_forall_submatrix_det_eq_zero`, `rank_submatrix_le_rank`);
  both `open Matrix`, no edit needed; build green.
- `DLNFibre/Core/FibreBundleLocallyTrivialFull.lean` — **the L2 trap**: uses `rank_submatrix_le_rank`
  **transitively** (no direct `RankLocusClosed` import — reaches it via `FibreChartConjugation` →
  `FibreBundleTransition`); the transitive path still reaches the lemma (now via `RankLocusClosed →
  RankMinors`); builds green in the full aggregator.
- `DLNFibre/DLN/BundleShiftDischarge.lean`, `DLNFibre/DLN/RlctPayoff.lean` — DLN consumers of
  `Matrix.rank_map_eq_of_injective` (already `Matrix.`-qualified, no code edit). Prose in
  `BundleShiftDischarge` re-pointed from `Core.RankLocusClosed` to `Core.Matrix.RankMinors`.

DLN base-change payoff `codimRealFibre_eq_codimRepCanonical_baseChange` (the direct
`rank_map_eq_of_injective` consumer) verified axiom-clean — proof transports unchanged. Cited Aoyagi/SLT
axioms (the `_via_aoyagi` payoff theorems) untouched and out of scope.

## Holes / surprises

- **None affecting correctness.** Verbatim re-home of already-general, already-green code; the one
  proof-body change (the `DLNFibre.Core.` qualifier drop in `rank_map_eq_of_injective`) is forced by
  the namespace co-location and is logic-neutral.
- **Flagged for the decorrelated review** (honesty on the `←` direction): I am confident the `←`
  direction compiled **unchanged** at the `Fin`/`ℕ` generality (the proof body is identical to the
  banked source modulo namespace). The one thing I did **not** do is *generalise* the index to arbitrary
  `Fintype` — I considered it (the underlying Mathlib lemmas support it) but kept the `Fin` shape to not
  risk the build; this is a deliberate non-extension, recorded as a clean follow-up, not a gap in the
  stated claim.
- LoC delta: `+175` (new module) / `−142` (RankLocusClosed shrink) / `+~12` (aggregator comment) /
  `~±0` proof content. Pre-existing longLine warnings (`FibreTargetOverlap`, `DLNFibre:471`, etc.) are
  in files this rung did not touch.
