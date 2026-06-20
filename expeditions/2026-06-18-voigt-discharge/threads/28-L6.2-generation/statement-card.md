# Statement card — L6.2 generation (box-move generation crux)

Module: `lean/DLNFibre/Core/BoxMoveGeneration.lean` (branch
`expedition/voigt-discharge`, L6.2c-generation commit). All headlines sorry-free, incl. the L6.2c
generation headline
`box_move_chain_of_le` (axioms `[propext, Classical.choice, Quot.sound]`; the move-side lemmas
without `Nat.find`/`min'`/filter use `[propext, Quot.sound]`). Whole `DLNFibre` library builds green.

The combinatorial converse to the box-move degeneration, on **rank patterns as integer arrays**
(`ℤ → ℤ → ℤ`, the `Core.RankPattern` `diff`/`Supported` world), decoupled from the
orbit/representation engine. `diff g a e = g a e − g a (e+1) − g (a−1) e + g (a−1)(e+1)` is the
paper's second difference (`RankPattern.diff`); `Supported N g` is the out-of-range-`=0` convention
(`i < 0` or `j > N`), pinned to `diff_cumul` exactly.

---

> **L6.2b-key (★).** For a nonnegative array `g` (`∀ i j, 0 ≤ g i j`) supported off the half-plane
> (`Supported N g`) and a cell `(I,J)` with `I < J`, `J ≤ N`, `0 < g I J`:
> `g I J ≤ ∑_{p ∈ coveringRect g N I J} diff g p.1 p.2`, where `coveringRect` is the
> rectangle-in-support family `{(a,e) : a ∈ [0,I], e ∈ [J,N], ∀ j ∈ [J,e], g > 0 on [a,I]×{j}}`.
>
> - **Lean:** `DLNFibre.Core.sum_secondDiff_coveringRect_ge`
> - **Gloss.** Summing the second difference of `g` over every rectangle `[a,I]×[J,e]` that stays in
>   the support of `g` is at least the value `g I J`. (★ of thread 26.)
> - **Proved.** The full telescope: row-fibre of `coveringRect` at `a` is `Ico J (qcol a)` (`qcol` =
>   first bad column, `Nat.find`), inner telescope collapses `diff g` to a column difference
>   (`sum_Ico_diff_eq`), outer column telescope gives `g I J` (`sum_Icc_colDiff`), the remainder is
>   `≤ 0` by the adjacent Abel shift (`sum_Icc_colDiff_abel`) + the jump fact
>   (`sum_Icc_colDiff_qcol_nonpos`).
> - **Assumed.** `g ≥ 0` and `Supported N g` (both hold for `g = r − s` of achievable patterns with
>   the same diagonal). No extremality of `(I,J)` is used — holds at any positive cell.
> - **Cited.** none. **Deferred.** none. **Status.** sorry-free.

> **L6.2b (move existence).** With `g = r − s` nonnegative and supported, `s` achievable
> (`∀ i j, 0 ≤ diff s i j`), at any positive cell `(I,J)` of `g`: `∃ p ∈ coveringRect g N I J`,
> `1 ≤ diff r p.1 p.2`.
>
> - **Lean:** `DLNFibre.Core.exists_coveringInterval_diff_pos`
> - **Gloss.** Some covering interval `[a,e]` (rectangle in `supp g`) carries positive `r`-multiplicity
>   `m(r)_{[a,e]} ≥ 1` — the interval the linked box move recombines.
> - **Proved.** By contradiction from (★): `diff g = diff r − diff s` (`diff_sub`), `diff s ≥ 0`, so
>   `diff r ≤ 0` on `coveringRect` would force `∑ diff g ≤ 0 < g I J`.
> - **Cited.** none. **Deferred.** none. **Status.** sorry-free.

> **L6.2a (the box move).** `boxDrop r a c b e = r − 1_D`, `D = [a,c−1]×[b+1,e]`. The four-corner
> identity `boxIndicator_diff` gives `diff(1_D)`; achievability `diff_boxDrop_nonneg` (on `i ≤ j`),
> dimension preservation `boxDrop_diag`, the drop `boxDrop_le` and strict drop `boxDrop_strict`.
>
> - **Lean:** `DLNFibre.Core.boxIndicator_diff`, `diff_boxDrop_nonneg`, `boxDrop_diag`,
>   `boxDrop_le`, `boxDrop_strict`.
> - **Gloss.** Dropping the rectangle `D` from `r` keeps multiplicities nonnegative on the upper
>   triangle when the move is applicable (`m(r)_{[a,e]} ≥ 1`, linked `m(r)_{[c,b]} ≥ 1`), fixes the
>   diagonal, and strictly lowers `r` at `(a,b+1) ∈ D`.
> - **Proved.** Exactly as stated.
> - **Assumed.** `a < c ≤ b+1 ≤ e`; achievability scoped to `i ≤ j` (the rank pattern's domain).
> - **Caveat (next to the claim).** In the **split case** `c = b+1`, the `(c,b)` corner of
>   `diff(1_D)` lands **below the diagonal** (`i = b+1 > j = b`), where `diff(r−1_D) = −1` — so
>   `r − 1_D` is *not* a globally-achievable array there; achievability is therefore stated on
>   `i ≤ j` only (verified: 6.1M upper-triangle checks, 0 failures). On the upper triangle the move
>   on multiplicities is the 3-term split move and matches `r − 1_D` (rank-diff ∈ {0,1}).
> - **Cited.** none. **Deferred.** none. **Status.** sorry-free.

> **Sub-fact 1 (linked applicability).** `one_le_diff_linked`: at an extremal deficient cell `(i0,j0)`
> with the three neighbours `g (i0+1)(j0−1) = g (i0+1) j0 = g i0 (j0−1) = 0` and `g i0 j0 ≥ 1`,
> `diff s ≥ 0`: `1 ≤ diff r (i0+1) (j0−1)`.
>
> - **Lean:** `DLNFibre.Core.one_le_diff_linked`. **Proved** (the extremal second-difference collapse
>   `diff g (i0+1)(j0−1) = g i0 j0`, then `diff r ≥ diff g`). **Status.** sorry-free.

> **Reusable interface for L6.2c / L6.4.** `BoxMoveStep r r'` = `∃ a c b e, a < c ∧ c ≤ b+1 ∧
> b+1 ≤ e ∧ 1 ≤ diff r a e ∧ (c ≤ b → 1 ≤ diff r c b) ∧ r' = boxDrop r a c b e`;
> `BoxMoveChain r s = Relation.ReflTransGen BoxMoveStep r s`.
>
> - **Lean:** `DLNFibre.Core.BoxMoveStep`, `DLNFibre.Core.BoxMoveChain`. **Status.** definitions, used
>   by the landed L6.2c headline below.

---

## L6.2c — box-move generation (LANDED, thread 28-cont, sorry-free)

> **L6.2c (★★, the headline).** Achievable rank patterns `s ≤ r` over the same dimension vector are
> connected by a finite chain of applicable box moves: `BoxMoveChain r s`.
>
> - **Lean:** `DLNFibre.Core.box_move_chain_of_le`.
> - **Signature.** `(N : ℤ) (r s : ℤ → ℤ → ℤ) (hsupp : Supported N (fun i j ↦ r i j − s i j))
>   (hpos : ∀ i j, 0 ≤ r i j − s i j) (hbelow : ∀ i j, j ≤ i → r i j − s i j = 0)
>   (hms : ∀ i j, 0 ≤ diff s i j) : BoxMoveChain r s`.
> - **Gloss / hypotheses.** `hpos`: `r` dominates `s` pointwise (the order). `hbelow`: `r` and `s`
>   **agree on/below the diagonal** — a *necessary* condition, since every box move's drop rectangle
>   `D = [a,c−1]×[b+1,e]` lies in the strict upper triangle (`i < j`), so a chain can never change a
>   value at `j ≤ i`. `hms`: `s` is achievable (`diff s = Kostant multiplicities ≥ 0`). `hsupp`: the
>   residual is supported (out-of-range `= 0`). Together these are non-vacuous and consistent (witness
>   below).
> - **Proved.** Strong induction on the deficiency `Φ = (deficiency N r s).toNat` (`ℤ`-sum
>   `∑_{0≤i≤j≤N}(r−s)` over `triBox N`, then `.toNat`): base `Φ = 0 ⟹ r = s` (each triangle summand
>   vanishes, support + below-diagonal agreement extend to literal `funext`); step the descent
>   produces a `BoxMoveStep r r'` with `s ≤ r'` and `Φ r' s < Φ r s`, then `ReflTransGen.head`.
> - **Non-vacuity witness (in-file).** `N = 2`, dim `(1,2,2)`: `bmcLower = cumul 2 {[0,1],[1,2],[2,2]}`,
>   `bmcUpper = bmcLower + 1_{(0,2)}` (= `cumul 2 {[0,2],[1,1],[2,2]}`). All four hypotheses hold and
>   `bmcUpper ≠ bmcLower` (differ at `(0,2)`) — the chain is the single split move
>   `[0,2]+[1,1] ↦ [0,1]+[1,2]`, non-trivial.
> - **Cited.** none. **Deferred.** none. **Status.** sorry-free, axioms
>   `[propext, Classical.choice, Quot.sound]`.

Supporting lemmas (all sorry-free):

1. **`exists_extremalCell`** — the extremal deficient cell. Over the finite positive-cell set
   `S = (Icc 0 N ×ˢ Icc 0 N).filter (0 < g ·)`, take `j0 = (S.image Prod.snd).min'`, then
   `i0 = (S.filter (·.2 = j0)).image Prod.fst |>.max'`; the three neighbour vanishings
   (`g (i0+1) j0 = 0` from `i0`-maximality, `g i0 (j0−1) = g (i0+1)(j0−1) = 0` from `j0`-minimality)
   follow from `min'_le`/`le_max'` + below-diagonal vanishing. (Product-support `Finset`, not a
   bounded-existential filter — sidesteps the `decidableExistsAndFinsetCoe` ↔ `Classical.propDecidable`
   instance clash.)

2. **`exists_boxMoveStep_descent`** — the descent step. Combines `exists_extremalCell` + sub-fact 1
   (`one_le_diff_linked`, anchor `c = i0+1, b = j0−1`) + L6.2b (`exists_coveringInterval_diff_pos`,
   the `(a,e)` with rectangle in `supp g`, via `coveringRect_pos`) into one
   `BoxMoveStep r (boxDrop r a c b e)` with `∀ i ≤ j, s ≤ boxDrop r` (rectangle ⊆ supp ⟹ `g ≥ 1` on
   `D`) and the bounds `0 ≤ a < c ≤ b+1 ≤ e ≤ N`. (Achievability of `r`, `diff r ≥ 0`, is **not**
   needed — `hmr` was dropped: a chain step only asserts the move was applicable to the *current*
   pattern.)

3. **`deficiency` / `triBox` / `deficiency_boxDrop_lt` / `box_move_chain_aux`** — the `Φ`-induction
   scaffolding (`triBox N = {0≤i≤j≤N}`, `single_le_sum` + `boxDrop_strict` for the strict drop,
   `funext_of_deficiency_eq_zero` for the base case).

Boundary convention pinned: `diff` and `Supported N` are taken verbatim from `Core.RankPattern`; the
`(a−1)`,`(e+1)` boundary indices are honest `ℤ` indices with out-of-range `= 0` realised by
`Supported` — the thread-26-flagged most-likely-to-break point, matched exactly to `diff_cumul`.

## For L6.4 (next)

`BoxMoveChain r s` (a `ReflTransGen`) is the reusable output L6.4 composes with the L6.1-general
per-move degeneration (`Core.BoxMoveGeneral`): `Relation.ReflTransGen.head_induction_on` /
`.trans` walks the chain, each `BoxMoveStep` feeding one degeneration. The chain's
`hbelow`-necessity (moves fix `{j ≤ i}`) means the matrix-side composition only needs the
strict-upper-triangle data each step changes.
