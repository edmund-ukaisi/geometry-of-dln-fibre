# Statement card — L6.1-general (thread 27): common-summand reduction + split box move

Module: `lean/DLNFibre/Core/BoxMoveGeneral.lean` (imported at the end of `DLNFibre.lean`).
Builds on the landed engine `mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily` (thread 23).
All headlines axiom-clean `[propext, Classical.choice, Quot.sound]`; whole library sorry-free.

## 1. Common-summand lemma (the `rest` reduction)

> **Claim.** If `D₀`'s flattening lies in the Zariski closure of the orbit of `U₀` — witnessed by a
> polynomial family `F₀` (engine hypotheses) — then for ANY common summand `R` the flattening of
> `dirSum D₀ R` lies in the closure of the orbit of `dirSum U₀ R`.
>
> - **Lean:** `DLNFibre.Core.mem_closure_dirSum_of_mem_closure` (@ `2c0ee61`).
> - **Gloss.** Over `[Field k] [Infinite k]`, for `U₀ D₀ : Tuple d`, `R : Tuple d'`,
>   `F₀ : Tuple (Polynomial k) d` with `tupleEval F₀ 0 = D₀` and `∀ t ≠ 0, ∃ P, P • U₀ = tupleEval F₀ t`:
>   `canonicalCoord (fun l ↦ d l + d' l) (dirSum D₀ R) ∈ zeroLocus (vanishingIdeal (orbitSet (dirSum U₀ R)))`.
> - **Proved.** The full implication, any `d, d', U₀, D₀, R, F₀`. The lifted family is
>   `dirSumPoly F₀ (constPoly R)` (block-diagonal, `R` fixed); the `t ≠ 0` base change is
>   `liftDirSumBaseChange P = P ⊕ 1_R` (per-vertex `reindex finSumFinEquiv (fromBlocks (P v) 0 0 1)`),
>   with `liftDirSumBaseChange_smul : (P ⊕ 1) • (dirSum A B) = dirSum (P • A) B`. Reuses the
>   block-diagonal levers `reindex_fromBlocks_mul` / `reindex_fromBlocks_one` of `Core.IntervalModule`.
> - **Assumed.** the engine's two hypotheses on `F₀` (caller's burden).
> - **Cited / Deferred.** none.
> - **Scope (caveat next to claim).** `R` rides as the SECOND `dirSum` block (block-diagonal); this is
>   exactly the shape of a box move's appended `rest` when both up/downstairs are written
>   `dirSum (2-interval part) (intervalDirectSum rest)`. It isolates `rest` from the symbolic move but
>   does NOT itself glue the move into the list form `intervalDirectSum (Lmove ++ rest)` (a `dirSum`
>   re-association / reindex, not done here).
> - **Status.** sorry-free; non-vacuity witness in-file (the certified `(1,2,1)` box move riding a
>   `1`-dim `R = M_{[0,0]}`).

## 2. Split box move `M_{[a,e]} ⇝ M_{[a,b]} ⊕ M_{[b+1,e]}` (`c = b+1`, no rest)

> **Claim.** Over an infinite field, the flattening of the cut chain `splitCut a e b` lies in the
> Zariski closure of the orbit of the single interval module `M_{[a,e]}`; and (for `a ≤ b`, `b+1 ≤ e`)
> the cut chain is `G_d`-equivalent to the genuine split sum `M_{[a,b]} ⊕ M_{[b+1,e]}`.
>
> - **Lean:** `DLNFibre.Core.splitCut_mem_closure` (the closure membership) and
>   `DLNFibre.Core.splitCut_orbit_intervalDirectSum` (the orbit equivalence) (@ `2c0ee61`).
> - **Gloss.** `splitCut a e b : Tuple (intervalDim a e)` is `M_{[a,e]}` (the all-identity chain) with
>   the single edge `b → b+1` zeroed. (i) `canonicalCoord (intervalDim a e) (splitCut a e b) ∈ zeroLocus
>   (vanishingIdeal (orbitSet (intervalModule a e)))`. (ii) For `a ≤ b.castSucc`, `b.succ ≤ e`:
>   `∃ P, P • splitCut a e b = h ▸ intervalDirectSum [(a, b.castSucc), (b.succ, e)]` where
>   `h : foldDim [...] = intervalDim a e` (`foldDim_split_eq`).
> - **Proved.** Both. The degeneration family `splitFamilyPoly a e b` carries parameter `X` on edge `b`
>   (limit at `t = 0` is the cut; `tupleEval_splitFamilyPoly_zero`). The `t ≠ 0` orbit certificate is
>   the EXPLICIT diagonal base change `splitBaseChange` — identity at vertices `≤ b`, scalar `t • 1` at
>   vertices `> b` (`scalarUnit`, a unit for `t ≠ 0`) — proven `splitBaseChange_smul :
>   splitBaseChange • M_{[a,e]} = tupleEval (splitFamilyPoly a e b) t`. The orbit equivalence (ii) is
>   the complete invariant `orbit_of_rankPattern_eq` applied to the rank-pattern equality
>   `rankPattern_splitCut` (the cut chain's `r_{ij} = [a≤i ∧ j≤b] + [b+1≤i ∧ j≤e]`, the split-sum
>   indicator) vs `rankPattern_intervalDirectSum`.
> - **Assumed.** `[Field k] [Infinite k]`; orbit-equivalence (ii) needs `a ≤ b.castSucc`, `b.succ ≤ e`
>   (a genuine split, both sub-intervals non-degenerate).
> - **Cited / Deferred.** none.
> - **Scope (caveat next to claim).** This is the split case `c = b+1` (the dropped-`M_{[c,b]}` branch)
>   with NO rest. The cut chain is the split downstairs realized over `intervalDim a e` (so NO
>   `foldDim`-transport for `splitCut` / `M_{[a,e]}` themselves — the transport only appears connecting
>   `splitCut` to the list form in (ii)). The membership is one point in one orbit's closure (relative
>   to `k`-points), not the rank-locus equality (Thm 3.8).
> - **Supporting lemmas (sorry-free).** `submult_splitCut_eq_of_not_cross` / `…_eq_zero_of_cross` (the
>   cut chain's sub-product equals `M_{[a,e]}`'s off the cut, vanishes across it); `rankPattern_splitCut`;
>   `foldDim_split_eq`.
> - **Status.** sorry-free; non-vacuity witness in-file (`M_{[0,2]} ⇝ M_{[0,0]} ⊕ M_{[1,2]}` over `ℚ`).

## 3. Downstairs-transport wrapper + split-case full §4 list headline (thread 27 continuation, @ `b61c5a3`)

> **Claim (downstairs transport).** The engine lands an *orbit-equivalent* downstairs `D' = Q • D₀`:
> given `F` with limit `D₀` and `t ≠ 0` orbit membership in `U`, and `Q • D₀ = D'`, then
> `canonicalCoord D' ∈ closure (orbit U)`. The family is base-changed (`smulPoly Q F`), `Q • (P • U) =
> (Q·P) • U` stays in the orbit.
>
> - **Lean:** `mem_closure_of_polynomialFamily_orbitEquiv` (single `d`); `smulPoly` /
>   `tupleEval_smulPoly` (the constant base change on a polynomial family, `eval ∘ C = id`);
>   `mem_closure_dirSum_of_mem_closure_orbitEquiv` (the combined `rest`-rider + transport).
> - **Proved.** Fully general. Bridges a recombination *limit* (only `G_d`-equivalent to the genuine
>   interval sum) to the genuine interval sum itself — the form the list headline needs.

> **Claim (split §4 list headline, arbitrary `rest`).** For a genuine split (`a ≤ b.castSucc`,
> `b.succ ≤ e`) and arbitrary `rest`, with `Lup = (a,e) :: rest`, `Ldn = (a,b) :: (b+1,e) :: rest`:
> `canonicalCoord (intervalDirectSum Ldn) ∈ closure (orbit (intervalDirectSum Lup))` (the lists share a
> dimension vector `foldDim Lup`; `Ldn` is transported onto it).
>
> - **Lean:** `splitMove_intervalDirectSum_mem_closure` (@ `b61c5a3`). Supporting:
>   `foldDim_splitCons_eq` (the transport), `orbit_dirSum_splitCut_intervalDirectSum` (the `Q` via the
>   complete invariant on rank patterns: `splitCut` riding `rest` is `G_d`-equivalent to `intervalDirectSum
>   Ldn`).
> - **Proved.** The full §4 headline for the **split case** with arbitrary `rest`. The orbit base
>   `dirSum (intervalModule a e) (intervalDirectSum rest)` is `intervalDirectSum Lup` definitionally.
> - **Status.** sorry-free; non-vacuity witness in-file (`M_{[0,1]} ⇝ M_{[0,0]} ⊕ M_{[1,1]}` riding
>   `M_{[1,2]}` as `rest`, over `ℚ`). Axiom-clean.

## 4. The NON-SPLIT move `M_{[a,e]} ⊕ M_{[c,b]} ⇝ M_{[a,b]} ⊕ M_{[c,e]}` (`a < c ≤ b < e`) — CLOSED (thread 109, @ `3dcdc23`)

> **Claim (non-split §4 list headline).** Over an infinite field, for `a < c ≤ b.castSucc`,
> `b.succ ≤ e` and arbitrary `rest`: the flattening of the downstairs
> `intervalDirectSum ((a,b) :: (c,e) :: rest)` (transported onto the upstairs dimension vector, which
> the move preserves) lies in the Zariski closure of the orbit of the upstairs
> `(M_{[a,e]} ⊕ M_{[c,b]}) ⊕ rest`.
>
> - **Lean:** `DLNFibre.Core.nonsplitMove_intervalDirectSum_mem_closure` (@ `3dcdc23`).
> - **Proved.** The full §4 headline for the non-split case, arbitrary `rest`. Axiom-clean
>   `[propext, Classical.choice, Quot.sound]`.
> - **Scope (caveat next to claim).** The orbit base is written `dirSum (dirSum M_{[a,e]} M_{[c,b]})
>   (intervalDirectSum rest)` — the upstairs `Lup = (a,e) :: (c,b) :: rest` with the two-interval move
>   part **left-associated** (the §4 `Lup` up to a `dirSum` re-association / dim-vector `+0`, not
>   yet reassociated to the right-nested `intervalDirectSum Lup`).
> - **Status.** sorry-free; non-vacuity witnesses in-file (the `(1,2,1)` recombination over `ℚ`:
>   `splice_mem_orbit_U2` for `λ ≠ 0`, and the headline with empty `rest`).

The recombination family is `splice a c e b λ` (the upstairs `U₂ = M_{[a,e]} ⊕ M_{[c,b]}` with the
single edge `b` overwritten by the row `[λ, 1]`, defined **entrywise** — dimension-agnostic, no
`fromBlocks`/`▸` at the edge). The crux was the **crossing rank** `rankPattern (splice λ) i j` for
`i ≤ b.castSucc < b.succ ≤ j`:

- **`rankPattern_splice_cross`** (the crux, @ `7f77134`): `= if j ≤ e ∧ ((λ ≠ 0 ∧ a ≤ i) ∨ c ≤ i)
  then 1 else 0`. Upper bound `rank ≤ [j ≤ e]` via `rank_mul_le_left` + `rankPattern_dirSum` (no entry
  work); the nonzero/zero split is four entry-level cases (`splice_cross_ne_zero_short/_long`,
  `splice_recomb_below_zero_of_lam_zero/_no_long`). The reusable rank bricks
  `matrix_eq_zero_of_rank_eq_zero` / `one_le_rank_of_ne_zero` and the four `reindex_fromBlocks_*` block
  entry lemmas + `splice_edge_inl/inr` support it; entry sums reduced via
  `← Equiv.sum_comp finSumFinEquiv` + `Fintype.sum_sum_type` (the Mathlib-idiomatic block-sum split).
- **Full rank pattern** (@ `0a74527`): `rankPattern_splice_eq_U2_of_ne_zero` (λ≠0 ⟹ splice has U₂'s
  rank pattern), `foldDim_nonsplit_eq` (the move preserves the dimension vector),
  `rankPattern_splice_zero_eq_down` (λ=0 ⟹ splice 0 has the downstairs rank pattern). Range-by-range
  (below/above off-edge via `submult_splice_below/_above`; crossing via the crux), closed by
  `split_ifs <;> omega` on `Fin.val` order facts.
- **Orbit + engine + headline** (@ `3dcdc23`): `splicePoly` (family carrying `X`),
  `tupleEval_splicePoly`, `splice_mem_orbit_U2` / `splice_zero_orbit_down` (complete invariant
  `orbit_of_rankPattern_eq`), `orbit_dirSum_splice_intervalDirectSum` (rest rides), then the
  downstairs-transport + common-summand wrapper `mem_closure_dirSum_of_mem_closure_orbitEquiv` (§3).

**Mathlib brick used for the rank-1 split:** not a single "`rank_le_one`" lemma — the upper bound is
`Matrix.rank_mul_le_left` against the computable `rankPattern U₂` (≤ `[j≤e]`), and the lower bound is
the nonzero-entry route `one_le_rank_of_ne_zero` (rank-0 ⟹ matrix-0 via `rank_eq_finrank_span_cols` +
`Submodule.finrank_eq_zero` + `span_eq_bot`).

**Decorrelated design (Codex `gpt-5-codex` high, `codex/crossing-rank-{prompt,answer}.md`; earlier
`gpt-5` xhigh `codex/nonsplit-*`):** confirmed the rank-pattern route over an explicit `P(t)`, and the
"`rank ≤ 1` (height) + nonzero-entry / matrix-is-zero" split with the landed block-entry lemmas —
adopted.

## Design notes

- Route choice (Codex `gpt-5-codex` high, 2 consults, decorrelated): for the `t ≠ 0` orbit membership,
  the complete invariant `rankPattern_eq_iff_orbit` is the lighter route at symbolic indices (avoids
  building `P(t)` entrywise) — used for the orbit equivalence (ii). For the split move's `horb` the
  explicit diagonal base change is direct (1-dim chain), so it was used there. The "edit at the cut
  arrow" framing (perturb one entry / add `X • E`, not extract through reindex) keeps the family clean.
- The `foldDim` transport is confined to (ii) and discharged by `rankPattern_transport` (already landed,
  used by `baseChange_normalForm`).
