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

## Gap (named, not formalised — thread 109)

The **non-split** general move (`c ≤ b`, `M_{[a,e]} ⊕ M_{[c,b]} ⇝ M_{[a,b]} ⊕ M_{[c,e]}` with a
dim-2 overlap on `[c,b]`) and the **list-gluing** of any move into `intervalDirectSum (Lmove ++ rest)`
are NOT formalised. The non-split case is the 2-strand cut-arrow recombination over `Fin (foldDim …)`
through nested `finSumFinEquiv` at the cut — heavier symbolic `Fin` indexing than the 1-dim split
chain. The common-summand lemma (§1) handles `rest` as a `dirSum` block but the move-list re-association
(`dirSum (intervalModule …) (intervalDirectSum …) = intervalDirectSum (… :: …)`, definitional, and the
`dirSum`-associativity to peel the 2-interval head) is the remaining bridge to the §4 `intervalDirectSum
Lup`/`Ldn` headline. Reachable; not sorry-patched.

## Design notes

- Route choice (Codex `gpt-5-codex` high, 2 consults, decorrelated): for the `t ≠ 0` orbit membership,
  the complete invariant `rankPattern_eq_iff_orbit` is the lighter route at symbolic indices (avoids
  building `P(t)` entrywise) — used for the orbit equivalence (ii). For the split move's `horb` the
  explicit diagonal base change is direct (1-dim chain), so it was used there. The "edit at the cut
  arrow" framing (perturb one entry / add `X • E`, not extract through reindex) keeps the family clean.
- The `foldDim` transport is confined to (ii) and discharged by `rankPattern_transport` (already landed,
  used by `baseChange_normalForm`).
