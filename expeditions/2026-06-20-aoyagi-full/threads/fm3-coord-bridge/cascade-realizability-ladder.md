# Cascade realizability ladder (sub-2b, #116) — the routeStep-body unblock

The genuinely-new Core piece for the general `routeStep` body: the §4 achiever witness
`T* ∈ RealizableRank M₀`, realized by the explicit diagonal cascade (pp2 g228, banked
`origin/g228-rankfn-cascade @d975c86`). Built bottom-up in `lean/DLNFibre/Core/CascadeRank.lean`,
network-free, each rung committed green. The clean lever: a cascade product is a single
partial-identity, so its rank = #surviving 1s = window-min — NO `Matrix.rank_mul_le`, NO surjectivity.

## Ladder state (commit SHAs pinned)

- **RUNG 1 — DONE @5395c9f.** `rank_partialId (r c t) : (partialId k r c t).rank = min t (min r c)`
  (the count-the-1s atom). `partialId k r c t : Matrix (Fin r)(Fin c) k` = the block `diag(1^t, 0)`.
  Mathlib's `rank_diagonal` is SQUARE-only; this is the RECTANGULAR case via the column-span route
  (`rank_eq_finrank_span_cols` + `Pi.linearIndependent_single_of_ne_zero` + `finrank_span_eq_card`):
  the nonzero columns are the distinct standard basis vectors `e_j` for `j < min t (min r c)`, span
  finrank = that count. Over an abstract field `k` (the Core `Tuple` convention). 0 sorry, ~103 LoC.

- **RUNG 2 — next.** `cascadeTuple M₀ T* : Tuple M₀ := fun s => <partialId-shaped block diag(1^{t_{s+1}},0)>`.
  Each `C_s : Matrix (Fin (M₀ s.succ))(Fin (M₀ s.castSucc)) k` (the `Tuple` factor shape). `t_{s+1}` from
  `T*` (with `t_0 := M₀ 0`).

- **RUNG 3 — the expected friction.** `submult` of cascade blocks = a single `partialId (window-min)`:
  `submult (cascadeTuple) i j = partialId (M₀ j)(M₀ i) (⨅_{i ≤ s < j} t_s)` (the running window-min of the
  cascade ranks). The dependent-`Fin` matrix-product bookkeeping over the chain. THE pp2-count-the-1s detail
  (which product = which window-min) is routed through fm3→pp2 when reached. Then `rank = window-min` by
  RUNG 1.

- **RUNG 4 — the headline.** `rankFn M₀ (cascadeTuple M₀ T*) = embedRank(T*'s 2-index pattern)` ⟹
  `T* ∈ RealizableRank M₀` (`= Set.range (rankFn M₀)`, `OrbitKostant.lean`). Anchors: (2,2,2) t=[2,1,0],
  (3,2,3) t=[3,1,0] (pattern rows = running ranks; diagonal = widths; interior = window-min) @d975c86.

## Why this is the unblock

`routeStep`'s general-M body (the committed `sorry` @`RouteMRecursion.lean:184`) needs honest branch
witnesses; the achiever-branch witness is `T* ∈ RealizableRank M₀`, which RUNG 4 supplies by CONSTRUCTION
(the cascade + the rank computation), NOT a surjectivity/`stratum_surjective` theorem. With the body filled,
`routeAtlas`/`routeMIota` go concrete and #103 (the value fold via `foldFamily_iInf_eq_half_minAdm`) closes.
The leaf classifier (#101/#108) + the branch assembly (#102 sub-2a, `routeStepBranch`) are already banked.
