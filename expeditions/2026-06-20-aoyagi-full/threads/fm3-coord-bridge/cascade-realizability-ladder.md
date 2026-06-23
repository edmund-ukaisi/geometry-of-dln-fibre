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

- **RUNG 3-atom — DONE @49919f8.** `partialId_mul (r m c a b) (ha : a ≤ m) : partialId r m a * partialId m c b
  = partialId r c (min a b)` — the window-min product law (a clean `Matrix.ext` entry computation, NO
  `rank_mul_le`). The `a ≤ m` bound = the cascade's middle-dimension admissibility.

- **RUNG 2 — DONE @cd24e2c.** `cascadeTuple d t : Tuple d := fun s => partialId k (d s.succ)(d s.castSucc)(t s)`
  — TYPE-CONFIRMED in Core's left-multiply orientation (`A s : Matrix (Fin (d s.succ))(Fin (d s.castSucc))`,
  i.e. `d_{s+1}` rows × `d_s` cols, the `Tuple` factor shape). Resolves the g228-transpose subtlety. +
  `submult_cascade_single` (single-block sub-product = `A_s`).

- **RUNG 3 — DONE @b947825.** `submult_cascade_prefix (ht : ∀ p, t p ≤ d p.castSucc) j : submult (cascadeTuple)
  0 j = partialId (d j)(d 0)(cascadeCount d t 0 j)` — the prefix sub-product is a single partial-identity,
  by `Fin.induction` on `j` through `submult_succ` + `partialId_mul`. `cascadeCount` = the running `min` of
  block ranks (base `d_0`). ORIENTATION NAILED: the bound is `t_p ≤ d p.castSucc` (= `d_p`, A_p's cols = the
  product middle dim), type-checker-pinned, NOT g228's `d_{p+1}`.

- **RUNG 4 — DONE @8ab9a6d / @4b60dac.** `rankPattern_cascade_prefix`: `rankPattern (cascadeTuple) 0 j =
  survivors (d_j)(d_0)(cascadeCount 0 j)` (rung 4a, the running-rank ROW, via `rank_partialId`).
  `cascadeTuple_mem_realizableRank`: `rankFn (cascadeTuple d t) ∈ Set.range (rankFn d)` = `RealizableRank`
  (rung 4b). **Decl-first reframing:** `embedRank` is a WRAPPER and `RealizableRank = Set.range rankFn`, so the
  realizability is the `rankFn` computation — NOT an `embedRank`-convention question (de-risked the wait).
  Membership is `⟨cascadeTuple, rfl⟩`; the NON-VACUITY (named, not smuggled) is the prefix-row characterization.
  Anchors: (2,2,2) t=[2,1,0], (3,2,3) t=[3,1,0], #107 double-confirmed (pp2 g228 + pp-r1realize xcheck).

- **ROADMAPPED (named in-file, NOT needed for the achiever-row §4).** The interior 2-index window
  `rankPattern (cascadeTuple) i j` for `i > 0` (the `i`-relative window-min `survivors (d_j)(d_i)(⨅_{i≤s<j}
  t_s)`, same `partialId_mul` iteration anchored at `i`) — for the literal full `Adm = RealizableRank` 2-index
  match (#96's bridge). The achiever-row realizability above (the `(0,j)` row) is what achiever-only §4 consumes.

## Why this is the unblock

`routeStep`'s general-M body (the committed `sorry` @`RouteMRecursion.lean:184`) needs honest branch
witnesses; the achiever-branch witness is `T* ∈ RealizableRank M₀`, which RUNG 4 supplies by CONSTRUCTION
(the cascade + the rank computation), NOT a surjectivity/`stratum_surjective` theorem. With the body filled,
`routeAtlas`/`routeMIota` go concrete and #103 (the value fold via `foldFamily_iInf_eq_half_minAdm`) closes.
The leaf classifier (#101/#108) + the branch assembly (#102 sub-2a, `routeStepBranch`) are already banked.

## The remaining routeStep-body gap (the seam, NOT this thread's piece)

The cascade gives realizability on the `RealizableRank` (Core-orbit) side; the committed `PivotWitness M₀` is
on the `Adm`/`Mval` (Lambda) side. Linking them — so the dispatcher's achiever-branch `PivotWitness` is
*backed by* the cascade's realized stratum — is the **`Adm ↔ RealizableRank` bridge (#96)**, the
dispatcher-body integration seam (pp2/fm3), not the cascade construction itself. The cascade deliverable
(#116) is complete and honest as the `RealizableRank`-side witness source.
