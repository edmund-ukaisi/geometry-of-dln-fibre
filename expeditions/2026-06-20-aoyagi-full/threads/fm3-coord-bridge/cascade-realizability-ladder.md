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

- **RUNG 4a — DONE @8ab9a6d.** `rankPattern_cascade_prefix`: `rankPattern (cascadeTuple) 0 j =
  survivors (d_j)(d_0)(cascadeCount t 0 j)` — the running-rank ROW of the realized pattern, via
  `rank_partialId`. THE genuine non-vacuous content of the cascade side. Anchors: (2,2,2) t=[2,1,0], (3,2,3)
  t=[3,1,0], #107 double-confirmed (pp2 g228 + pp-r1realize xcheck).

- **RUNG 4b — a TAUTOLOGY, NOT the realizability (corrected, fm3 #121 anti-vacuity catch).**
  `cascadeTuple_rankFn_mem_range`: `rankFn (cascadeTuple d t) ∈ Set.range (rankFn d)` is `⟨cascadeTuple, rfl⟩`
  — VACUOUS as an achiever-realizability claim (every tuple's pattern is in `Set.range rankFn`; it says nothing
  about WHICH pattern, nothing tying it to the achiever `r*`). Kept only as the trivial membership. The genuine
  realizability is NOT this lemma — see #121.

- **THE GENUINE REALIZABILITY = #121 (NOT done, the orbit-side tie).** `rankFn (cascadeTuple t*) = r*` where
  `r*` is defined INDEPENDENTLY from `Adm` (the minimising admissible exponent's rank pattern), NOT as
  `rankFn (cascadeTuple)`. rung-4a (`rankPattern_cascade_prefix`) supplies the cascade `(0,j)` row; #121 defines
  `r*` from `Adm` and proves the equality (matching `cascadeCount t*` to `r*`'s running ranks). This is the
  `Adm ↔ RealizableRank` tie. The general routeStep arm (#103) and #116-(2) cite #121, never the rung-4b
  tautology.

- **ROADMAPPED.** The interior 2-index window `rankPattern (cascadeTuple) i j` for `i > 0` (the `i`-relative
  window-min, same `partialId_mul` iteration anchored at `i`) — for the literal full 2-index `Adm =
  RealizableRank` match. Not needed for the achiever-row.

## Why this is the unblock (with the #121 caveat)

`routeStep`'s general-M body (the committed `sorry` @`RouteMRecursion.lean`) needs honest branch witnesses; the
achiever-branch witness is that the achiever rank pattern `r*` is realized — `rankFn (cascadeTuple t*) = r*`,
which the cascade supplies (rung-4a row) ONCE #121 defines `r*` independently and proves the equality. The
rung-4b `Set.range` membership does NOT supply this (it's the tautology). With #121 + the body filled,
`routeAtlas`/`routeMIota` go concrete and #103 (the value fold via `foldFamily_iInf_eq_half_minAdm`) closes.
The leaf classifier (#101/#108) + the branch assembly (#102 sub-2a, `routeStepBranch`) are already banked.

## The remaining routeStep-body gap (the seam, NOT this thread's piece)

The cascade gives realizability on the `RealizableRank` (Core-orbit) side; the committed `PivotWitness M₀` is
on the `Adm`/`Mval` (Lambda) side. Linking them — so the dispatcher's achiever-branch `PivotWitness` is
*backed by* the cascade's realized stratum — is the **`Adm ↔ RealizableRank` bridge (#96)**, the
dispatcher-body integration seam (pp2/fm3), not the cascade construction itself. The cascade deliverable
(#116) is complete and honest as the `RealizableRank`-side witness source.
