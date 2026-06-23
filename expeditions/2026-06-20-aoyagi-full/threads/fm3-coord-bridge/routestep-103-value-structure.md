# #103 value-structure: how `routeAtlas`'s `⨅` relates to `routeStep`'s per-node codims

The precise target for #103 (assemble `routeStep` + wire the value fold), traced from the committed
`routeAtlas` recursion (`RouteMRecursion.lean:193`). Holds regardless of the (A)/(B) dispatcher reading.

## The recursion's value accumulation (decl-traced)

`routeAtlas M₀ M = WellFounded.fix` on `chainRel`:
- `routeStep M₀ M = .leaf md` ⟹ one chart, `data = md`.
- `routeStep M₀ M = .branch cells split codim witness` ⟹ `ι = Σ c, (child c).ι` where
  `child c = routeAtlas M₀ (split c).red` (recurse on the reduced chain), and
  `data x = ((child x.1).data x.2).appendDivisor (codim x.1)`.

So a leaf at the bottom of the descent has `data = foldr appendDivisor (leaf-base) [codims along its
root→leaf path]`. With the leaf arm `= leafMonoData 0` (the `d = 0` base, threshold `⊤`):
`data i = MonoData.foldDivisors (pathCodims i)` and
`monomialThreshold (data i) = ratioMinFold (pathCodims i) = ⨅ over the path of (codim / 2)`.

The headline value: `⨅ over routeMIota M₀ of monomialThreshold (data i) = min over all root→leaf paths of
(min over that path of codim/2)`.

## The value target ⟹ what the per-node codims must satisfy

`⨅ = ½·minAdm(M₀)` requires (exactly `foldFamily_iInf_eq_half_minAdm`'s hypotheses, banked):
- **(C≥)** every codim on every path carries a `PivotWitness M₀` (an admissible `T ∈ Adm M₀` with
  `codim = (Mval M₀ T).toNat`) ⟹ each `codim ≥ minAdm(M₀)` (`minAdm_le_Mval_toNat`) ⟹ each `codim/2 ≥
  ½·minAdm`, so every path threshold `≥ ½·minAdm`.
- **(C=∃)** ONE achiever leaf `i₀` whose path contains a codim `= minAdm(M₀)` ⟹ its path threshold `=
  ½·minAdm`.

So the dispatcher's per-node codims are **root-anchored `Mval M₀ T` values down the `schurState` descent**,
with the achiever path threading `T*` (the `minAdm` minimiser). The codims are NOT all `minAdm` — they are
the node's genuine pivot codims (each `≥ minAdm`), and the path-MIN on the achiever = `minAdm`.

## The (A)/(B) fork (awaiting fm3's confirm)

- **(A)** the general rank-pattern read: emit, for arbitrary `M`, the genuine per-cell admissible-`Mval`
  codims + the achiever — the full general dispatcher (hard).
- **(B)** cover-discharged: since the cover (#104, `IsRouteMCover`) is the honesty-gate (it catches a
  fabricated `(d,k,h)` via `cover_le`/`cover_ge_div`'s genuine `pivotBlowupOn` CoV), the dispatcher may emit
  a branch threading ONLY the achiever `T*`'s root-anchored codim sequence down the descent (the `i₀` path),
  with the C≥ witnesses admissible-by-construction. The value `½·minAdm` then follows by `foldFamily_iInf`,
  and the cover enforces geometric genuineness. The `(2,2,2)` anchor (`Case222RouteStep`, codimsOf `[4,3]`,
  achiever `T*=(1,0)`, `3=minAdm`) is the (B)-shape worked instance.

Under (B), #103 is tractable now: leaf-first dispatch + an achiever-`T*`-threaded branch (codims root-anchored
to `M₀`, achiever path = `T*`'s sequence) + `foldFamily_iInf` over `routeMIota`. The cascade realizability
(#116, rankPattern_cascade_prefix) is the (0,j)-row computation; the genuine r* realizability tie is #121, consumed in the COVER (#104), not here.
