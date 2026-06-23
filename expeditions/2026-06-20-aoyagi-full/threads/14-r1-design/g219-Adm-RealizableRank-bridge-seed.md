# §4 reachability seed — `Adm M = RealizableRank M` (the Lambda↔Core bridge), structural both directions (pp-hall, 2026-06-23, #96)

**fm3's decl-located §4 wall (g216):** the achiever reachability (g148 "resolve each layer to its T*-rank,
root-anchored by construction") is a DESIGN assertion — `stratum_surjective` is proven NOWHERE for general
`M` (only the `![1,1]` example). The gap: `Adm M` (Lambda.lean, the exponent cone via `Mval`) and
`Core.OrbitKostant.RealizableRank M = Set.range (rankFn M)` are SEPARATE combinatorial encodings, NO linking
lemma. This cert is the SEED of the bridge: a g148-level exact-algebra argument that the achiever `T*` is
always in BOTH, decorrelated input for pp-r1realize's in-reach verdict.

## The two encodings (the bridge endpoints)
- **`Adm M` (Lambda):** rank vectors `T = (t_1,…,t_L)`, `t_j = rank(C_1···C_j)`, on `{∏ = 0}` (`t_L = 0`),
  weakly-decreasing, `0 ≤ t_j ≤ min(t_{j-1}, M^{j+1})`. `Mval(M,T) = Σ_j (t_{j-1}−t_j)(M^j − t_j)`, `minAdm
  = inf' Mval`.
- **`RealizableRank M` (Core):** `Set.range (rankFn M)` — the rank patterns `rankFn M A` (`= rank(A_i···A_{j-1})`
  for `i ≤ j`) achieved by some tuple `A`. For a CHAIN, the consecutive partial-product ranks `t_j`.

## THE SEED: `Adm M = RealizableRank M` on the chain, BOTH directions, structural
**(⊆) Adm ⊆ Realizable** (the constructive realizer — every admissible `T` is achieved): the **canonical
diagonal cascade** `C_s = diag(1^{t_{s+1}}, 0)` (the first `t_{s+1}` diagonal entries `1`, rest `0`) has
running partial-product rank `rank(C_1···C_j) = t_j`. Valid (the cascade achieves `t_{s+1}`) IFF
`t_{s+1} ≤ min(t_s, M^{s+1})` — which is EXACTLY the admissibility inequality. So every admissible `T` is
realized by its cascade. **Verified (g217):** all admissible `T` realized by construction on
`(2,2,2)/(3,2,3)/(3,3,3)/(2,2,2,2)/(4,3,2)` (3/3, 3/3, 4/4, 6/6, 4/4). The achiever `T*` realized in every
case. STRUCTURAL (not instances): the cascade's running rank is `t_{s+1}` precisely when the bottleneck
admits it = admissibility — no case dependence.

**(⊇) Realizable ⊆ Adm** (every achieved rank vector is admissible): `t_j = rank(C_1···C_j)` satisfies
(a) `rank(C_1···C_j) ≤ rank(C_1···C_{j-1})` (appending a factor can't raise rank) ⟹ weakly-decreasing;
(b) `rank(C_1···C_j) ≤ rank(C_j) ≤ min(M^j, M^{j+1}) ≤ M^{j+1}` ⟹ `t_j ≤ M^{j+1}`. So any achieved `T`
satisfies Adm's inequalities. **Verified (g218):** 200 random tuples, ZERO achieved-rank-vector violations
of the Adm inequalities. STRUCTURAL: rank-monotonicity + the bottleneck.

## ⟹ §4 reachability (the achiever is realizable — the weaker, in-reach claim)
`Adm M = RealizableRank M` ⟹ the achiever `T*` (Lambda's `Mval`-minimiser, `T* ∈ Adm M`) is ALWAYS in
`RealizableRank M` (realized by its cascade) ⟹ **§4 reachability holds:** the chart path resolving each
layer to `t*_s` (the cascade ranks) reaches `T*`, the binding stratum. Crucially this needs only
**`T* ∈ Realizable`** (the achiever, via its explicit cascade), **NOT the full `stratum_surjective`** (every
`T ∈ Adm` reached) — the weaker, in-reach claim my §4 cert always flagged. (The full surjectivity is the
two-direction `Adm = Realizable`; the achiever-only needs the (⊆) cascade at `T*`.)

## For the Lean bridge (the seed → theorem, decorrelated input for pp-r1realize)
- **(⊆)** the cascade is a CONSTRUCTIVE realizer: define `cascadeTuple M T := (fun s => the diag-(t_{s+1})
  block)`, prove `rankFn M (cascadeTuple M T) = (the 2-index pattern of T)` (rank of the diagonal cascade =
  the prescribed `t_j`). The `i ≤ j` 2-index `rankFn` reads `rank(A_i···A_{j-1})`; the cascade's general
  partial-product rank is `min over the window of t`, the standard cascade fact.
- **(⊇)** rank-monotonicity (`rank(MN) ≤ rank(M)`, Mathlib) + the bottleneck (`rank ≤ min dim`).
- The 1-index (Lambda `T`) ↔ 2-index (`rankFn`) reindex: `Adm`'s `t_j` = `rankFn M A 0 j` (the partial
  product from the start); the full 2-index pattern is determined by the consecutive `t_j` for a chain
  (`rank(A_i···A_{j-1})` = the windowed cascade rank). This reindex is the bridge's bookkeeping.
- **Achiever-only suffices:** for §4 the binding `T*` is realized by `cascadeTuple M T*`; `rankFn` of it
  gives `T*`'s pattern; `T* ∈ RealizableRank` by definition (it's in the range). NO general surjectivity.

## Most likely thing to break this / the honest scope
The cascade realizes the CONSECUTIVE partial-product ranks `t_j = rank(C_1···C_j)` — for the chain this is
all that `Adm`/`Mval` use. The full 2-index `rankFn` also records `rank(A_i···A_{j-1})` for interior windows
`i > 0`; the diagonal cascade gives `min(t_i-shifted...)` there, which matches the realizable pattern but the
1-index↔2-index reindex must be stated carefully (it's determined for a chain, but the Lean bridge must spell
`rankFn M (cascade) = embedRank T`). That reindex is the bridge's load-bearing bookkeeping — the SEED here is
that the cascade realizes `T` (both `Adm`'s 1-index view and, for the achiever, the `RealizableRank` membership);
the full `Adm = RealizableRank` as 2-index sets needs the reindex lemma. For §4 (achiever-only,
`T* ∈ Realizable`), the cascade + `rankFn(cascade) = T*`-pattern suffices — lighter than the full bridge.

## Decorrelation
pp-hall exact algebra: g217 (the canonical cascade realizes every admissible `T`, 5 cases, achiever
included), g218 (the converse, rank-mono + bottleneck, structural + 200 random tuples zero violations).
Codex down env-wide (the AISI-wrapper hang) — the exact-algebra + the cascade/rank-mono structural argument
carries it; a decorrelated subagent pass is the substitute channel. Builds on g147/g148 (the achiever `T*`,
the worked cases as evidence), `Core.OrbitKostant` (`rankFn`/`RealizableRank`, the orbit↔rank-pattern half
done), `Adm`/`Mval` (Lambda.lean). The §4 wall: this is the SEED (achiever realizable via the cascade); the
full `Adm = RealizableRank` bridge theorem is the 1-index↔2-index reindex + the cascade-realizer + rank-mono
— pp-r1realize adjudicates in-reach-vs-roadmap with this seed as the constructive core.
