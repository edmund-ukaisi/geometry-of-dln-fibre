# #108(b) RECONCILED + PROVEN — the two leaf notions; ⊤ terminal + [4,3] at branches = 3/2 (pp-hall, 2026-06-23)

**The leaf-value flip-flopped 3× because TWO distinct "leaf" notions were conflated.** fm3's decl finding
(`case222_routeStep_value` uses `codimsOf222 := fun _ => [4,3]`, NOT `leafMonoData-⊤`) is the key. This cert
RECONCILES them and PROVES the (2,2,2) actual-recursion folds to 3/2 — the controller's demanded proof.

## THE TWO LEAF NOTIONS (the confusion source, now separated)
1. **The value-validation ABSTRACT leaf** (`case222_routeStep_value`, `codimsOf222 := fun _ => [4,3]`): a
   one-element (`Unit`) leaf FAMILY whose single leaf = the END of the achiever PATH, carrying the
   ACCUMULATED branch-divisors `[4,3]`. `⨅ = monomialThreshold(foldDivisors [4,3]) = min(axisRatio 3 1,
   axisRatio 2 1) = min(2, 3/2) = 3/2`. This is the PATH (with its accumulated divisors), NOT the terminal.
2. **The recursion TERMINAL** (`leafStep`/`leafMonoData 0`, threshold ⊤): the degenerate base case
   (`minAdm=0 ⟺ ∃M_s=0`), reached when the `schurState` descent hits a width-0. Appends NOTHING (⊤).

These are DIFFERENT objects: (1) = the whole path bearing `[4,3]`; (2) = the path's end-marker bearing `[]`.

## THE ACTUAL RECURSION ON (2,2,2) — TRACED + PROVEN (g237)
`schurState M = (M_0−1, M_1−1, M_{≥2})` (banked rank-1). Recursion (branch while `minAdm M > 0`, terminal
at `minAdm M = 0`):
- **step 1: node `(2,2,2)`** (`minAdm=3 > 0`, BRANCH) → blow up, APPEND divisor codim
  `Mval((2,2,2),(0,0)) = 4` → `schurState → (1,1,2)`.
- **step 2: node `(1,1,2)`** (`minAdm=1 > 0`, BRANCH) → blow up, APPEND divisor codim
  `Mval((2,2,2),(1,0)) = 3` (= minAdm, the binding/achiever) → `schurState → (0,0,2)`.
- **step 3: node `(0,0,2)`** (`minAdm=0`, `∃M_s=0` → TERMINAL leaf, ⊤, APPENDS NOTHING).

So `codimsOf(achiever path) = [4, 3]` (the 2 BRANCH-node divisors), the terminal `(0,0,2)` appends `[]`.
`foldDivisors([4,3] ++ []) = foldDivisors([4,3])`, `ratioMinFold = min(4/2, 3/2) = 3/2 = lambdaCore(2,2,2) =
½·minAdm = 3/2`. **PROVEN: the actual recursion's accumulated codims = `[4,3]` = `codimsOf222`, folding to
3/2 with the ⊤ terminal contributing nothing.** ✓ (The flip-flop's "if ⊤ gave 3/2, why is ⊤ wrong?" DISSOLVES:
⊤ never "gave 3/2" — the [4,3] from the BRANCH nodes gave 3/2; the ⊤ terminal is the end-marker, orthogonal.)

## THE PROVEN ANSWERS (controller's 3)
**1. PRECISE (core-vs-whole + leaf fold-contribution):** `routeStep`/`foldFamily` computes the CORE
(`⨅ monomialThreshold = ½·minAdm = lambdaCore`). The divisors ACCUMULATE at the BRANCH nodes (via
`appendDivisor`, codim `= Mval(M₀, T_node)`); the recursion TERMINAL (`leafMonoData 0`, ⊤) appends NO
divisor. `nReg/2` is L2's regular shift OUTSIDE (`aoyagiLambda = nReg/2 + lambdaCore`). `#70` = the WHOLE
`rlctAt = nReg/2` at a degenerate ROOT (the headline case-split), NOT a per-leaf fold-contribution.

**2. RECONCILE = 3/2 (the actual recursion with the degenerate terminal):** traced above. `(2,2,2) →
(1,1,2) → (0,0,2)`: branches append `[4,3]`, terminal `(0,0,2)` appends `[]`; `foldDivisors([4,3]) = 3/2`.
The accumulated codims ARE `[4,3]` (matching `codimsOf222`) — no contradiction. The abstract one-leaf
`[4,3]` IS the actual path's accumulated branch-divisors.

**3. COMPOSE-CONSISTENCY (no double-count, no missing-shift, on (2,2,2)):** leaf-⊤ (terminal, `[]`) +
branch-`[4,3]` (the 2 C1 nodes) → `foldDivisors([4,3]) = 3/2 = lambdaCore`. L2 adds `nReg/2` OUTSIDE
(`(2,2,2)` r=1: `nReg = 1·(2+2−1) = 3`, `aoyagiLambda = 3/2 + 3/2 = 3`). `#70` NOT invoked (the ROOT `(2,2,2)`
is non-degenerate, all `M_s ≥ 1`). NO double-count: `nReg/2` once (L2), terminal ⊤ (`[]`), branch divisors
give `lambdaCore`. NO missing-shift: L2's `nReg/2` carries the regular part for the non-degenerate root.

## THE PINNED SPEC (for rs-grind / #103)
- `routeStep`'s value = CORE (`⨅ monomialThreshold = lambdaCore`); divisors APPEND at BRANCH nodes (`appendDivisor`,
  codim `= Mval(M₀, T_node)`); the recursion TERMINAL = `leafMonoData 0` (⊤, appends NOTHING) — fm3's choice RIGHT.
- The (2,2,2) `codimsOf = [4,3]` is the ACCUMULATED branch-divisors (NOT the terminal); `case222_routeStep_value`'s
  one-leaf `[4,3]` matches the actual recursion's achiever path.
- `#70` = degenerate-ROOT handler (headline case-split, `rlctAt = nReg/2`), NEVER a mid-recursion leaf fold-contribution.
- `nReg/2` = L2's spectator shift, OUTSIDE `routeStep`. Composition: non-deg root `→ nReg/2 + lambdaCore`;
  deg root `→ #70 (nReg/2)`. No double-count.

So: the ⊤ TERMINAL is RIGHT (it's the path end-marker, appends `[]`); the `[4,3]` are the BRANCH-node divisors
(accumulated via `appendDivisor`); the value folds to `lambdaCore = 3/2`. The flip-flop conflated "the
[4,3]-bearing leaf" (= the whole path) with "the ⊤ terminal" (= the end-marker) — they are CONSISTENT, not
contradictory. PROVEN on the actual (2,2,2) recursion.

## Decorrelation
pp-hall exact algebra (g237: the actual (2,2,2) recursion trace — 2 branch nodes appending [4,3], the ⊤
terminal (0,0,2) appending []; foldDivisors([4,3]) = 3/2 = lambdaCore). Builds on g233 (the leaf test =
degenerate boundary), g236 (the CORE-vs-WHOLE accounting), g195/g228 (the [4,3] codimsOf + rankFn), g204
(#70 deg-root), RouteMState (foldDivisors/appendDivisor, banked). The reconciliation: the abstract-[4,3]
(validation) = the actual-recursion's branch-accumulated divisors; the ⊤ terminal is the orthogonal
end-marker. No flip-flop — two notions, one consistent fold.
