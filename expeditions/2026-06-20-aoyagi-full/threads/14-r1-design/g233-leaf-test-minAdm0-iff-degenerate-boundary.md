# #108 BASE CASE adjudication — `minAdm M = 0 ⟺ ∃s M_s=0` (the degenerate boundary); the leaf VALUE is #70, NOT ½·minAdm (pp-hall, 2026-06-23)

**Controller-elevated #108 (gates #103 dispatch):** is rs-grind's leaf test `isLeafNode M := minAdm M = 0`
EXACT + non-vacuous? **Verdict: the test is EXACT and decidable, BUT it detects the DEGENERATE BOUNDARY
(`∃s, M_s=0`), not a clean interior leaf — and at such a node the leaf VALUE must route through #70 (direct
Morse, `rlctAt = nReg/2`), NOT the additive `½·minAdm = 0` (the ⊤-trap).** This is the "too-weak base case →
wrong value" risk #108 was elevated to catch — the test is right, the naive VALUE-handling is wrong.

## THE EXACT CHARACTERIZATION (verified, 1360 M, zero mismatches)
**`minAdm M = 0 ⟺ ∃ s, M_s = 0`** (`g232`, exhaustive L=1..4, widths 0..3, zero counterexamples).
- **(⇐)** some `M_s = 0`: the width-0 layer bottlenecks the chain through rank 0 (`t_s ≤ M_s = 0` forces
  `t_s = 0`); a zero-codim admissible path exists (saturate/stay to 0). `minAdm = 0`.
- **(⇒)** all `M_s ≥ 1`: every admissible `t` (weakly-decr, `t_L = 0`) has a positive summand — the minimal
  (the rank-1 incidence `(1,0,…)`) has `Mval = (M_0−1)(M_1−1) + … > 0` since all `M_s ≥ 1`. `minAdm > 0`.

**No `minAdm=0` node has all `M_s ≥ 1`** (verified L=2,3): the genuine interior leaf NEVER has `minAdm=0`.

## THE CANDIDATE COMPARISON (which "geometric leaf" RHS is right)
- **(a) achiever `T*` has `Mval=0`** = `minAdm=0` (tautological, `T* = argmin`). ✓ = the test.
- **(c) `IsUnit residual core`** ⟺ the minimal stratum is codim-0 ⟺ `minAdm=0`. ⟺ (a). ✓
- **(b) schurState-bottomed (`M_0=0` or `M_1=0`)** ≠ `minAdm=0` — **WRONG**. Counterexample `(2,2,0)`:
  `minAdm=0` (leaf) but `M_0=M_1=2 ≠ 0` (schurState still applies). The boundary is **ANY** `M_s=0`
  (incl interior `M_2=0`), not just the first two pivots. **Do NOT use (b) as the leaf RHS.**

So the exact RHS is `minAdm M = 0 ⟺ ∃s, M_s=0` (= (a) = (c), and the geometric meaning is "the chain
bottlenecks through a width-0 layer = the degenerate boundary").

## THE ⊤-TRAP (the load-bearing correction — the leaf VALUE)
At a `minAdm=0` node, `lambdaCore = ½·minAdm = 0`. BUT `dlnLoss M 0` at such a node is ≡ 0 (a width-0 layer
makes the product vacuously 0 — e.g. `(2,2,0)`: `C_2` is `2×0`, `C_1 C_2 = 0`), so `rlctAtOn(dlnLoss M 0) =
⊤` (the team's `sSup` convention). **`½·minAdm = 0 ≠ ⊤`** — the #70 ⊤-trap. So:
- the leaf TEST `minAdm=0` is EXACT (detects the degenerate-boundary base case ✓);
- but the leaf VALUE is **NOT** `½·minAdm = 0` — it must route through **#70** (the direct-Morse
  `rlctAt(deepest) = nReg/2`, NOT `rlctAtOn(dlnLoss M 0)`, which is the ⊤-trap). My g204 cert handles
  exactly this (the degenerate-boundary `rlctAt = nReg/2 = aoyagiLambda` via the Gauss-Newton Hessian +
  smooth-transversal, avoiding the `rlctAtOn(core)=⊤` route).

## NON-VACUITY (confirmed)
Branches (`minAdm>0`, all `M_s≥1`): `(2,2,2)→3`, `(1,1,1)→1`, `(3,2,3)→5`, `(2,1,2)→2`. Leaves
(`minAdm=0`, `∃M_s=0`): `(2,2,0)`, `(0,0,2)`, `(2,0,2)`, `(1,1,0)`, `(2,0,0)`, … Not always/never.

## What rs-grind pins (the #103 gate)
- `isLeafNode M := minAdm M = 0` is the RIGHT decidable test, and `minAdm M = 0 ↔ ∃s, M_s = 0` is the
  exact characterization (a clean Lean lemma: `Finset.inf' Mval = 0 ↔ ∃ s, M s = 0`). Use THIS as the gate.
- **The leaf VALUE must be the #70 degenerate-boundary handler** (`rlctAt = nReg/2`, g204's direct-Morse),
  NOT `½·minAdm=0`. The recursion on the bulk (all `M_s≥1`) descends via schurState until a width hits 0
  (the degenerate boundary), THEN the leaf is the #70 case. So #103's leaf arm = the #70 wrapper, not a
  trivial 0-value.
- **Do NOT use (b)** (M_0=0 or M_1=0) — it misses interior-`M_s=0` leaves.

## Most likely thing to break this
The recursion must actually REACH a width-0 (the degenerate boundary) as its base case — the schurState
descent `(M_0−1, M_1−1, M_{≥2})` decrements `M_0, M_1` each step, so it hits `M_0=0` or `M_1=0` in finite
steps (terminates, ΣM↓). At that point `minAdm=0` fires, the leaf is the #70 case. The interior layers
`M_{≥2}` only hit 0 if a C5/deeper node decrements them — but the leaf test `minAdm=0` catches ANY `M_s=0`,
so it's robust to which layer bottoms out first. The one care: the recursion's leaf VALUE wiring must call
#70 (the degenerate-boundary `nReg/2`), not report `½·minAdm = 0` — that's the classifier-correctness gate
#108 was elevated to pin.

## Decorrelation
pp-hall exact algebra: g229 (the leaf cases), g230 (the DP characterization + candidate (b) refuted), g231
(the ⊤-trap: `dlnLoss(2,2,0) 0 ≡ 0`, `rlctAtOn=⊤≠½·minAdm`), g232 (the `minAdm=0 ⟺ ∃M_s=0` exhaustive
verification, 1360 M, zero mismatches + the structural reason). Codex down env-wide — exact-algebra +
the structural (⇐)/(⇒) argument carries it. Ties to g204 (#70, the degenerate-boundary `rlctAt = nReg/2`,
the leaf VALUE handler). The #108 finding: the leaf TEST is exact (= degenerate boundary), but the leaf
VALUE is #70, NOT `½·minAdm` — surfaced NOW, before #103 wires it.
