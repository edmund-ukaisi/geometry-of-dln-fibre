# #108(b) leaf VALUE + CORE-vs-WHOLE accounting — CORE; ⊤ terminal; no double-count (pp-hall, 2026-06-23)

**Controller-expanded #108 (gates #103 fold):** the leaf TEST is exact (`minAdm M=0 ⟺ ∃s M_s=0`, g233); now
the leaf VALUE + the CORE-vs-WHOLE accounting the ⊤-trap exposed. fm3's candidate: CORE (leaf value
contributes via the accumulated divisors, terminal ⊤; `nReg/2` is L2's shift outside). **Confirmed, with the
exact spec: routeStep computes the CORE; the degenerate-boundary terminal leaf is `leafMonoData` (threshold
⊤, NON-binding); the binding is the accumulated minAdm-codim divisor ALONG the path; `nReg/2` enters once in
L2 (outside); #70 is for a degenerate ROOT only — no double-count.**

## Q1 — CORE or WHOLE: CORE (confirm fm3)
`routeStep`'s `⨅ monomialThreshold = ½·minAdm = lambdaCore` — the B=0 CORE (the reduced widths `M`). The
`nReg/2` regular shift is L2's `product_reduction` OUTSIDE: `aoyagiLambda = nReg/2 + lambdaCore` (g212: the
regulars are spectator axes, `nReg/2` the L2 normal-form shift, NOT in `routeStep`). So `routeStep` computes
the CORE; it does NOT compute `nReg/2`. ✓

## Q2 — the leaf VALUE: ⊤ terminal, NON-binding (fm3's leafMonoData 0 is RIGHT)
The recursion on a NON-degenerate root (all `M_s≥1`) descends via `schurState` (decrementing `M_0, M_1`) until
a width hits 0 — the degenerate-boundary terminal (`∃M_s=0`, `minAdm=0`). E.g. `(2,2,2)→(1,1,2)→(0,0,2)`.

**The ⨅ is over LEAF PATHS of `foldDivisors(codimsOf path)`, where `codimsOf` = the C1/C5-DIVISOR codims
ACCUMULATED ALONG the path (the blow-up exceptional divisors), NOT the terminal leaf's own `½·minAdm`.** The
terminal leaf (`(0,0,2)`) is a UNIT (`leafMonoData`, threshold ⊤) — it does NOT contribute a binding value;
the path's threshold = `min` over the accumulated divisor codims. **CRITICAL: a 0-BINDING leaf would wrongly
force the root `⨅` to 0; the ⊤ terminal + the accumulated divisors gives the right `½·minAdm`.** So the
`½·minAdm=0` "leaf core-value" is NOT what enters the `⨅` — it's the degenerate sub-core's value (the unit
residual after the path's blow-ups), correctly carried as the ⊤ terminal.

**Verified end-to-end (g235):** the `(2,2,2)` achiever path `codimsOf = [4, 3]` (the C1-divisor codims
`Mval((2,2,2),(0,0))=4`, `Mval((2,2,2),(1,0))=3=minAdm`); `foldDivisors → ratioMinFold = min(4/2, 3/2) = 3/2
= lambdaCore`. The terminal `(0,0,2)` = ⊤ (non-binding); the binding is the codim-3 divisor (= minAdm) along
the path. ⊤ terminal + accumulated divisors = 3/2 ✓.

So: **rs-grind's `leafMonoData 0` (threshold ⊤) IS the right terminal**, PROVIDED the divisor codims are
accumulated via `appendDivisor` at each C1/C5 node (which they are). The leaf does NOT bind the ⨅ to 0; the
path's binding minAdm-codim divisor binds. The exact leaf `(d,k,h)` at the degenerate-boundary terminal =
`leafMonoData 0` (`d` = the ambient core dim, `k≡0`, `h≡0`, threshold ⊤).

## Q3 — composition with L2's `nReg/2` + #70 (no double-count, no missing shift)
- **`routeStep` (CORE):** `⨅ = lambdaCore = ½·minAdm` — the divisor-min, terminal ⊤. For a NON-degenerate root.
- **L2 (the regular shift):** adds `nReg/2` OUTSIDE: `aoyagiLambda = nReg/2 + lambdaCore`. The regulars are
  spectator axes (g212); `nReg/2` enters ONCE, in L2's `product_reduction`.
- **#70 (the degenerate-boundary WHOLE):** `rlctAt(deepest) = nReg/2` — used ONLY when the ROOT is degenerate
  (`∃M_s=0` AT THE ROOT, the headline case-split). NOT for a degenerate-boundary leaf reached MID-recursion
  (that's the ⊤ terminal of the CORE fold, not #70). #70's `nReg/2` = the WHOLE rlctAt at a degenerate root
  (where `lambdaCore=0`, the core empty); it's the headline's degenerate branch, separate from `routeStep`.

**NO double-count:** `nReg/2` enters once (L2, the spectator shift); the mid-recursion degenerate-boundary
leaf terminal is ⊤ (no value); the divisors give `lambdaCore`. **NO missing shift:** L2 carries `nReg/2` for
the non-degenerate root; #70 carries the whole `nReg/2` for the degenerate root (where `routeStep`/L2's CORE
would ⊤-trap). The headline case-splits: non-degenerate root → `nReg/2 + lambdaCore` (L2 + `routeStep`-CORE);
degenerate root → `nReg/2` (#70).

## What rs-grind pins (#103)
1. `routeStep` computes the CORE (`⨅ monomialThreshold = lambdaCore = ½·minAdm`); `nReg/2` is L2's, outside.
2. The leaf ARM (degenerate-boundary terminal, `minAdm=0`) = `leafMonoData 0` (threshold ⊤, NON-binding) —
   fm3's choice is RIGHT. The divisors accumulated along the path (via `appendDivisor` at C1/C5 nodes) carry
   the value; the terminal does NOT bind. (NOT the `½·minAdm=0` as a binding leaf — that would force ⨅=0.)
3. #70 is the degenerate-ROOT handler (headline case-split), NOT the mid-recursion leaf. No double-count.

## Decorrelation
pp-hall exact algebra (g234: CORE-vs-WHOLE + the ⊤-terminal accounting; g235: the (2,2,2) end-to-end fold =
3/2 with ⊤ terminal). Codex down env-wide — the value-structure argument carries it. Ties to g233 (the leaf
test = degenerate boundary), g204 (#70, the degenerate-ROOT `nReg/2`), g212 (the CORE headline / regulars-as-
spectators), the foldFamily/appendDivisor value-side (RouteMState, banked). The accounting: `routeStep` CORE
(divisor-min, ⊤ terminal) + L2 `nReg/2` outside + #70 for the degenerate root — no double-count, no ⊤-trap.
