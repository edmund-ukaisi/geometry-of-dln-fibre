# SD-7 `deeperFlagSaturatedShell_reduce` is FALSE as stated — fidelity flag (genm-sj5-satfill)

**Seat:** lean-formaliser (SD-7 fill tide). **Date:** 2026-07-15. **Branch:** `genm-sj5-satfill`
(off `origin/genm-sj5-jreqb` tip `c94e7fde0`). **Status:** SD-7 sorry NOT filled — the statement is refuted;
this is a report-only fidelity finding (escalated to controller, not silently rewritten).

## Verdict

`deeperFlagSaturatedShell_reduce` (RouteMSJDecoratedStep.lean:303) — the SD-7 statement the satcover cert
certified as a "separate, simpler, pivotDom-INDEPENDENT mechanism using NONE of hpiv/hcvg/hrange, no new
math, bounded" — is **FALSE AS STATED**. It omits an upper-bound hypothesis on `c'` (equivalently `hpiv`
or `hcT : c' < carrierThreshold M`). Its `hc'` only asserts `c' > (a·b)/2 = 0` (no upper bound), so it
claims the domination for arbitrarily large `c'`, where it fails.

## The counterexample (exact, elementary)

`M = (1,1,2,2)` (L=1, all widths ≥1), `t = 1`, `j = 0`, any `c' ∈ [1/2, 1)` (e.g. `c' = 0.7`).

All SD-7 hypotheses hold: `ht` (t=1 ≤ min(1,1)=1), `hj` (j=0 ≤ min(0,0)=0), `ht1` (1≤1), `hnd`,
`hc'` (0 = (M0−1)(M1−1)/2 < 0.7), `hjeq` (j=0 = min(M0−t,M1−t)=0). So `u = t+j = 1`, `a = M0−u = 0`,
`b = M1−u = 0` (both corners vanish — the deepest degenerate case), `peelCharge = 0`.

At `a=b=0` the integrand collapses exactly:
- `freedSchurLoss = frobSq(P·Q_p)` (C-rows empty, Γ singleton, no corank block). `P` is `1×1` (scalar `p`),
  so `= p² · frobSq(Q_p)`, `Q_p = prod(tailChain M) A'` (a single row, `tailChain (1,1,2,2) = (1,2,2)`).
- Shell is `univ` (r=0). B₁₂/C/Γ boxes are singletons (weight 1). `outerDom` forces `p ≠ 0`, `p ∈ [−1,1]`.

So, with `J := ∫_{A'∈box} frobSq(prod(1,2,2)A')^(−c') dA'` (finite, positive; `c'=0.7 < carrierThreshold(1,2,2)=1`):

    shellSpineIntegrand = ( ∫_{[−1,1]} |p|^(−2c') dp ) · J.

RHS target: `(cornerComparator (redChain 1 M) ![1] ![minAdm−1]).integral c'`, `redChain 1 (1,1,2,2) = (1,2,2)`,
`minAdm(1,2,2) = 2` (exact, via the Lean `minAdmRec`), so the Jacobian monomial is `|v|^(minAdm−1) = |v|^1`
and `decLoss = |v|²·frobSq(prod(1,2,2)z)`:

    RHS = C · ( ∫_0^1 v^(1−2c') dv ) · J.       (same box integral J: tailChain = redChain here)

Dividing by `J > 0`, the domination `LHS ≤ C·RHS` reduces to a **scalar** inequality:

    ∫_{[−1,1]} |p|^(−2c') dp   ≤   C · ∫_0^1 v^(1−2c') dv.

For `c' ∈ [1/2, 1)`: the LHS diverges (`∫_0^1 p^(−2c') dp = ∞` since `2c' ≥ 1`), the RHS is finite
(`∫_0^1 v^(1−2c') dv < ∞` since `1−2c' > −1`). So `∞ ≤ C·finite` — **no finite `C` exists. SD-7 is false.**

Exact-integer check (`/tmp` script, matches `minAdmRec`): `minAdm(1,2,2)=2`, `minAdm(1,1,2,2)=1`
(so `carrierThreshold(M) = 1/2`). Decorrelated Codex (gpt-5.6-sol, xhigh, conclusion withheld) reached
the same **NEEDS-EXTRA-HYP** verdict independently with an equivalent permitted-data obstruction
(`codex/satfill-strategy-{prompt,answer}.md`): matching the pivot singularity to the comparator monomial
requires an exponent bound (`minAdm(redChain u M) ≤ u²`-type), realizable-to-fail under only the banked
`minAdm(redChain u M) ≤ u·M2`.

## Root cause — where the satcover cert is wrong

The cert's route §5 step 2 ("drop the corank ⟹ pivot-only ⟹ direct D-A pivot-radial blow-up ⟹ the
surviving rows integrate to a finite constant `C`") hides the pivot near-singularity. The whole-block
radial blow-up (`pivotBlock_radial_blowup`) exposes radial weight `r^(u·w−1)` (here `w=M1=u`, weight
`r^(u²−1)`), but the comparator demands `|v|^(minAdm(redChain u M)−1)`. The "surviving rows integrate to
finite `C`" step is exactly the codimension balance `minAdm−1 ≤ (pivot radial exponent)`, which is NOT
free — it is precisely what `hpiv` (the pivot-admissibility criterion) supplies in the general case
(`headSplit_domination`/`pivotDom_finiteness`, both still open sorries). At `min(a,b)=0` this balance is
NOT automatic: the counterexample has `minAdm−1 = 1 > 0 = u²−1`.

The claim "SD-7 uses NONE of hpiv/hcvg/hrange" is therefore false. The FIRST-CHECK the controller flagged
(do the banked D-A lemmas accept degenerate widths a=0/b=0?) is a NON-issue — `pivotBlock_radial_blowup`
wants `NeZero(u·w)` which holds (`u≥1, w=M1≥1`); the `Fin 0` corner-collapse idioms
(`pivotUzero_freedSchurLoss`-style `frobSq[Fin 0]=0`, `matBox_volume` at `a·b=0`, probability-1 singleton
domains) are all banked. The real obstruction is the missing exponent/threshold hypothesis, one level
deeper than the width chore.

## Why the assembled architecture still (probably) holds

`deeperFlagSaturatedShell_finite` (the caller, line 327) is only ever invoked with `hcT : c' <
carrierThreshold M` in hand (and it retains `hpiv/hcvg/hrange`). It calls SD-7 WITHOUT passing any of them.
So the divergent regime (`c' ≥ carrierThreshold`) is never actually reached at runtime — but SD-7's
*statement* still claims it, so SD-7 cannot be proved sorry-free as written. For the counterexample chain,
`carrierThreshold(M) = 1/2` exactly matches the pivot convergence threshold `c' < 1/2` — i.e. adding
`hcT` (or `hpiv`) would restore truth for this case.

## Recommended repair options (controller decision — architecture-load-bearing)

1. **Add `hcT : c' < carrierThreshold M` to SD-7** (the caller has it; pass it through — one-line call-site
   edit at RouteMSJDecoratedStep.lean:345). Plausibly restores truth. Still a genuine analytic-CoV brick to
   PROVE (the codim balance), NOT a chore.
2. **Add `hpiv` (± hcvg/hrange) to SD-7** — makes it the honest `ab=0` instance of `deeperFlag_shell_le`
   (Brick D), consistent with the general dispatch; also a genuine brick.

Either way the satcover characterization ("separate simpler mechanism / pivotDom-independent / bounded /
no new math") does not survive: SD-7 is (a) false without an extra hypothesis, and (b) a genuine analytic
brick of the `pivotDom_finiteness`/`headSplit_domination` class even with one (Codex est. 400+ lines,
requiring product-map/singular-value analysis). This is NOT the bounded fill the tide was scoped for.

## Deliverables banked here
- `codex/satfill-strategy-{prompt,answer}.md` — the decorrelated strategy consult.
- This note. SD-7 sorry left INTACT (a wrong statement; must not be proved or laundered).
- Baseline `scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedStep` is green (exit 0) with the sorry.
