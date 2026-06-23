# V4 minAdm-min identity: numerical adjudication (2026-06-23)

Adjudicating the cover's V4 identity `hmin` for the min-spine, over the literal Lean
`Mval`/`Adm`/`inf'` defs (sympy, `v4-minadm-refutation.py`, 1360 nodes L=1..4, widths 1..4).

## VERDICT: the sketched `n = M(Fin.last L)` is FALSE.

`minAdmZ M = min(M₀·M₁, M(Fin.last L) + minAdmZ(schurStateRed M))` — **FAILS 760/1360**.
- **12 UNSOUND undershoots** (`min < true minAdm`): all L=1, e.g. `(2,1)`: `minAdm=2`, `min(2, 1+0)=1`.
- **748 overshoots** (`n = M_last` too big): e.g. `(3,3,3,3)`: `minAdm=6`, `min(9, 3+4)=7`;
  `(2,3,2,4)`: `minAdm=4`, `min(6, 4+2)=6`.

## The TRUE n: `n := nRegOf M = minAdmZ M − minAdmZ(child)`.

`minAdmZ M = min(M₀·M₁, nRegOf M + minAdmZ(schurStateRed M))` — **0 failures, ALL L (incl L=1)**.
The `n_needed` across every overshoot is exactly `nRegOf` (= `minAdm M − minAdm(child)`), NOT `M_last`.

But this is **vacuous/circular at the value level** (`nRegOf` is defined via `minAdm M`): the descent
branch `nRegOf + minAdmZ(child) = minAdmZ M` identically, so `min(M₀M₁, minAdmZ M) = minAdmZ M` by
**F2** (`minAdmZ M ≤ M₀·M₁`, verified 0 failures all nodes; = the proven `lambdaCore_le_front_mul`).

## Conclusion (confirms the prior pen-and-paper finding)

The value-level min is VACUOUS — the genuine SELECTING min is GEOMETRIC, with `n` = the RAW ∑Erow²
smooth-block dim in the cover integrand, which is **NOT `M(Fin.last L)`** (refuted) and **NOT the
regularized `nRegOf`** (circular). The cover's `hstep_min` and the value `hmin` must use a CONSISTENT
`n`; the reconciliation `min{mk/2, n_raw/2 + R/2} = (nReg+R)/2` (cert-104b V8) is a5f5ceb1's geometric
fact relating the raw `n` to `nRegOf` — NOT a standalone combinatorial identity provable against
`M(Fin.last L)`.

## The honest composable lemma (n-agnostic)

`minAdmZ_min_of_reconcile`: GIVEN `n + minAdmZ(child) = minAdmZ M` (the V8 reconciliation, a hypothesis
the cover supplies) + F2 (`minAdmZ M ≤ M₀·M₁`, proven), conclude
`minAdmZ M = min(M₀·M₁, n + minAdmZ(child))`. This is the `hmin` the spine needs, `n`-agnostic — it
composes with whatever `n` a5f5ceb1's cover actually produces (the cover proves the reconciliation).
