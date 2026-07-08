# De-risk certificate — the BOUNDARY derivative-zero of `psiSplitRawGen − id` (#120 `hstep2`, Producer 1)

**Seat:** pen-and-paper (witness/obstruction hybrid — here a scoped *obstruction*: "no first-order
term survives at the boundary"). **Question (from hstep2germs11):** before a >1000-line
diffeo-triple build, verify the degree-2 vanishing `psiSplitRawGen(q) − q = o(‖q‖)`
(`HasStrictFDerivAt (psiSplitRawGen − id) 0 0`) at the ONE place it could fail — the
frame-dependent BOUNDARY reads (layers `0` / `last`) through `forcedDecodeLeft/Right` and
`Ring.inverse`. The interior/abstract vanishing was CERT-CONFIRMED (`genm-d1psidesign`, `O(‖q‖³)`);
this de-risks the boundary.

## HEADLINE — GREEN-LIGHT. The boundary derivative is ZERO. Producer 1's triple is buildable.

At `q = 0` (wstar), for the boundary layers `s ∈ {0, last}`, the per-layer read minus the identity
read `f_s(q) := psiReadBlk(q,s) − identityRead(q,s)` has **zero value and zero first derivative**:

    f_s(0) = 0   and   D f_s(0) = 0   at s = 0 and s = last.

The frame-dependent boundary decode introduces **no first-order term**. In fact `f_s` vanishes to
order `≥ 3` at the last layer and `≥ 5` at layer 0 (at least as high as the interior `O(‖q‖³)`), so
the boundary does not degrade the cert's `psiSplitRawGen − id = O(‖q‖³)`. Verified EXACTLY (exact
rational / symbolic; dual-number = exact value+first-derivative) for `L ∈ {3,4,5}`, `r ∈ {1,2}`,
`m ∈ {1,2}`, multiple seeds. Decorrelated Codex (xhigh, verdict withheld) reached the **same verdict
by the same mechanism**.

## The objects (faithful transcription of the Lean setup)

From `DeepestPsiSplitRawGen.lean` + `DeepestPsiSplitGenMoved.lean` + `DeepestPsiSplitGenLeftCol.lean`
+ `DeepestFramedProductPivot.lean` + `DeepestFramedBoundaryMove.lean`. In `r ⊕ m` block form:

* **framing** (`framedLayer`): `C_s(q) = corM + P_s · rawDev_s(q) · Q_s`, `corM = fromBlocks I_r 0 0 0`,
  `rawDev_s(q) = fromBlocks (X_s) (Y_s) (Z_s) (T_s)` the raw gauge/core reads (LINEAR in `q`,
  `rawDev_s(0)=0`). The frames `P_s, Q_s` are **`q`-INDEPENDENT** structural constants (they appear as
  `Pf`/`Qf` *parameters* in every signature — `framedLayer` never takes `q` into the frame). By the
  triangular bundle they are trivial (`= I`) except at the two boundaries:
    * layer 0:  `P_0 = fromBlocks P11 0 P21 I_m` (block-LOWER),  `Q_0 = I`;
    * last:     `P_last = I`,  `Q_last = fromBlocks Q11 Q12 0 I_m` (block-UPPER),
  with `P11 = deepBlkA_0`, `Q11 = deepBlkZ_last`-analog constant **units** at wstar (`deepBlkA_isUnit_gen`).
* **moved chain** (`movedC C (Z0edit0 C L)`): pivots fixed, up-edit all layers, one down-edit `Z_0`
  via the `deltaV0` accumulator, cores reconstructed. Previously certified (`genm-d1psidesign` §4,
  `codex_construction.py`): `movedC_s − C_s = O(‖q‖²)` per layer (interior/last `O(‖q‖³)`, layer-0 `O(‖q‖⁵)`).
* **the boundary decode** (`psiGhat`/`psiReadBlk`): `psiTargetD_s := movedC_s − corM`, and
    * interior `s`: `psiReadBlk_s = psiTargetD_s`;
    * layer 0:  `psiReadBlk_0 = forcedDecodeLeft (P_0) (psiTargetD_0)`;
    * last:     `psiReadBlk_last = forcedDecodeRight (Q_last) (psiTargetD_last)`,
  with (blocks `A,Y,Z,T` of the argument `D`; `Pinv = Ring.inverse P11`, `Qinv = Ring.inverse Q11`):
    * `forcedDecodeLeft(F,D)  = fromBlocks (Pinv·A) (Pinv·Y) (Z − P21·Pinv·A) (T − P21·Pinv·Y)`,
    * `forcedDecodeRight(Q,D) = fromBlocks (A·Qinv) (Y − A·Qinv·Q12) (Z·Qinv) (T − Z·Qinv·Q12)`.
* **identity read** (the `id` side of `psiSplitRawGen − id`): `q`'s own reads, `identityRead_s = rawDev_s(q)`
  (`psiReadBlk` packs its four blocks straight into the `X/Y/Z/core` slots via `regGaugeSlotEquiv.symm`
  / `paramsEquivFlat`; the identity map returns `q`'s literal slot values).

## The mechanism (why the frame injects no first-order term)

Two `q`-independent facts do all the work. Write `E_s := movedC_s − C_s` (the abstract per-layer edit).

1. **`forcedDecodeLeft(F)` / `forcedDecodeRight(Q)` are ℝ-LINEAR in the target `D`, with
   `q`-INDEPENDENT coefficients** (`Pinv, P21` / `Qinv, Q12` are constants — the frame corner
   `P11 = deepBlkA_0` is a *fixed* unit at wstar, so `Ring.inverse P11` is a *constant*, not a
   `q`-varying inverse). This is the crux the mission flagged: *the frame factors are `q`-independent
   constants, so they contribute no first-order term.*

2. **Identity-read recovery `(★)`** — the forced decode is a genuine inverse of the boundary framing:

        forcedDecodeLeft (P_0)  (P_0 · R)  = R          (uses Q_0 = I, and Pinv·P11 = 1)
        forcedDecodeRight (Q_last) (R · Q_last) = R      (uses P_last = I, and Q11·Qinv = 1)

   for a generic block `R`. Since `C_0 − corM = P_0 · rawDev_0` (as `Q_0 = I`) and
   `C_last − corM = rawDev_last · Q_last` (as `P_last = I`), `(★)` gives
   `forcedDecode(frame_s)(C_s − corM) = rawDev_s = identityRead_s` **identically** (not merely to
   first order).

Combining (1) + (2) by linearity, at each boundary layer:

    f_s = forcedDecode(frame_s)(movedC_s − corM) − rawDev_s
        = forcedDecode(frame_s)(movedC_s − corM) − forcedDecode(frame_s)(C_s − corM)     [by (★)]
        = forcedDecode(frame_s)(E_s).                                                    [by (1)]

A **fixed linear map applied to an `O(‖q‖²)` quantity is `O(‖q‖²)`** — so `D f_s(0) = 0` at the
boundary, and `f_s` inherits `E_s`'s order (last `O(‖q‖³)`, layer-0 `O(‖q‖⁵)`). The interior case is
`f_s = movedC_s − C_s = E_s` directly. No boundary exception.

## Exact evidence (three independent methods; all exact-rational / symbolic — no float load-bearing)

`sympy/` (run under `python3`):

| check | file | result |
|---|---|---|
| value + FIRST DERIVATIVE (dual numbers `ε²=0`, EXACT) at every layer | `boundary_deriv_dual.py` | `f_s(0)=0` **and** `Df_s(0)=0` at boundary+interior, ALL cases `L∈{3,4,5} r∈{1,2} m∈{1,2}` → **GREEN** |
| leading `ε`-order (truncated series, Neumann inverse) | `boundary_order.py` | layer0 `≥5`, last `3`, interior `3` → boundary ≥ interior; corroborates `O(‖q‖³)` |
| crux identity-read recovery `(★)`, FULLY SYMBOLIC generic `R` + generic invertible corners | `crux_identity.py` | `forcedDecodeLeft(P0,P0·R)=R` & `forcedDecodeRight(Qlast,R·Qlast)=R` : True, `r,m ≤ 2` |
| full-symbolic-`ε` reference cross-check (slow; small cases) | `boundary_deriv.py` | agrees with dual-number result |

**Falsification probe** (in `boundary_deriv_dual.py`): if the *other-side* boundary frame were
wrongly non-trivial (`Q_0 ≠ I` at layer 0, `P_last ≠ I` at last), the single-sided `forcedDecode`
would miss it and `Df_s(0) ≠ 0` at BOTH boundaries — confirmed to break. This shows the model is
faithful and SENSITIVE (the GREEN is not a degenerate artifact), and pins the exact hypothesis the
green-light rests on: **exactly one side of each boundary frame is non-trivial, and the matching
single-sided `forcedDecode` inverts it.**

## Decorrelated Codex (xhigh) — full agreement, same mechanism (verdict withheld)

`codex/boundary-prompt.md` / `codex/boundary-answer.md` (setup + question given; my empirical results
and my GREEN verdict WITHHELD).

* Independent verdict: **Q1 yes (value 0), Q2 yes (first derivative 0) at BOTH boundary layers.**
* Independently reconstructed the mechanism: "boundary decoders are linear maps in `D`, coefficients
  `Pinv,P21,Qinv,Q12` constant in `q`"; `f_0 = forcedDecodeLeft(P_0, E_0)`,
  `f_last = forcedDecodeRight(Q_last, E_last)`, "fixed linear maps preserve vanishing order ⟹ no
  frame-created first-order term."
* Independently flagged the SAME failure mode (secret non-trivial opposite-side frame) and proposed
  the SAME cheapest check as `(★)` (`forcedDecodeLeft(P0,P0·R)−R=0`), which I then verified symbolically.
* Correct caveat it raised (registered): the "leading order = 3 / 5" is a *lower bound* derivable from
  the big-O facts; the truncated-series run shows the last-layer nonzero term does appear at order 3
  (so `O(‖q‖³)` is *sharp* at the last layer) and layer 0 vanishes beyond truncation (order `≥ 5`).

## Scope, and the most likely thing to break it (for the formaliser, not the math)

**Load-bearing hypotheses (all already banked in the Lean setup):**
1. The frames `Pf`/`Qf` are `q`-independent (structural, evaluated at wstar) — true by construction
   (`framedParamsPivot` takes them as parameters). *If a downstream caller instantiated `Pf`/`Qf` as
   `q`-dependent, this de-risk would not apply* — the formaliser should keep them `q`-fixed.
2. Frame corners `P11 = deepBlkA_0`, `Q11` are UNITS at wstar (`deepBlkA_isUnit_gen` /
   `deepBlk_boundary_gen`) — so `Ring.inverse` is a genuine two-sided inverse and `(★)` holds.
3. Exactly one side non-trivial per boundary (`Q_0 = I`, `P_last = I`). The move identity
   (`DeepestFramedBoundaryMove`) already rests on this; the falsification probe shows it is essential.
4. `movedC_s − C_s = O(‖q‖²)` per layer — the banked `genm-d1psidesign` result (re-confirmed here,
   per-layer, at the boundary layers).

**Most likely to break it (formalisation, not math):** the algebraic `(★)` step needs `Pinv·P11 = 1`
(left inverse) for the layer-0 recovery and `Q11·Qinv = 1` (right inverse) for the last layer, whereas
`DeepestFramedBoundaryMove`'s banked identities are stated with the *other* one-sided inverse
(`P11·Pinv = 1`, `Qinv·Q11 = 1`). Both hold once `P11`/`Q11` are units (two-sided), but the formaliser
must invoke the *two-sided* unit (not just the one-sided lemma already on the shelf) at the
identity-read recovery. This is the one spot where the direction of the inverse matters.

**Next construction/consult that would settle the open part:** the Lean lemma `(★)` —
`forcedDecodeLeft (P_0) ((P_0) · R) = R` and its right mirror — as a two-sided-unit corollary of the
banked `fromBlocks_lowerFrame_mul_forcedDecode` / `fromBlocks_rightUpper_mul_forcedDecode`. Once
`(★)` + the banked `movedC − C = O(‖q‖²)` are in hand, the boundary `HasStrictFDerivAt (psiReadBlk_s −
identityRead_s) 0 0` is `forcedDecode(frame_s)` (a CLM) applied to a strict-derivative-zero germ.

## GREEN-LIGHT (one line for the Producer-1 formaliser)

**BUILD IT.** `HasStrictFDerivAt (psiSplitRawGen − id) 0 0` holds INCLUDING the boundary layers:
`f_s = forcedDecode(frame_s)(movedC_s − C_s)`, a `q`-independent linear map applied to an `O(‖q‖²)`
germ, so the boundary contributes no first-order term (last `O(‖q‖³)`, layer-0 `O(‖q‖⁵)`). The one
formalisation watch-point is invoking the *two-sided* unit of `P11`/`Q11` at the identity-read
recovery `(★)`.
