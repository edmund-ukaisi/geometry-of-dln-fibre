# Statement card — Validate GATE: `(1,1,1)`, `r=0`, `B=0` end-to-end

The first real end-to-end Lean result. The trivial network `H = (1,1,1)` has loss
`dlnLoss (1,1,1) 0 A = (c₁·c₂)²` (`c₁ = A 0 0 0`, `c₂ = A 1 0 0`), which is **already** normal-crossing
— no blow-up/resolution/`S1`/`L1`/`L2`/`D1`. It threads the monomial model through the one cited
`monomial_rlct` (S2) and lands on the closed form. The anti-treadmill checkpoint: confirms the
architecture assembles to the right number (`1/2`) through the single citation.

- **File:** `lean/DLNFibre/DLN/RLCT/Validate/Case111.lean` (@ commit `0bd68fe`, branch
  `expedition/aoyagi-full`).
- **Status.** sorry-free for `dlnLoss_case111`, `case111_axisRatio_inf`, `aoyagiLambda_case111`,
  `ofReal_aoyagiLambda_case111`, `case111_monomialThreshold`, `deepest111_mem_optimalSet`. One named
  bridge `sorry` (`case111_rlct_eq_monomialThreshold`, S1 content) gates the `rlctAt`-headline.
  Awaiting fidelity review.

## The sorry-free gate (the end-to-end through the one citation)

> **`case111_monomialThreshold :`**
> **`monomialThreshold 2 (![1,1]) (![0,0]) = ENNReal.ofReal (aoyagiLambda (![1,1,1]) 0)`**
>
> - **Gloss.** The weighted-monomial-integral threshold of the resolved `(1,1,1)` loss — monomial data
>   `k=(1,1)`, `h=(0,0)`, `d=2` — equals Aoyagi's closed form. Both sides are `1/2`: S2 gives
>   `⨅ⱼ (0+1)/(2·1) = 1/2`, and `aoyagiLambda (1,1,1) 0 = [−0²+0·(1+1)]/2 + ½·(Adm).inf' Mval = 0+½·1`.
> - **Proved.** The equality, unconditionally (the `(1,1,1)` monomial is genuinely singular, `k≠0`).
> - **Cited.** The threshold-half of `monomial_rlct` (S2; Watanabe/Hironaka), the one permitted external
>   citation. **`#print axioms case111_monomialThreshold` (verbatim):**
>   `[propext, Classical.choice, Quot.sound, monomial_rlct]` — the one citation + standard, no `sorryAx`.
> - **Deferred.** none (this statement is sorry-free).

## Supporting sorry-free lemmas

> **`dlnLoss_case111 (A) : dlnLoss (![1,1,1]) 0 A = (A 0 0 0 * A 1 0 0) ^ 2`**
>
> - **Gloss.** The monomial-form coercion: for `1×1` layers the loss is the bare monomial `(c₁c₂)²`.
>   Pure polynomial algebra; no citation. (`#print axioms`: standard only.) This is the form the S2
>   citation consumes. Friction (reported): `prodAux`'s recursive `Eq.mpr` casts and the non-reducing
>   `Fin (![1,1,1] s)` widths — closed via `simp [prodAux, Matrix.mul_apply]` (clears casts to
>   `1 * A 0 * A 1`) then an `erw` chain reading the single entry up to the defeq `Fin (H s) = Fin 1`.

> **`case111_axisRatio_inf : ⨅ⱼ axisRatio ((![0,0]) j) ((![1,1]) j) = (1/2 : ℝ≥0∞)`**
> — every axis ratio is `(0+1)/(2·1) = 1/2`.
>
> **`aoyagiLambda_case111 : aoyagiLambda (![1,1,1]) 0 = (1/2 : ℚ)`** — by `decide +kernel` (axiom-clean).
>
> **`deepest111_mem_optimalSet : deepest111 ∈ optimalSet (![1,1,1]) 0`** — the origin (`fun _ ↦ 0`,
> shown explicitly since `Params` is a `def` with no synthesised `Zero`) lies in the fibre.

## The `rlctAt`-headline (stated; one named bridge `sorry`)

> **`case111_rlct :`**
> **`rlctAt (![1,1,1]) (dlnLoss (![1,1,1]) 0) deepest111 = ENNReal.ofReal (aoyagiLambda (![1,1,1]) 0)`**
>
> - **Gloss.** The local RLCT of the loss at the deepest fibre point equals the closed form `= 1/2`.
> - **Proved.** Assembled by `rw` from the two pieces below — so the statement type-checks and the
>   dependency is real.
> - **Cited.** `monomial_rlct` (via `case111_monomialThreshold`).
> - **Deferred (the one bridge `sorry`).** `case111_rlct_eq_monomialThreshold :`
>   `rlctAt (![1,1,1]) (dlnLoss …) deepest111 = monomialThreshold 2 (![1,1]) (![0,0])`. **Not free even
>   here:** `rlctAt` integrates `|F|^{−c}` over a `Params`-neighbourhood of `0`; `monomialThreshold`
>   over the unit box against `|uⱼ|`-symmetrised monomials. Equating the admissible-exponent down-sets
>   is germ-locality + a box change-of-variables — the **S1** substrate (`rlct_germ_local` /
>   `rlct_unit_invariant`), not yet proven. Carried as a named `sorry` rather than folded silently into
>   a sorry-free `rlctAt`-claim. **`#print axioms case111_rlct`:**
>   `[propext, sorryAx, Classical.choice, Quot.sound, monomial_rlct]` — the citation + the one flagged
>   gap.

## TASK 1 — S2 axiom hygiene (Rung-0c FLAG 1), same commit

> The order-half of `monomial_rlct` is scoped to the singular case:
> **`… ∧ ((∃ j, k j ≠ 0) → monomialOrderAnalytic d k h = monomialOrder d k h)`**.
>
> - **Why.** When all `kⱼ = 0` (the non-singular `F(w*)≠0` chart) every `axisRatio = ⊤` ties, so the old
>   unconditional `monomialOrder = d` was a stray pole-order claim about a regular point. The
>   threshold-half stays **unconditional** — `⨅ ⊤ = ⊤` is the correct locally-nonvanishing RLCT in that
>   degenerate case. Verified: `(monomial_rlct …).1` still usable hypothesis-free; the order-conjunct now
>   demands `∃ j, k j ≠ 0`. No existing code depended on the order-half (only the axiom declared it).

## Build / audit

- `lake build` (full `DLNFibre`) green. `scripts/sorries`: **10 sorry, 0 #exit, 0 native_decide, 1
  axiom** — the 9 pre-existing skeleton rungs + 1 new named bridge `sorry`; the single S2 axiom; +0
  unintended.
- Note (single-writer): the controller-instructed wiring added one append-only import line to
  `lean/DLNFibre.lean` (`import DLNFibre.DLN.RLCT.Validate.Case111`); no existing imports reordered.
