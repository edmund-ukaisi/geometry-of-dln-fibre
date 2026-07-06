# Statement card — general-`L` R1-UPPER `(S,J)` resolution SKELETON (`sjfound` foundation tide)

**Status:** sorry-free for the CLOSED pieces + the recursion wrapper; the genuinely-new analytic
content is confined to clearly-named sorries. Green in the full import closure of
`RouteMSJResolution` (8295 jobs). On `origin/genm-sjresolution` (base
`origin/expedition/aoyagi-full @3d533215`), module commit `d74066a1`. **NOT yet wired into
`DLNFibre.lean`** (single-writer aggregator) — controller to add the import.

One new module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJResolution.lean`. This is the FIRST tide of
the R1-UPPER `(S,J)` mountain (design cert:
`threads/genm-r1upper-design/design-cert.md`, its 7-piece build spec). It lays the honest 7-piece
contract, CLOSES the pieces that reuse banked machinery, and pre-stages the genuinely-new analytic
pieces as named sorries.

## The target

> **Claim.** For an arbitrary width vector `M : Fin (L+1) → ℕ`, the layer-product box integral
> `∫_{A ∈ paramsBoxM M 1} frobSq(prod M A)^{−c'}` is finite for every `c' < ½·minAdm M`
> (`RouteMBoxThresholdFinite M`). This is R1-UPPER (`rlct ≥ ½·minAdm`); it discharges the bare sorry
> `routeMCore_threshold_lt_top` (`RouteMSchur.lean:426`) via `routeMCore_threshold_lt_top_of_box`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMBoxThresholdFinite_sjResolution`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJResolution.lean` @ `d74066a1`)
> - **Gloss.** For all `M`, `RouteMBoxThresholdFinite M` holds — the box integral is `< ⊤` below the
>   geometric threshold.
> - **Proved.** The **recursion spine**: the strong-induction-on-arity wrapper
>   `routeMBoxThresholdFinite_of_step` (axiom-clean `[propext, Classical.choice, Quot.sound]`, NO
>   `sorryAx`) reduces the ∀L target to two contracts — the `(S,J)` inductive step (`SJStepHyp`) and
>   the `L = 1` base (`SJBaseHyp`) — and the step `sjResolutionStep_proof` genuinely composes piece 3
>   (`sjBoundaryPeel`) with pieces 4/5/7 (`sjJointResolution`). The `L = 0` base is closed vacuously
>   (`minAdm = 0`).
> - **Assumed.** none (the target is unconditional; the open content is inside the named sorries).
> - **Cited.** the banked `RouteMLayerSplit` recursion (`LayerSplit_value_eq_minAdm`,
>   `minAdmRec_eq_minAdm`, `Mval_decompose`), the L=2 `(r,r,p)` box-finiteness
>   `routeMBoxThresholdFinite_rrp`, the free-matrix Morse endpoint `sumSqND_box_lt_top`, the L=2
>   fibre engine `fibre_lintegral_mul_le`, the corank recursion `core_schurGen_lt_top`.
> - **Deferred (named sorries — the genuinely-new analytic content).**
>   - `sjBoundaryPeel` (**piece 3**, LOAD-BEARING) — the boundary-0 blow-up peel: the `M` box integral
>     `≤` finite const × Σ over pivot charts of the joint peeled integral (the cert's exact identity
>     `J ≍ P_tail^{−(c'−a/2)}·P_full^{−a/2}`).
>   - `sjJointResolution` (**pieces 4/5/7**, LOAD-BEARING) — the joint peeled integral is `< ⊤` given
>     the strong IH; the simultaneous `(S,J)` double induction + monomial integrability endpoint.
>   - `sjBase1_freeMatrix` (**L = 1 base**) — the single-free-matrix Morse integral; clean plumbing,
>     reducible to `sumSqND_box_lt_top` via a `matBox ≃ᵐ morseBox` reindex (template
>     `MatMulFibre.frobSq22_box_lt_top`).
> - **Status.** sorry-free spine + closed base; named-sorry analytic stubs. Awaiting reviewer fidelity.

## What is CLOSED (sorry-free) — the reusable base

| Piece | Declaration(s) | How |
|---|---|---|
| 1 (comparability) | `sjLocalComparability`, `paramsBoxM_volume_lt_top` | pure measure theory + box compactness |
| 2 (pivot-Schur, L=2) | `sjPivotSchurChart_rrp` | banked `routeMBoxThresholdFinite_rrp` |
| 4 (invariant block-dim) | `sjRunMin_antitone` | running-min corank `M(S)` monotone (coarse consequence) |
| 5 (charge accounting) | `sjChargeUpdate_accum` | banked `Mval_decompose` |
| 6 (charge budget) | `sjChargeBudget_recursion`/`_le`/`_binding`, `minAdm_le_minAdm_redChain_min`, `minAdm_le_minAdm_tailChain`, `sjSubordination` | banked `LayerSplit_value_eq_minAdm` + `minAdmRec_eq_minAdm` (modulo the one residual below) |
| spine | `routeMBoxThresholdFinite_of_step` (axiom-clean), `sjResolutionStep_proof`, `routeMBoxThresholdFinite_base0` | strong induction on arity; step = peel ∘ joint |
| defs | `tailChain` (+`_zero`/`_succ`/`_eq_redChain`), `peelExp`, `frobSqTopRows` (+`_nonneg`), `jointPeelIntegral`, `SJState`, `sjRunMin` | the objects the pieces are stated over |

`sjChargeBudget_recursion`, `sjRunMin_antitone`, `sjLocalComparability` are axiom-clean
`[propext, Classical.choice, Quot.sound]` (forced `#print axioms`).

## The named-sorry stubs (open, for subsequent tides)

| Piece | Declaration | Kind |
|---|---|---|
| 3 (peel) | `sjBoundaryPeel` | genuinely-new analytic (LOAD-BEARING) |
| 4/5/7 (joint resolution) | `sjJointResolution` | genuinely-new analytic (LOAD-BEARING) |
| 6 residual | `minAdm_leadWidth_mono` | clean combinatorial fact (leading-width monotonicity) |
| L=1 base | `sjBase1_freeMatrix` | free-matrix Morse (clean plumbing) |

**Four** sorries total, each genuinely hard (no vacuous or redundant stub). **Three feed the final
`routeMBoxThresholdFinite_sjResolution`** (`sjBoundaryPeel`, `sjJointResolution`, `sjBase1_freeMatrix`);
`minAdm_leadWidth_mono` is the piece-6 residual (feeds only `minAdm_le_minAdm_tailChain` /
`sjSubordination`, not the wrapper). `sjSubordination` carries `sorryAx` only via `minAdm_leadWidth_mono`.

**Fidelity note (self-caught, corrected).** Two candidate stubs were dropped as misleading: a
`sjNormalFormInvariant` sorry stated as `sjRunMin (S+1) ≤ sjRunMin S` is *trivially true* (inf over a
growing set), so it is CLOSED and renamed `sjRunMin_antitone` (the honest coarse consequence, NOT the
matrix-valued invariant, which is deferred with no fake stub); and a general-`L` `sjPivotSchurChart`
stub was dropped because its statement was identical to `SJStepHyp` (redundant with the closed
`sjResolutionStep_proof`) — the general-`L` chart is the internal c.o.v. of piece 3, stated in
`sjBoundaryPeel`'s docstring.

### On the piece-6 residual `minAdm_leadWidth_mono`
`p ≤ q → minAdm (Fin.cons p rest) ≤ minAdm (Fin.cons q rest)`. Numerically verified (0 violations,
`/tmp/sj_check.py`, L ≤ 3, widths 1..5). It is NOT termwise: growing the leading width both raises the
block terms `(p−t)(rest₀−t)` AND widens the admissible pivot range `min(p,rest₀)`, so the
monotone-selection argument does not chain (checked). A modest self-contained combinatorial tide
(strong induction on arity + an `inf'` comparison handling the range-widening); everything else in
piece 6 is banked. This is the only residual keeping subordination from clean-three.

## The key statement shapes (fidelity anchors against the cert)

- **`jointPeelIntegral M t c'`** (piece 3's object): `∫_{A ∈ paramsBoxM (tailChain M) 1}`
  `(frobSqTopRows t (prod (tailChain M) A))^{−(c'−a/2)} · (frobSq (prod (tailChain M) A))^{−a/2}`,
  `a = (M₀−t)(M₁−t)`. Both factors read the SAME tail parameters `A` — the object is **joint**, NOT
  the (cert-proven-unsound) product of independent single-chain integrals. `P_tail` = top-`t`-rows loss
  (`frobSqTopRows` = the reduced tail chain `(t,M₂,…)` loss), `P_full` = the full remaining product
  `(M₁,…,M_L)` loss (`tailChain M = redChain (M 1) M`, proven).
- **`sjBoundaryPeel`**: `∃ C ≠ ⊤, routeMLayerBoxIntegral M c' 1 ≤ Σ_{t ≤ min(M₀,M₁)} C · jointPeelIntegral M t c'`.
- **`sjJointResolution`**: `(∀ M' : Fin (L+1+1)→ℕ, RouteMBoxThresholdFinite M') → c' < ½·minAdm M → jointPeelIntegral M t c' < ⊤` (strong IH → per-chart finiteness).
- **`SJStepHyp`**: for a `≥3`-width `M`, box-finiteness for every one-shorter chain ⟹ box-finiteness for `M`.

## Recommended next-tide order (the mountain, from here)

1. **`sjBase1_freeMatrix`** (L=1 Morse) — cheapest; general `matBox m n ≃ᵐ morseBox (m·n)` reindex +
   `sumSqND_box_lt_top`. Closes an assembly base and de-risks the reindex plumbing.
2. **`minAdm_leadWidth_mono`** — closes piece 6 to clean-three (subordination becomes axiom-clean).
3. **`sjBoundaryPeel`** (piece 3) — the load-bearing peel/exponent-shift; the general-`L` pivot-Schur
   chart (Aoyagi Lemma 2, internal here) + radial blow-up. Consumes piece 1 comparability.
4. **`sjJointResolution`** (pieces 4/5/7) — the standing L≥3 wall: the `(S,J)` double induction (piece 4
   invariant over the `[E_J|D_J]` carrier — block-dim `sjRunMin_antitone` closed; piece 5 charge-update
   `sjChargeUpdate_accum`) + monomial assembly (piece 7), with subordination (`sjSubordination`) keeping
   coupling exponents subordinate. Consumes the strong IH.

Once 1,3,4 (+ base) land, `routeMBoxThresholdFinite_sjResolution` is sorry-free and discharges
`routeMCore_threshold_lt_top`.

## Instrument caveat
The statements transcribe the design cert's 7-piece spec (3 decorrelated passes + Codex xhigh) and
Aoyagi §5; the numeric grounding of the charge budget / subordination / leading-width monotonicity is
`/tmp/sj_check.py` (exact, `minAdmRec == brute-force minAdm` 0/3000; `a(t*) ≤ minAdm M ≤ minAdm(tail)`
0 violations). The analytic pieces (3, 4/5/7) are the box-integral-level contracts; their internal
`(S,J)` carrier (`diag(b)·[E_J|D_J]·∏C^{(s)}`) is the mountain's core definitional work, deferred —
`SJState`/`sjRunMin` are the minimal stubs the invariant is stated over.
