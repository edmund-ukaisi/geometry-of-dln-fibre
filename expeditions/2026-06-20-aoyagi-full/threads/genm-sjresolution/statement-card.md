# Statement card — general-`L` R1-UPPER `(S,J)` resolution SKELETON (`sjfound` foundation tide)

**Status:** sorry-free for the CLOSED pieces + the recursion wrapper; the genuinely-new analytic
content is confined to clearly-named sorries. Green in the full import closure of
`RouteMSJResolution` (8295 jobs). On `origin/genm-sjresolution` (base
`origin/expedition/aoyagi-full @3d533215`), module commit `d74066a1`. **NOT yet wired into
`DLNFibre.lean`** (single-writer aggregator) — controller to add the import.

> **UPDATE (`genm-sjbase` tide, base `origin/expedition/aoyagi-full @3cb51997`).** The two
> foundational/base sorries (next-tide order #1 and #2) are now **CLOSED sorry-free**:
> - **`sjBase1_freeMatrix`** (the `L = 1` free-matrix Morse base) — reduced the `Params M` box integral
>   through the measure-preserving flattening `paramsEquivFlat M` to the `Fin (M₀M₁)` Morse box, finite by
>   the banked `sumSqND_box_lt_top` (threshold `M₀M₁/2 = ½·minAdm M`); the degenerate `M₀M₁ = 0` case is
>   vacuous. New helpers: `frobSq_prod_eq_flatSum` (`= ∑ flat²` via `prod_one_layer` + `FlatIdx` collapse),
>   `morseBox_sumSq_lt_top` (the `Fin N`-form of the `Fin (m+1)` Morse endpoint), `minAdm_two_eq`.
> - **`minAdm_leadWidth_mono`** (piece-6 residual) — arity induction on the layer-peeling recursion
>   `minAdm_cons_eq` (= `sjChargeBudget_recursion` in `cons` form): the reduced chains `cons t (tail rest)`
>   are shared between the `p`/`q` sides (`redChain_cons`), so the two `inf'`s differ only in the pivot
>   range and the block factor; range-widening handled by the `t = p` zero-charge cut + the IH on
>   `tail rest`. New helpers: `cons_one_eq`, `redChain_cons`, `minAdm_cons_eq`.
>
> Both **force-`#print axioms` clean-three** `[propext, Classical.choice, Quot.sound]` (no `sorryAx`);
> `sjSubordination` and `minAdm_le_minAdm_tailChain` (which rode the piece-6 residual) are now clean-three
> too. The module's remaining sorries are **exactly** `sjBoundaryPeel` + `sjJointResolution` (the two
> LOAD-BEARING analytic pieces); `routeMBoxThresholdFinite_sjResolution` carries `sorryAx` via only those.
> Full `scripts/lb DLNFibre` green. On `origin/genm-sjbase`.

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
> - **Deferred (named sorries — the genuinely-new analytic content).** (Post-`genm-sjbase`: only these
>   two remain; the `L = 1` base is now closed.)
>   - `sjBoundaryPeel` (**piece 3**, LOAD-BEARING) — the boundary-0 blow-up peel: the `M` box integral
>     `≤` finite const × Σ over pivot charts of the joint peeled integral (the cert's exact identity
>     `J ≍ P_tail^{−(c'−a/2)}·P_full^{−a/2}`).
>   - `sjJointResolution` (**pieces 4/5/7**, LOAD-BEARING) — the joint peeled integral is `< ⊤` given
>     the strong IH; the simultaneous `(S,J)` double induction + monomial integrability endpoint.
> - **Closed (`genm-sjbase`).** `sjBase1_freeMatrix` (**L = 1 base**) — the single-free-matrix Morse
>   integral, reduced through `paramsEquivFlat` to the `Fin (M₀M₁)` Morse box, finite by
>   `sumSqND_box_lt_top`.
> - **Status.** sorry-free spine + closed base + closed piece-6 residual; two LOAD-BEARING analytic
>   sorries remain (`sjBoundaryPeel`, `sjJointResolution`).

## What is CLOSED (sorry-free) — the reusable base

| Piece | Declaration(s) | How |
|---|---|---|
| 1 (comparability) | `sjLocalComparability`, `paramsBoxM_volume_lt_top` | pure measure theory + box compactness |
| 2 (pivot-Schur, L=2) | `sjPivotSchurChart_rrp` | banked `routeMBoxThresholdFinite_rrp` |
| 4 (invariant block-dim) | `sjRunMin_antitone` | running-min corank `M(S)` monotone (coarse consequence) |
| 5 (charge accounting) | `sjChargeUpdate_accum` | banked `Mval_decompose` |
| 6 (charge budget) | `sjChargeBudget_recursion`/`_le`/`_binding`, `minAdm_le_minAdm_redChain_min`, `minAdm_le_minAdm_tailChain`, `sjSubordination`, `minAdm_leadWidth_mono` (`genm-sjbase`), `minAdm_cons_eq`/`redChain_cons`/`cons_one_eq`/`minAdm_two_eq` | banked `LayerSplit_value_eq_minAdm` + `minAdmRec_eq_minAdm`; the residual `minAdm_leadWidth_mono` closed by arity induction (fully sorry-free) |
| L=1 base (`genm-sjbase`) | `sjBase1_freeMatrix`, `frobSq_prod_eq_flatSum`, `morseBox_sumSq_lt_top` | `paramsEquivFlat` MP flatten → `Fin (M₀M₁)` Morse box, banked `sumSqND_box_lt_top` |
| spine | `routeMBoxThresholdFinite_of_step` (axiom-clean), `sjResolutionStep_proof`, `routeMBoxThresholdFinite_base0` | strong induction on arity; step = peel ∘ joint |
| defs | `tailChain` (+`_zero`/`_succ`/`_eq_redChain`), `peelExp`, `frobSqTopRows` (+`_nonneg`), `jointPeelIntegral`, `SJState`, `sjRunMin` | the objects the pieces are stated over |

`sjChargeBudget_recursion`, `sjRunMin_antitone`, `sjLocalComparability` are axiom-clean
`[propext, Classical.choice, Quot.sound]` (forced `#print axioms`).

## The named-sorry stubs (open, for subsequent tides)

| Piece | Declaration | Kind |
|---|---|---|
| 3 (peel) | `sjBoundaryPeel` | genuinely-new analytic (LOAD-BEARING) |
| 4/5/7 (joint resolution) | `sjJointResolution` | genuinely-new analytic (LOAD-BEARING) |
| ~~6 residual~~ | ~~`minAdm_leadWidth_mono`~~ | **CLOSED** (`genm-sjbase`) — arity induction on `minAdm_cons_eq` |
| ~~L=1 base~~ | ~~`sjBase1_freeMatrix`~~ | **CLOSED** (`genm-sjbase`) — free-matrix Morse via `paramsEquivFlat` |

**Two** sorries remain (post-`genm-sjbase`), both genuinely hard LOAD-BEARING analytic pieces feeding
the final `routeMBoxThresholdFinite_sjResolution`: `sjBoundaryPeel` (3) and `sjJointResolution` (4/5/7).
The `L=1` base and the piece-6 residual are now closed sorry-free (see the UPDATE banner);
`sjSubordination` / `minAdm_le_minAdm_tailChain` no longer carry `sorryAx`.

**Fidelity note (self-caught, corrected).** Two candidate stubs were dropped as misleading: a
`sjNormalFormInvariant` sorry stated as `sjRunMin (S+1) ≤ sjRunMin S` is *trivially true* (inf over a
growing set), so it is CLOSED and renamed `sjRunMin_antitone` (the honest coarse consequence, NOT the
matrix-valued invariant, which is deferred with no fake stub); and a general-`L` `sjPivotSchurChart`
stub was dropped because its statement was identical to `SJStepHyp` (redundant with the closed
`sjResolutionStep_proof`) — the general-`L` chart is the internal c.o.v. of piece 3, stated in
`sjBoundaryPeel`'s docstring.

### On the piece-6 residual `minAdm_leadWidth_mono` (CLOSED, `genm-sjbase`)
`p ≤ q → minAdm (Fin.cons p rest) ≤ minAdm (Fin.cons q rest)`. Numerically verified (0 violations,
`/tmp/sj_check.py`, L ≤ 3, widths 1..5). It is NOT termwise: growing the leading width both raises the
block terms `(p−t)(rest₀−t)` AND widens the admissible pivot range `min(p,rest₀)`, so the
monotone-selection argument does not chain (checked). **Proved** by strong induction on the chain arity
via `minAdm_cons_eq` (the layer-peeling recursion `sjChargeBudget_recursion` rewritten in `Fin.cons`
form, with `redChain t (cons p rest) = cons t (tail rest)` = `redChain_cons` making the reduced chains
`p`-independent): for a `q`-cut `t` inside the `p`-pivot range the shared cell is monotone in the leading
width; for `min(p,rest₀) < t ≤ rest₀` the `p`-cut `t = p` has zero block charge and the induction
hypothesis on `tail rest` gives `minAdm (cons p (tail rest)) ≤ minAdm (cons t (tail rest))`. This closes
the last residual, so `sjSubordination` / `minAdm_le_minAdm_tailChain` are now clean-three.

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

1. ~~**`sjBase1_freeMatrix`** (L=1 Morse)~~ — **DONE** (`genm-sjbase`; the reduction went through
   `paramsEquivFlat`, not a bespoke `matBox ≃ᵐ morseBox` reindex).
2. ~~**`minAdm_leadWidth_mono`**~~ — **DONE** (`genm-sjbase`; piece 6 now clean-three, subordination
   axiom-clean).
3. **`sjBoundaryPeel`** (piece 3) — the load-bearing peel/exponent-shift; the general-`L` pivot-Schur
   chart (Aoyagi Lemma 2, internal here) + radial blow-up. Consumes piece 1 comparability.
4. **`sjJointResolution`** (pieces 4/5/7) — the standing L≥3 wall: the `(S,J)` double induction (piece 4
   invariant over the `[E_J|D_J]` carrier — block-dim `sjRunMin_antitone` closed; piece 5 charge-update
   `sjChargeUpdate_accum`) + monomial assembly (piece 7), with subordination (`sjSubordination`) keeping
   coupling exponents at or below threshold. Consumes the strong IH. **Gentle-cut caveat (reviewer +
   decorrelated Codex):** subordination is `≤` (NON-strict); strict fails at some `a>0` binding cuts
   (84/3875: `a = minAdm(tail)` exactly, e.g. `M=(1,1,1)` cut `t=0`), so this tide must select a favorable
   minimal-`a` ("gentle") binding cut or exhibit slack elsewhere — it cannot assume strict slack from the
   arbitrary minimiser `sjChargeBudget_binding` returns.

With 1 and 2 landed (`genm-sjbase`), only 3 and 4 remain; once they land,
`routeMBoxThresholdFinite_sjResolution` is sorry-free and discharges `routeMCore_threshold_lt_top`.

## Reviewer verdict
Fidelity audit (reviewer + decorrelated Codex, `d74066a1`): **PASS-WITH-NITS**. The skeleton faithfully
encodes the cert's 7-piece spec + Aoyagi §5; `jointPeelIntegral` is a correct JOINT encoding (not the
cert-proven-unsound independent-chain product); the recursion spine is sound and gap-free (`L=0` vacuous,
`L=1` base, `L≥2` step, arity drops by one); the four sorries are all genuinely-new content under correct
non-vacuous statements, final footprint exactly `{sjBoundaryPeel, sjJointResolution, sjBase1_freeMatrix}`.
`minAdm_leadWidth_mono` confirmed a genuine non-trivial residual (0/5418; 318 cases where the range-
widening beats termwise selection — so it does not chain). The one substantive nit (strict-subordination
prose overclaim) is corrected above and in the module docstrings; the Lean statement was already sound
(`≤`). `sjRunMin_antitone` confirmed honestly caveated (coarse consequence, not the matrix invariant).

## Instrument caveat
The statements transcribe the design cert's 7-piece spec (3 decorrelated passes + Codex xhigh) and
Aoyagi §5; the numeric grounding of the charge budget / subordination / leading-width monotonicity is
`/tmp/sj_check.py` (exact, `minAdmRec == brute-force minAdm` 0/3000; `a(t*) ≤ minAdm M ≤ minAdm(tail)`
0 violations, non-strict — strict fails at 84/3875 `a>0` cuts). The analytic pieces (3, 4/5/7) are the
box-integral-level contracts; their internal `(S,J)` carrier (`diag(b)·[E_J|D_J]·∏C^{(s)}`) is the
mountain's core definitional work, deferred — `SJState`/`sjRunMin` are the minimal stubs the invariant
is stated over.
