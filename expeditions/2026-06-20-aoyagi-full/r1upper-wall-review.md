# R1-UPPER general-L box-finiteness WALL — adversarial review (red-team)

**Reviewer:** independent red-team (aoyagi-full). Function: claim-soundness of a NEGATIVE (no-go) claim.
**Target:** the WALL verdict in `r1upper-derisk.md` (scout `genm-r1upper`): that ∀L R1-UPPER
box-finiteness (`RouteMBoxThresholdFinite M` for general `M`) is a genuine research wall, not bounded
labour.
**Method:** verify-first source-read of the actual Lean objects + independent exact-algebra (I
reimplemented `minAdm` from the Lean defs, 0 mismatches vs the recursion over 3000 random chains and all
Lean anchors) + a literature check on the Watanabe direction. Codex CLI confirmed broken (Item 111 — it
hangs on a git fetch then throws); I am the decorrelated check, per dispatch.

## VERDICT: WALL CORROBORATED — and sharpened.

The negative claim survives my strongest attacks. The four attack vectors all fail to produce a bounded
route, for a reason I confirmed with a factor-of-2 concrete counterexample. In the course of attacking I
found two refinements the controller should fold in (neither rescues a bounded route; both make the wall
*more precise*). I also flag one **direction imprecision in the fallback framing** (Item 39) that should
be corrected in the synthesis.

---

## What I verified against the actual Lean (the reduction chain is real)

- `RouteMSchur.lean:426` `routeMCore_threshold_lt_top` is a bare `sorry` (SKELETON) — confirmed.
- `RouteMBoxReduction.lean`: `routeMCore_le_matBox` (∀M, MP plumbing) + `routeMCore_threshold_lt_top_of_box`
  (∀M, discharges `:426` GIVEN `hbox : RouteMBoxThresholdFinite M`) are real and the reduction is exactly
  as described. So the entire open content is `RouteMBoxThresholdFinite M` =
  `∫_{A∈paramsBoxM M 1} frobSq(prod M A)^{−c'} < ⊤` for `c' < ½·minAdm M`. **Confirmed.**
- `RouteMLayerCoverHfin.lean` independently corroborates: the value-only layer atlas
  (`routeLayerAtlas`) carries **zero measure-theoretic information** about the loss (no chart map to
  `routeMCore M`), so it supplies only the numerical bound `c' < ½·minAdm M` — the box finiteness `hbox`
  is stated as an EXPLICIT hypothesis there too. This is the same wall, named twice.

## The corank scaffold is genuinely closed — corank is NOT the wall (I built it)

I built `#print axioms` on the load-bearing depth-2 discharge (self-contained scratch module, target only):

```
routeMBoxThresholdFinite_rrp : [propext, Classical.choice, Quot.sound]
schurRecStep_p               : [propext, Classical.choice, Quot.sound]
core_schurGen_lt_top         : [propext, Classical.choice, Quot.sound]
```

So `RouteMBoxThresholdFinite (![r,r,p])` is **fully sorry-free and axiom-clean for ALL corank r and ALL
output width p** — not just the `p=4` binding family the derisk cert emphasized. The corank recursion
(`SchurRecStep p`) is an **exponent-shifting** recursion (the shift `c'' = c' − jp/2` lives in
`SchurLowerIH`), but it shifts across **corank of the single square factor `Δ`** in the `SchurCore
Δ·S` shape, with **no layer index**. This confirms the derisk's key structural claim: the missing
recursion is on the ARITY (layer count), not the corank.

## Attack vector 4 (re-derive the small-L arithmetic) — CONFIRMED, exactly

Independent faithful `minAdm` (block-bound + weak-decrease + last-exponent-zero, cross-checked 0/3000 vs
the recursion and all four Lean `decide` anchors):

- multi-active-boundary binding minimizer at L=3: **86/256** — matches the cert exactly.
- single-cut collapse strictly overshoots minAdm: **44/256** — matches the cert exactly.
- single-cut collapse never undershoots: 0/256 — matches.
- `(2,2,2,2)`: minAdm=3, binding `T*=[1,0,0]`, terms `[1,2,0]` — matches.

The threshold match `schurLambda(r) = ½·minAdm(r,r,4)` holds for all `r` checked (`[½,2,4,6,8,…]`); for
general `p`, `schurLambdaP p r := minAdm(r,r,p)/2` is `rfl`. So the two-matrix machinery is **tight** at
the `(r,r,p)` family — verified.

## Attack vectors 1 & 2 (an arity / exponent-partitioned peel that reaches ½·minAdm) — FAIL, factor-of-2

The strongest bounded route I could construct is the composition the derisk did NOT explicitly try in
this form: a **front-peel arity recursion** — peel the outer layer with `fibre_lintegral_mul_le`
(`prod = A₀·Q` via `prod_front_peel`, cap `c' < M₀/2`), then recurse on the tail box integral, stopping
at any length-2 suffix via the closed `SchurCore` reach. Allowing peel from either end (transpose
symmetry) and the square-Schur reach at leaves, this closes 231/320 chains (L≤3, widths 1–4) — INCLUDING
several genuine L≥3 chains (`(2,2,2,3)`, `(4,4,2,2)`, `(1,2,3,4)`). But it **fails on `(3,3,3,3)`**:

- `minAdm(3,3,3,3) = 6`, target threshold `c' < 3`. Unique binding `T* = [2,1,0]`, per-boundary terms
  `[1,2,3]` — a **full 3-boundary staircase** `3→2→1→0`, codims `1+2+3=6`.
- Best peel reach: peel `A₀` costs the full row-count cap `c' < 3/2` (codim 3), then demands the SAME
  `c'` on the residual `frobSq(A₁·A₂)^{−c'}`. Reach = `min(3, minAdm(3,3,3)=7) = 3` (codim), i.e.
  `c' < 3/2`. **Undershoots the target `c' < 3` by a factor of 2.**

The mechanism is exactly the exponent-preserving obstruction the derisk named, now pinned concretely:
`fibre_lintegral_mul_le` bounds `∫_X frobSq(X·Y)^{−c'} ≤ C·frobSq(Y)^{−c'}` at the **same** `c'`. There
is no repo mechanism to convert budget spent at boundary 0 into a REDUCED exponent on the residual (the
only algebraic factorization, `frobSq(A₀·Y) ≤ frobSq(A₀)·frobSq(Y)`, gives the inverse-power inequality
in the **unusable** direction for an upper bound). The peel charges the full row-count `3` at boundary 0
when the optimal blow-up charges only `1` there and saves `2,3` for the deeper boundaries. **This is the
`½·minAdm` = additive-over-boundaries staircase that no exponent-preserving two-matrix step reaches.**
Attack vectors 1 and 2 fail for the same root cause.

## Attack vector 3 (is the two-matrix limitation fundamental) — YES, fundamental

The `SchurCore Δ·S` object requires the FIRST factor **square** (`Δ : r×r`). `(3,3,3,3)`'s integrand is a
**three-fold** product `frobSq(A₀·A₁·A₂)^{−c'}` — literally not `frobSq(Δ·S)` for any free `(Δ,S)`
measure-equivalent to the box. The single exponent-shifting recursion the repo has descends corank of one
square factor; realizing the additive `[1,2,3]` codim needs a **simultaneous blow-up along the full rank
flag** (the genuine Aoyagi resolution), which is new mathematics, not a composition of the banked pieces.
Fundamental, confirmed.

---

## SHARPENINGS the controller should fold in (the wall is finer than "L≥3")

The derisk frames the wall as uniformly "L≥3". The true boundary of what the **current sorry-free
machinery** closes is finer, and I verified it in Lean:

1. **Some L≥3 chains ARE closed** by the fibre engine. `routeMCore_M4422_threshold_lt_top`
   (`RouteM4422Hfin.lean`) closes `(4,4,2,2)` (L=3) sorry-free, riding `fibre_lintegral_mul_le`. My
   reach model agrees (`(4,4,2,2)` peel reach = 4 = minAdm). So "L≥3 ⟹ wall" is too coarse.
2. **Some L=2 chains are OPEN.** `(2,3,4)` is L=2 but `M₀≠M₁`, so the first factor `A₀` is `2×3`
   (**not** square) — the `SchurCore` shape does not fit, and the peels undershoot (reach 4, need 6).
   Only the `(r,r,p)` sub-family (square first factor) is closed at L=2.

**The sharp characterization:** the current machinery closes exactly the chains whose `½·minAdm` is
reached by (best exponent-preserving both-sided fibre-peel) ∪ (square-first-factor `SchurCore` reach). The
wall is the complement — the **≥2-active-boundary staircases with no square-factor shortcut**
(paradigm: `(3,3,3,3)`, terms `[1,2,3]`; also `(2,2,2)` needs the Schur scaffold since even its peel
reach 2 < minAdm 3). This is the *converged* statement; the monster `(3,3,3,3)` sits exactly the other
side of it. Recommend the synthesis state the wall this way rather than "L≥3".

## Fallback (Item 39 / §5) — available, but the FRAMING is direction-imprecise

The R1-UPPER box-finiteness is the statement `∫ frobSq(prod)^{−c'} < ∞` for `c' < ½·codim`, which is
**exactly** `rlct ≥ ½·codim` (a LOWER bound on the RLCT — finiteness *below* the threshold). Watanabe's
universal inequality is `λ ≤ d/2` with `d` = **total parameter dimension** (regular-model ceiling), an
UPPER bound on the RLCT (literature-confirmed: JMLR/Watanabe SLT — the `d/2` is the regular-model
ellipsoidal-sublevel-set ceiling, not the fibre codimension). **Watanabe's universal upper bound is the
wrong direction and the wrong quantity to supply this finiteness.** The cited route that genuinely
delivers `rlct ≥ ½·codim` is **Aoyagi's exact** `rlct = ½·codim` — which the repo already carries as the
Cited hypothesis `RlctInterface.cited_aoyagi_dln` (the full equality). So the fallback **is** available and
does keep the headline — but *via the Aoyagi exact equality (already Cited), not via a Watanabe universal
`rlct ≤ ½·codim`*. The §5 / Item-39 phrasing "Watanabe's universal `rlct ≤ ½·codim`" should be corrected;
as written it mislabels the direction and the quantity of the citation that actually does the work.

## Instrument caveat (bedrock)

My exact-algebra measures `minAdm` (the threshold VALUE) and the reach of the peel/Schur compositions in
codim units (unit-check: `fibre_lintegral_mul_le` cap `c' < p/2` ⟹ codim-reach `p`; monomial leaf `a×b`
⟹ codim `a·b` — verified consistent). It does **not** numerically integrate the box; the finiteness itself
rests on the Aoyagi/Cited RLCT theory, as the derisk also noted. What I established: (i) the reduction
chain is real and axiom-clean; (ii) the corank scaffold is genuinely closed (corank ≠ wall); (iii) the
natural arity/peel compositions undershoot `½·minAdm` by a factor of 2 at `(3,3,3,3)`; (iv) the wall
boundary is finer than "L≥3"; (v) the fallback is available but its framing needs a direction fix.

## Anchors

- Target sorry: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSchur.lean:426`.
- Reduction (∀M, real): `RouteMBoxReduction.lean` (`routeMCore_le_matBox`,
  `routeMCore_threshold_lt_top_of_box`, `RouteMBoxThresholdFinite`).
- Corank scaffold CLOSED for (r,r,p) ∀r∀p (I built `#print axioms`): `RouteMBoxThresholdRRP.lean`
  (`routeMBoxThresholdFinite_rrp`), `RouteMSchurRecStepP.lean` (`schurRecStep_p`),
  `RouteMSchurGeneral.lean` (`core_schurGen_lt_top`, `SchurCore` = `Δ·S` two-matrix).
- Fibre engine (exponent-preserving peel, cap `c' < p/2`): `MatMulFibre.lean:399`
  (`fibre_lintegral_mul_le`).
- Value-only arity recursion (no measure content): `RouteMLayerSplit.lean` (`minAdmRec`, `LayerSplit`,
  `routeLayerAtlas_value`); the reduction-side corroboration: `RouteMLayerCoverHfin.lean`.
- An L=3 chain the fibre engine DOES close: `RouteM4422Hfin.lean` (`routeMCore_M4422_threshold_lt_top`).
- Fallback interface (the Aoyagi exact equality, Cited hypothesis): `RlctInterface.cited_aoyagi_dln` in
  `lean/DLNFibre/DLN/RlctPayoff.lean`.
- Reproduction scripts (this review): `/tmp/minadm_faithful.py`, `/tmp/wall_arith.py`,
  `/tmp/peel_analysis.py`, `/tmp/frontpeel_recursion.py`, `/tmp/sharp_cases.py`, `/tmp/units_check.py`.
