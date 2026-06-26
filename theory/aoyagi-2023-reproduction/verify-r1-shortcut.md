# Hard-validation certificate — the R1 §8 "binding-divisor shortcut"

**Seat:** `pen-and-paper` (adversarial hard-validation). **Date:** 2026-06-23.
**Gates:** R1 Lean design (#18).
**Method:** exact sympy (symbolic pullbacks, exact orders), MC volume-scaling as a *guide only*,
+ one decorrelated `local-codex-consult` at `xhigh` (frame-in / facts-in / hypothesis-out).
Artefacts: `/tmp/r1_L3_chain.py`, `/tmp/r1_L3_unit_check.py`, `/tmp/r1_L2_unit_order.py`,
`/tmp/r1_L3_resolve_U.py`, `/tmp/r1_U_leadform.py`, `/tmp/r1_L3_t110.py`,
`/tmp/r1_normal_hessian.py`, `/tmp/r1_recursive_value.py`, `/tmp/r1_branch_lowerbound.py`,
`/tmp/r1_mc_rlct.py`; Codex prompt+answer in
`expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/shortcut-{prompt,answer}.md`.

---

## VERDICT: **NEEDS-MODIFICATION** (the geometry is wrong for `L≥3`; the value survives)

The §8 shortcut, **as written**, is **false for general `L`**. Its specific geometric claim —

> iterated block-elimination exposes a *single* codim-`Mval(t)` smooth center; **ONE** blow-up of
> it gives `F∘φ = u²·(unit)` with Jacobian `u^{Mval(t)−1}`, ratio `½·Mval(t)`, in one step

— **holds at `L=2` and FAILS at `L=3` (and beyond)** with an explicit witness. It is the *same
class of error* as the refuted per-node recursion: validated on `L=2`, broken at `L≥3`.

**BUT** the part R1's headline actually consumes — the **value** `rlctAt(core) = ½·min_t Mval(t)` —
is **robust** (confirmed exact + MC-guide + decorrelated Codex). What must change is the *mechanism*:
the resolution is **recursive in depth** (one (incidence + 1 blow-up) peels **one layer**, leaving a
fresh depth-`(L−1)` core), **not** a single terminal blow-up. With that correction the route is sound
and is materially lighter than Aoyagi's full accumulated Cases 1&2 — see the recommendation.

---

## The general-`L` witness (the load-bearing failure)

Take `(2,2,2,2)`, `L=3`, minimizing stratum `t=(1,0,0)`, `Mval(t)=3`. Apply **exactly** the §8
procedure that succeeds at `L=2`: the layer-1 incidence chart
`A=α[[1,a],[b,ab+δ]]`, `B=[[u−ar,v−as],[r,s]]`, then **one** blow-up of the codim-3 center
`{δ=u=v=0}` in the δ-chart `δ=ρ, u=ρξ, v=ρη`. Exact sympy (`/tmp/r1_L3_chain.py`,
`/tmp/r1_U_leadform.py`):

$$F \;=\; \alpha^2\,\rho^2\,U,\qquad
U \;=\; \big\lVert\,\begin{psmallmatrix}\xi&\eta\\ b\xi+r& b\eta+s\end{psmallmatrix}\,C\,\big\rVert^2
\;=\; \big\lVert\,\begin{psmallmatrix}1&0\\ b&1\end{psmallmatrix}
\begin{psmallmatrix}\xi&\eta\\ r&s\end{psmallmatrix}\,C\,\big\rVert^2 .$$

`U` is **not a unit**: it **vanishes to order 4** at the deepest point of `{ρ=0}`
(`/tmp/r1_L3_unit_check.py`: `U` order at origin of the free coords = 4, `U|_{deepest}=0`). So
`F = ρ²·U` is **not** `ρ²·(unit)` — the §8 "one blow-up gives `u²·unit`" claim is **false here**.

The contrast with `L=2` is the diagnostic (`/tmp/r1_L2_unit_order.py`):

| | residual `U` after the one blow-up | order at deepest pt | transverse Hessian rank | status |
|---|---|---|---|---|
| `L=2` `t=(1,0)` | `(bξ+r)²+(bη+s)²+ξ²+η²` | 2 | **4 (nondegenerate, Morse)** | `ρ` genuinely binds, `unit` resolves cleanly |
| `L=3` `t=(1,0,0)` | `‖XC‖²` (a **fresh `‖XY‖²` (2,2,2) core**) | **4** | 0 (degenerate) | `ρ` does **not** give `u²·unit`; recursion needed |

At `L=2` the residual is a **nondegenerate quadratic** (Morse) in the normal coords, so the one
blow-up *does* finish that divisor. At `L=3` the residual is a **fresh matrix-product singularity**
`‖XC‖²` — *another copy of the `L=2` (2,2,2) core* — that needs its **own** incidence+blow-up.

**Decorrelated Codex independently reached the identical residual** `[[ξ,η],[r,s]]·C = 0` and the
same verdict (answer file, FACT-tagged): "*the statement 'one codim-`Mval(t)` blow-up gives
`F=u²·unit`' is false as a global geometric/log-resolution claim for `L≥3`*"; "*the correct
full-resolution picture is recursive*." No rubber stamp: it was withheld my conclusion and
constructed the witness from the setup.

### Why the "smooth codim-`Mval` center" framing is itself misleading

A second exact check (`/tmp/r1_L3_oneshot.py`, `/tmp/r1_normal_hessian.py`) shows the strawman
"blow up `S(t)` directly" is even worse:
- **No** codim-3 *coordinate-subspace* blow-up of the original variables gives `F` order `≥1`
  (all 220 triples give order 0 — `F` does not even vanish along a generic codim-3 plane).
- The **transverse Hessian of `F` at a generic point of `S(t)`** has rank `< Mval(t)` for *every*
  stratum tested (e.g. `L=3 t=(1,0,0)`: Hessian rank **0**, `Mval=3`). So `F` vanishes to order
  `>2` in normal directions — `S(t)` is **not** a Morse-transverse center.

The §8 residual is therefore **not** a coordinate subspace of the original space, and **not** the
normal cone of `S(t)`; it lives only in the *blown-up* chart (after the incidence blow-up). The §8
text's "single smooth center, one blow-up" conflates the genuine `L=2` picture with the `L≥3`
recursion. Aoyagi's `M_{s,k}` is **accumulated across multiple blow-up steps** (p15 invariant:
each `b_i` is a *product* of many `u_{s,k}`; Case 1(1) *increments* `M'_{s,k}=M_{s,k}+J_1(M^{(S+1)}−J)`
and merges divisors). The accumulation is **real and multi-step**; one-shot misrepresents it.

---

## Answers to the five questions

**Q1 — one-shot `F∘φ=u²·unit`, Jacobian `u^{Mval−1}`, for general `L`?**
**NO.** Exact witness above: at `L=3` `t=(1,0,0)` the pullback is `α²ρ²·U` with `U` order-4
(not a unit). The `ρ`-divisor's *own* `(k,h)=(1,2)` is correct on the generic open piece, but the
chart is **not normal-crossing after one blow-up** — `U` is a fresh L=2 core needing its own
resolution. This is the direct analogue of the Erow-not-Morse failure.

**Q2 — residual = a regular sequence cutting a smooth codim-`Mval` center, general `L`?**
**The codim count is right; the geometry is not "one center."** `{δ=u=v=0}` *is* a smooth codim-3
coordinate subspace in the chart, and the joint `R_1,…,R_L` scalar count `= Mval(t)` (verified
`/tmp` sweeps in thread-14, re-confirmed: the layer-decomposition sums to `Mval` with 0 mismatches
across L=2,3,4 incl. non-equal widths). **But** blowing it up does **not** terminate the resolution
at `L≥3`: the §8 inference "smooth codim-`Mval` center ⟹ one blow-up gives `u²·unit`" is the false
step. The residual is a *complete intersection of the right codimension* that, after blow-up, leaves
a **lower-depth product singularity**, not a unit. (Verified L=3 `t=(1,0,0)` AND the L=4 recursion
step `U₄=‖XCD‖²`, a fresh L=3 core — `/tmp/r1_L3_t110.py`.)

**Q3 — generic-vs-nongeneric: does a nongeneric sublocus bind LOWER than `½·Mval_min`?**
**No evidence of lower binding; value holds.** The nongeneric locus where `U` vanishes is exactly
the *fresh lower-depth core* `‖XC‖²`. Its RLCT is `½·min Mval` over the **sub-strata**, and the
sub-strata are a **subset** of the original strata (the recursion fixes `t₁` at the branch value),
so `min over sub-strata ≥ global min`. Inductively, **no recursive divisor binds below
`½·min_t Mval(t)`** (`/tmp/r1_branch_lowerbound.py`). MC volume-scaling guide
(`/tmp/r1_mc_rlct.py`): `L=2 (2,2,2)` slope → 1.495 ≈ 3/2 cleanly; `L=3 (2,2,2,2)` slope climbing
1.33→1.5 from below (consistent with `θ=3` log-corrections), no sign of anything `<3/2`.

**Q4 — cover lower bound "no branch's ratio `< ½·min Mval`", without the full atlas?**
**Yes — structural/inductive, no atlas enumeration.** Per recursion step the divisors are:
(i) the **incidence/`α` divisor**, ratio `= ½·(layer-1 full codim) = ½·M¹M² = ½·Mval(t=0) ≥ ½·min`;
(ii) the **`ρ` (residual) divisor**, ratio `= ½·Mval(branch) ≥ ½·min` by definition of the min;
(iii) the **recursive-core divisors**, `≥ ½·min` by induction (sub-strata ⊆ original strata).
So every divisor's ratio `≥ ½·min_t Mval(t)`, and the binding stratum attains it. (Caveat below.)

**Q5 — BOTTOM LINE: build §8 shortcut, or fall back to Aoyagi's full recursion?**
**Build the CORRECTED recursion** — neither the literal §8 one-shot **nor** the full accumulated
Cases 1&2 bookkeeping. The correct, verified, Lean-tractable mechanism is the **depth recursion**:

> **One layer per (incidence blow-up + ONE residual blow-up).** For the core `F_L = ‖C¹⋯Cᴸ‖²`,
> the layer-1 incidence chart + the `{δ=u=v=0}` blow-up gives `F_L = α²·ρ²·F_{L−1}'`, where
> `F_{L−1}' = ‖X C³⋯Cᴸ‖²` is a **fresh depth-`(L−1)` core** (`X` a fresh free matrix). Recurse on
> `F_{L−1}'`. The exceptional divisors are `{α_j, ρ_j}` over the `L` recursion levels; the value is
> `½·min_t Mval(t)` and **every** divisor ratio is `≥` that (Q4). Verified exact at the recursion
> step for `L=3` and `L=4`.

This is **lighter than Aoyagi's accumulated atlas** (no Case-1(1) exponent merging, no `b_i`
product bookkeeping) and **honest about the geometry** (it is genuinely recursive, matching
Codex's "recursive picture"). It is heavier than the (now-refuted) one-shot, but that shortcut was
wrong.

---

## Scope, caveats, and the recursion across branch types (open leg now CLOSED)

- **Value vs mechanism, kept separate.** Proven-robust: `rlctAt(core) = ½·min_t Mval(t)` (exact +
  MC-guide + Codex). Refuted: the one-shot single-blow-up mechanism at `L≥3`. The `rlct = ½·codim`
  *reading* still rides on the cited analytic bound (S2 / the codim/2 input) — unchanged by this.
- **Recursion peel — now verified beyond `2×2`.** The recursion step `F_L = α²ρ²·‖X·C³⋯Cᴸ‖²`
  (fresh lower-depth core) is exact-confirmed on:
  - `L=3` `(2,2,2,2)` `t₁=1` (`/tmp/r1_L3_chain.py`): residual `= ‖X C‖²`, fresh `(2,2,2)` core;
  - `L=4` `(2,2,2,2,2)` (`/tmp/r1_L3_t110.py`): residual `= ‖X C D‖²`, fresh `(2,2,2,2)` core;
  - **non-square inner layer** `(2,2,3,2)` `t₁=1` (`/tmp/r1_general_peel.py`): residual
    `= ‖X'·C³‖²` with `X'` a `2×3` block, a fresh `(2,3,2)` `L=2` core — the peel handles
    rectangular layers. Here the `ρ`-divisor codim `= Mval(branch t=(1,0,0)) = 4`, ratio `2`, and
    the **binding** is the inner core (min `Mval` over the inner strata), exactly as the recursive
    picture predicts.
### Partial-rank incidence (`t₁ ≥ 2`) — CLOSED (the open leg), decorrelated-confirmed

Layer-1 rank `t₁ ≥ 2` splits into **two sub-cases** by the layer-1 residual codimension
`c₁ := (M¹−t₁)(M²−t₁)`, and they behave differently. All three controller-named cases run
explicitly (no extrapolation):

**Sub-case A — `c₁ = 0` (`t₁` is full in the smaller dimension): unit reduction, recursion CLEAN.**
- `(3,2,2,2)`, `t₁=2 = M²` (full *column* rank of the `3×2` `C¹`): `C¹ᵀC¹ = E₂ + A₂₁ᵀA₂₁` is
  positive-definite (a unit), so `⟨C¹C²C³⟩ = ⟨C²C³⟩` — reduces to a **fresh `(2,2,2)` core**,
  `rlct = 3/2 = ½·min Mval(3,2,2,2)` (`/tmp/r1_named_cases.py`).
- `(2,3,2,2)`, binding branch `t=(2,1,0)`, `t₁=2 = M¹` (full *row* rank of the `2×3` `C¹`): `C¹`
  surjective ⟹ `C² ↦ C¹C²` surjective onto all `2×2` (Jacobian rank 4), so `⟨C¹C²C³⟩ = ⟨D C³⟩`
  with `D` a **free** `2×2` — a fresh `(2,2,2)` core, `rlct = 3/2 = ½·min Mval(2,3,2,2)`
  (`/tmp/r1_named_cases.py`). **No exceptional divisor at layer 1; the one-layer peel holds
  cleanly.** (Both controller-named cases land here — `c₁=0`.)

**Sub-case B — `c₁ > 0` (genuine partial drop, `0 < t₁ < min(M¹,M²)`): coupled, recursion NOT
disjoint.** This is where the previous shortcut died. Tested on `(3,3,2,2)`, binding branch
`t=(2,1,0)`, `Mval=4` (target `rlct=2`), `t₁=2 < min(3,3)=3`, residual codim `c₁=(3−2)(3−2)=1`
(a real `δ`).

**Exact peel (`/tmp/r1_partial_peel.py`).** Block-eliminating `C¹` (unit transforms, ideal-
preserving — Aoyagi Lemma 1) to `C¹ ∼ diag(E₂, δ)` and absorbing into `C²` (fresh free `3×2`)
gives the **exact identity**
`F_core = ‖T·C³‖² + δ²·‖R·C³‖²`, with `T` = top `2×2` of the fresh `C²`, `R` = its bottom `1×2`
row, `C³` free `2×2`, `δ` the residual scalar.

**KEY FINDING — partial rank does NOT preserve the clean recursion.** Unlike the rank-1 peel
(`F = α²ρ²·(fresh disjoint core)`), here the `δ²‖RC³‖²` term **shares `C³`** with `‖TC³‖²`:
applying the `‖TC³‖²`-resolving blow-up leaves `δ²‖RC³‖²` **not** divisible by the exceptional
coordinate (`/tmp/r1_partial_resolve.py`: lowest `τ`-power 0). The peel leaves
`M = diag(E₂, δ)·(free)` — **exactly Aoyagi's `diag(b)` invariant** (p15) — i.e. the recursion
*continues on a constrained core*; it does not factor into independent pieces.

**The VALUE survives, exactly.** `rlctAt(F_core) = rlct of the (3,3,2,2) core at this branch
= ½·Mval = 2`, guaranteed by ideal-preservation (block-elim is a unit transform). Independently
confirmed by **decorrelated Codex** (`codex/partial-answer.md`, xhigh, FACT-tagged) with a full
exact resolution: blow up `{C³=0}` (radial divisor, ratio `4/2=2`); on the rank-1 `C̄` chart the
residual monomial ideal `(εB₁, εB₂, δE, δεF)` has Newton-min `1`, residual RLCT `1+1=2`; so
`RLCT₀(G)=min(2,2)=2`. Codex pinpoints the coupling: **the `δE` generator from `δ²‖RC³‖²` raises
the residual threshold from `3/2` (the `‖TC³‖²`-only value) to exactly `2`** — the `C³`-sharing is
load-bearing. Independent MC guide (`/tmp/r1_verify_codex_newton.py`, NOT using Codex's algebra):
`‖TC³‖²`-only residual → 1.49 ≈ 3/2 (clean); with `δ`-terms → ~1.83 climbing to 2. Value `2` robust.

**Consequence for R1 (precision).** The depth-recursion's *value* `½·min Mval` holds general-`L`,
**all branch types** (rank-1, full-in-min-dim, and genuine partial — every case tested gives the
exact `½·Mval`). But the **clean disjoint "divisor + fresh core" Fubini recursion holds only when
each peel has residual codim `c₁ = 0` or is a rank-1 cone** (`t₁=1`, or `t₁` full in the smaller
dimension). A **genuine partial drop (`c₁>0`, sub-case B) reproduces Aoyagi's coupled `diag(b)`
invariant** — the recursion continues on a *constrained* core, not a disjoint product. So R1's Lean
build must **not** assume the disjoint-core recursion in general. Two sound options: (i) build the
clean disjoint recursion for the `c₁=0`/rank-1 peels and handle `c₁>0` branches by the value
directly (codim + the cited `codim/2`); or (ii) commit to the constrained `diag(b)` recursion
(Aoyagi's actual structure). The value-match is unaffected either way.

**Whether every minimizer can be reached by clean (`c₁=0`/rank-1) peels — a follow-up worth a
check, not a blocker.** In all `(2,2,2,2)`, `(2,3,2,2)`, `(3,2,2,2)` cases the binding branch was
reachable by a clean peel; `(3,3,2,2)`'s binding `t=(2,1,0)` was NOT (`c₁=1`). If a clean peel
always reaches *some* minimizer (plausible but unproven), option (i) suffices general-`L`; if not,
option (ii) is mandatory for those branches. Either way the **value** is certified.

### Earlier open items — now resolved
- **General widths / non-square layers (`t₁=1`):** `(2,2,3,2)` peel leaves a fresh `(2,3,2)` `L=2`
  core (`/tmp/r1_general_peel.py`).
- **Full-row-rank layer (`t₁=M¹`):** unit reduction, no exceptional divisor, reduces to a fresh
  lower core (`/tmp/r1_partial_rank.py`).
- **Cover lower bound (Q4), general widths:** robust regardless of branch type — the radial
  `{C³=0}` blow-up in the partial case gives ratio `½·(its codim) ≥ ½·min`, and the residual RLCT
  `= ½·Mval(branch) ≥ ½·min`.

**Theorem named by true scope (precision policy).** The honest name is **"the depth-recursive
resolution: peeling one layer reduces the core to a lower-depth core; the binding ratio is
`½·Mval(t)` and no divisor binds lower"** — with the caveat that the peel is a clean *disjoint*
divisor+core only for rank-1 branches, and a *coupled* (Aoyagi `diag(b)`) reduction for
partial-rank branches. **Not** "the codimension is resolved in one blow-up" (the refuted claim).
