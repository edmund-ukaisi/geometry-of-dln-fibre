# genm-vsastruct — the NATIVE alt vs the sector-casting (charter-directed route pick)

**Seat:** pen-and-paper (route adjudication). **Date:** 2026-07-11. **NO Lean.** **Charter:** "a det-inverse
in a Jacobian = re-express in native form, NOT a wall." **Charge:** decide the literal (3,3,3,4) one-peel
build path — the native `sjGoodMap` endpoint (no det-inverse) vs the sector-restricted casting (`|det M|^{−4}`).
**Decorrelated:** `codex/altroute-{prompt,answer}.md` (gpt-5.6, xhigh; my lean withheld — it CONFIRMED the
native win term-for-term, with the `det M=0` vs positive-definite counterexample). Prior: `onepeel-tieback`,
`onepeel-tonelli`, `onepeel334-audit`.

---

## ONE-LINE VERDICT — the NATIVE `sjGoodMap` route WINS decisively; ABANDON the casting

**The native route reaches the SAME strict `c'<7/2 = ½·minAdm(3,3,3,4)`, GENUINELY ELIMINATES the
`|det M|^{−4}` det-inverse (does not relocate it), and its inner slice is ALREADY BANKED — no casting, no
`{|det M|≥η}` sector, no ~7-piece chart, no `corner334` Fin-2-row, no clean-coords `onePeel334` detour, no
coercive unit-clear. The det-inverse was a self-inflicted artifact of reparametrising `A₂`. The native
route's only remainder is the OUTER tail integration + the good-chart cover — the deeper (S,J) rung BOTH
routes share (a σ_min/coercivity weight, det-inverse-free). Charter ("re-express natively") + bedrock
DECISIVELY favour the native route. Commission the formaliser on it, NOT the casting.**

## 1. The native ALT — banked inner slice, no det-inverse (Q1)

The native chain (all sorry-free / banked; the one `sorry` grep-hit in `RouteMSJGoodCoords` is the docstring
word "sorry-free"):

1. **`gammaPeelIntegral_sjGoodMap_eq`** (`RouteMSJGoodCoords`) — `gammaPeelIntegral M t ρ κ c'` = the triple
   integral of `sjGoodChartLoss = frobSq(P·v·A₂) + frobSq((C·v+Γ·W)·A₂)`. Equality, no hyps. BANKED.
2. **`sjGoodChartLoss_endpoint_lt_top`** (`RouteMSJVExpose`, 0 sorries) — the `v`-exposure CoV + the endpoint:
   the `(Γ,v)`-integral of `sjGoodChartLoss^{−c'}` is finite for `c' < (a·b + t·h)/2`, given the good-chart
   invertibility. BANKED.
3. **`sjGoodMap_loss_matBox_lt_top`** (`RouteMSJGoodChart`, 0 sorries) — the endpoint: flatten `(Γ,v)` to
   `ℝ^{a·b+t·h}` (measure-preserving linear), `g_cc` becomes degree-2-homogeneous + continuous +
   sphere-positive (`sjGoodMap_loss_pos`), closed by the ISOTROPIC `corner_block_cube_lintegral_lt_top_of_pos`,
   threshold `(a·b+t·h)/2`. BANKED.

**For (3,3,3,4) t=1:** `a=p=M₀−t=2`, `b=q=M₁−t=2` (`a·b=4`), `t=1`, `h=M₂=3` (`t·h=3`), so
`(a·b+t·h)/2 = (4+3)/2 = 7/2 = ½·minAdm`. [FACT — Codex-confirmed.] `g_cc = ‖L_θ(Γ,v)‖²` is a
POSITIVE-DEFINITE quadratic on `ℝ⁷` (given `P` left-inv, `W,A₂` right-inv: `L_θ(Γ,v)=0 ⟹ v=0` (via `A₂,P`
inverses) `⟹ Γ=0` (via `W` inverse)); the isotropic-`7`-corner and Route 1's weighted-`4+3` corner have the
SAME codimension-addition mechanism and critical exponent `7/2` (`h₀+1=4=dim Γ`, `h₁+1=3=dim v`). The native
presentation is CONCEPTUALLY STRONGER: it obtains `7/2` directly from the actual 7-dim quadratic loss,
without manufacturing two radial units and recombining their codimensions. [Codex Q1.]

**No det-inverse:** the native inner integral is over `(Γ,v)` at FIXED `A₂`, closed by `corner_block_cube`
— it NEVER casts `A₂`, so `|det M|^{−4}` never appears. The `{|det M|≥η}` sector-restriction is likewise
absent. [FACT.]

## 2. Decision — native eliminates (not relocates) the det-inverse; strictly smaller remainder (Q2, Q3)

**The det-inverse is GENUINELY ELIMINATED.** [FACT — Codex Q2, decisive.] The outer degeneration (as the
good-chart data `P,W,A₂` approach rank loss) is the sphere-minimum / smallest-singular-value coercivity
weight `a(θ) = min_{‖x‖=1}‖L_θ x‖² = σ_min(L_θ)²`, giving `∫_{cube} g_cc^{−c'} ≤ C·a(θ)^{−c'} =
C·σ_min(L_θ)^{−2c'}` — a **coercivity weight, NOT a change-of-variables Jacobian**. The distinction is
substantive: `W=(e₁;e₂), v̄=e₁` gives `det M=0` (Route 1's casting degenerates), while the native quadratic
form `g_cc` **remains positive-definite** (no degeneration at all) under the good-chart hypotheses. So the
casting determinant vanishes where the native slice has none — `|det M|^{−4}` came SOLELY from reparametrising
`A₂`. A deeper proof may use rank strata / singular values / minor estimates as TOOLS, but that does not
resurrect the casting determinant.

**Native remainder is strictly smaller.** [FACT — Codex Q3.] Route 2's inner work is ALREADY banked (chart
equality + `v`-exposure + flatten + sphere-positivity + isotropic corner). Route 1 ADDITIONALLY needs the
angular/projective charts, the unit-clear coercivity, the `A₂`-casting, its image-domain control, the
`|det M|^{−4}` Jacobian, and a determinant sector/complement. BOTH owe the outer rank degeneration. So Route
2's substantive remainder = the common outer-tail / deeper (S,J) rung, WITHOUT Route 1's casting-specific
obligations. **Native wins on charter (re-express natively), bedrock (no manufactured det-inverse, no coercive
unit-clear, the actual chart loss), and piece-count (inner slice banked).**

**Build plan for the WINNER (native).** The (3,3,3,4) one-peel body:
- **Inner slice (good chart, `7/2`): BANKED** — `gammaPeelIntegral_sjGoodMap_eq` ∘ `sjGoodChartLoss_endpoint_lt_top`.
- **Remainder: the OUTER tail integration** over `A'` on the refined good∪deeper cover + the (S,J)
  L-recursion (the environment integration `chartInner_eq_outerShearFree` flags as "the un-banked mountain").
  This is det-inverse-free (a σ_min/coercivity weight `σ_min(L_θ)^{−2c'}`, integrated over the tail).
- **ABANDON** the casting route (a)+(b) + `onePeel334` clean-coords detour — it is a PARALLEL route that
  manufactured the det-inverse. (Keep `onePeel334`/`corner334` banked as reusable, but OFF the critical path.)

## 3. The front-rank-drop deeper rung — both routes owe it; it is the decorated (S,J) descent (3)

Either route owes the OUTER degeneration where the good-chart data loses rank. In the native route this is
`σ_min(L_θ) → 0` (as `P,W,A₂` degenerate) — the environment integration on the refined good∪deeper cover +
the (S,J) L-recursion. This IS the T4 decorated-double-induction descent: the FRONT rank descends per level
(the good chart is the `{σ_min(L_θ) ≥ κ}` sector; the complement is the deeper corank stratum = a further
peel of the `redChain`), and the DEEP factor `A₂` is rescued per level (`onepeel-tonelli-cert`: A₂-rank-drop
is a Morse codim-rescue, non-binding). Consistent with the decorated recursion + `DecoratedPeelStep`; it is
the genuine remaining `sjJointResolution` content. **Caveat (Codex):** the crude `a^{−c'} = σ_min(L_θ)^{−2c'}`
bound may be too coarse globally — proving ITS integrability over the tail (or a sharper anisotropic estimate)
is part of the deeper rung. This is exactly the LAYER-2 / product-tube `∫σ_min^{−α}` integrability
(banked-adjacent, `RouteMSJProductTube`) and the corank-recursion — the σ_min weight, det-inverse-free.

---

## VERDICT / firmest / most-likely-to-break / next
- **VERDICT.** NATIVE `sjGoodMap` route WINS decisively (charter + bedrock + piece-count). Same strict
  `c'<7/2=½·minAdm`; det-inverse genuinely eliminated (outer degeneration is `σ_min(L_θ)²`, not a
  det-Jacobian); inner slice already banked; remainder = the shared deeper (S,J) rung.
- **Firmest.** The native inner slice (7/2) is banked and sorry-free (`gammaPeelIntegral_sjGoodMap_eq` +
  `sjGoodChartLoss_endpoint_lt_top` + `sjGoodMap_loss_matBox_lt_top`, isotropic corner dim `a·b+t·h=7`).
  `g_cc` positive-definite on the good chart. Decorrelated-confirmed, with the `det M=0`-vs-positive-definite
  counterexample.
- **Most likely to break.** The OUTER tail integration of the coercivity weight `σ_min(L_θ)^{−2c'}` — the
  crude bound may be globally too coarse; the deeper (S,J) rung must prove `∫_tail σ_min(L_θ)^{−2c'} < ⊤`
  (the LAYER-2-style / corank-recursion σ_min integrability, banked-adjacent) OR a sharper anisotropic
  estimate. This is the SAME deeper rung both routes owe — but now det-inverse-free.
- **Next.** Commission the one-peel body on the NATIVE route: consume the banked inner slice; build the
  OUTER tail integration on the good∪deeper cover (the good chart via `σ_min(L_θ)≥κ`, the complement via the
  decorated (S,J) descent / a further `redChain` peel). Do NOT commission the casting (a)+(b). The det-inverse
  charter catch is resolved: it was an artifact, and the native re-expression is banked.
