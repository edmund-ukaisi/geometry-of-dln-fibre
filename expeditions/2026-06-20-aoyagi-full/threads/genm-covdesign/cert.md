# CoV domain-control certificate — `frontChartIntegral_lt_top` (the bounded route)

**Seat:** pen-and-paper (witness). **Task #110.** **Date:** 2026-07-10. **NO Lean.**
**Charge:** adjudicate + exhibit a BOUNDED-domain, Lean-friendly route for the per-pivot-chart
front-split integral, given the reduced-chain IH, WITHOUT the unbounded Schur image.
**Exact algebra:** `/tmp/cov_verify.py`, `/tmp/cov_verify2.py`, `/tmp/psi_test2.py`,
`/tmp/psi_cone.py`, `/tmp/pivot_charge.py`. **Decorrelated:** `codex/covdomain-{prompt,answer}.md`
(gpt-5.x, xhigh; my construction withheld — it independently reached the SAME obstruction and supplied
the scalar model that pins it).

---

## VERDICT (headline)

**NOT a wall — a bounded route exists — BUT the scoped "clean CoV → `reducedMorseFront`" route is
UNSOUND as stated, and the real content is a PIVOT CHARGE the current reduction omits.**

Three findings, all exact-confirmed and decorrelated:

1. **The loss does NOT split cleanly as `‖R‖² + frobSq(Z)`.** The exact split (verified `cov_verify.py`
   (1), diff `= 0`) is
   > `frobSq(A₀·P) = ‖R̃·α‖² + ‖R̃·B + S̃·Z‖²`   (α = the `q×q` pivot block; `R̃,S̃` = column blocks
   > of the sheared `A₀`; `Z` = reduced Schur block `= prod (redTail) Y`).

   The Morse block carries a factor `α`, and the "core" is coupled to `R̃,S̃`. Cleaning it to `‖R‖²`
   needs `R = R̃·α` — Jacobian `|det α|^{−m₀}`, a **determinant INVERSE**. So the normalslice-cert's
   claim (§3–4) that the loss splits as `‖R‖²+‖Z‖²` under a **unit** Jacobian is **incorrect for the
   loss/RLCT layer**: the compass's own det-inverse red flag fires exactly here. (The unit-Jacobian
   claim is correct only for the RANK identity `rank P = q + rank Z`, not the loss split.) The
   unbounded Schur image and this det-inverse are the **same** `α⁻¹` phenomenon.

2. **Direction (B) [unbounded whole-space] is REFUTED** (`cov_verify.py` (3)): the reduced product has
   degree `2(L−1)`, so `∫_{ℝ^{flatDim}} frobSq(prod redTail Y)^{−c''} dY` has radial tail
   `∫^∞ r^{flatDim−1−2(L−1)c''} dr`, **divergent for small `c''`** (`2(L−1)c'' < flatDim`). Rule (B) out.

3. **The chart integral's finiteness threshold is governed by a PIVOT CHARGE the front-peel
   accounting (`frontCharge q = m₀q + minAdm(redTail)`) does not carry.** Codex's scalar model
   (`m₁=m_L=q=1`, `P=a`, `A₀=x`): `frobSq(A₀P)=a²‖x‖²`, so
   > `J = (∫_{−1}^{1}|a|^{−2c'} da)·(∫_{[−1,1]^{m₀}}‖x‖^{−2c'} dx)`, finite ⟺ `c' < min(½, m₀/2) = ½`.

   The `< ½` is a **pivot charge** (codim-1 `{det α = 0}`), SEPARATE from the `m₀q/2` Morse charge.
   It matches `½·minAdm(M)` because `minAdm(M) = min_q frontCharge q` picks up the `q=0` term
   (`= minAdm(1,1) = 1`), NOT `frontCharge(q=1) = m₀`. **The pivot charge is how `minAdm`'s
   min-over-`q` sees the lower strata; the per-chart reduction at a fixed `q` must reproduce it.**

---

## THE OBSTRUCTION, PRECISELY (why the scoped route can't be a clean equality)

`reducedMorseFront M q c'` (banked finite, threshold `½·frontCharge q = ½(m₀q + minAdm redTail)`) is a
Morse-block-plus-reduced-core object. But (finding 3) the true chart-integral threshold is
`½·minAdm(M) ≤ ½·frontCharge q`, and can be **strictly smaller** (scalar: chart threshold `½` vs
`reducedMorseFront` threshold `m₀/2`). For `c' ∈ [½·minAdm, ½·frontCharge q)` the chart integral is
`+∞` while `reducedMorseFront < ⊤`. So **`frontChartIntegral ≤ C·reducedMorseFront` is FALSE on that
range** — the reduction is not a clean domination. Within the LEGAL range `c' < ½·minAdm` both are
finite, but the mechanism must **spend the pivot charge**, which `reducedMorseFront` does not model.

This is why "domain control of the unbounded Schur image" is the wrong framing: the unboundedness is
the `α⁻¹` blow-up, and it carries a real charge, not a mere technical enlargement of the domain.
`reducedMorseFront_lt_top` is **not wasted** — it is the correct **per-shell** endpoint (below); what
is unsound is applying it **once** to the whole chart. The pivot charge emerges from **summing** the
per-shell `reducedMorseFront` bounds over the dyadic `|det α|`-shells, not from `reducedMorseFront`
itself.

---

## THE BOUNDED ROUTE (route FOUND) — two mechanisations, one crux inequality

Both keep every integral over a **bounded** domain. Both need ONE new ingredient beyond the banked
bricks. The reduced (tail) half is fully dissolved; the pivot half is the genuine new content.

### Ingredient A (the tail half — the unbounded-image killer): **iterated Anderson's inequality**

`frobSq(prod redTail Y)` is a **PSD quadratic form in EACH factor `Y_i` separately** (multilinear
degree 1 in each, squared). So for the shift of any one factor, holding the others fixed, the integrand
`(Y_i^⊤ M Y_i)^{−s}` is **symmetric and unimodal** (superlevel sets = ellipsoids, convex symmetric).
**Anderson's inequality** (1955): for symmetric convex `K` and symmetric-unimodal `h`,
`∫_K h(y − s) dy ≤ ∫_K h(y) dy`. Iterating factor-by-factor (Fubini + Anderson in `Y_i`, others held):

> `∫_{∏_i (box − shift_i)} frobSq(prod redTail Y)^{−s} dY  ≤  ∫_{∏_i box} frobSq(prod redTail Y)^{−s} dY`
> `= routeMLayerBoxIntegral (redTail) s 1`  (the IH object, centred unit boxes).

This **exactly dissolves the unbounded Schur image**: the MP CoV sends the chart's reduced part to
`∫` over shifted unit boxes (each `Y_i = D_i − shift_i`, shift unbounded as `α→0`); Anderson dominates
it by the CENTRED unit-box integral = IH, **uniformly in the (unbounded) shift, constant `C = 1`.**
The pivot-independent "other" coordinates stay in the unit box, so the outer factor is `≤ IH·vol(box)`.

**Numerics (rigour of `C = 1`):** `psi_test2.py`, `psi_cone.py` — `Ψ(shift)/Ψ(0) ≤ 1` and DECAYS
(`~|shift|^{−2(L−1)s}`) for L=3 `(2,2,2)@q=1` across `c''∈{0.6,1.0,1.4}`, generic AND cone-aligned
worst-case shifts (max ratio `0.89`). Near-threshold `c''=1.49` shows `1.31` — MC noise (integrand
near-non-integrable), NOT a real breach; iterated Anderson gives `C=1` rigorously.

**Lean cost:** Anderson's inequality is **NOT in Mathlib** (no Anderson / Prékopa-Leindler / Brunn-
Minkowski / log-concave-rearrangement under `Analysis/Convex`, `MeasureTheory`). The needed instance
is narrow — `h = (PSD-quadratic-form)^{−s}` even + ellipsoidal superlevel sets — but is a genuine new
brick (an even, quasi-concave-superlevel translation-domination over a symmetric box).

### Ingredient B (the pivot half — the genuine missing charge): the pivot charge is codim-1, threshold `½`

`∫_{box} |det(q×q)|^{−2s} d(entries)` is finite ⟺ `s < ½` — for **every** `q` (`pivot_charge.py`:
`{det=0}` is a codim-1 hypersurface; its smooth points dominate, giving `P(|det|≤t) ~ t^1` with a
`log^{q−1}` correction — so `s = ½` is a log-borderline divergence, `s < ½` strictly converges). So
the pivot contributes **codim 1**, threshold `½`, independent of `q`.

Two ways to spend it inside a bounded route:

- **(B-shells) Disjoint dyadic shells in `|det α|`** — the FIX the failed nested `{|det|≥1/n}` cover
  missed. Decompose the chart `U = ⊔_{n≥0} Shell_n`, `Shell_n = {2^{−n−1} < |det P[ρ,κ]| ≤ 2^{−n}}`
  (disjoint, measurable, countable). On `Shell_n`, `‖α⁻¹‖ ≲ 2^n` is **bounded**, so `K = γα⁻¹` is
  bounded and the CoV maps `Shell_n × A₀-box` into a **bounded** radius-`~2^n` region → the banked
  `reducedMorseFront_lt_top`-at-radius-`2^n` (via the radius-scaling identity `I(T)=T^{exp}·I(1)`)
  applies per shell. The shell contribution `≲ vol(Shell_n)·2^{n·exp}·reducedMorseFront(1)`; with
  `vol(Shell_n) ≲ 2^{−n}` (codim-1) the sum is **geometric**, `∑_n 2^{n(exp−1)}`, convergent ⟺
  `exp < 1`. Codex's own scalar shell sum `∑ 2^{n(2c'−1)}` converges ⟺ `c' < ½` = `½·minAdm` — i.e.
  the geometric series converges **precisely on the legal range**, diverging only OUTSIDE it. (This is
  why the *nested* `{|det|≥1/n}` cover failed: it dropped the `vol(Shell_n)` decay; disjoint shells
  keep it.)
- **(B-split) AM-GM exponent split** (banked `rpow_add_split_le`): split `c' = s_M + s_p + s_r` with
  `s_M < m₀q/2`, `s_p < ½`, `s_r < ½·minAdm(redTail)`; a valid split exists ⟺
  `c' < ½(m₀q + 1 + minAdm redTail)`. Since `minAdm M ≤ m₀q + minAdm(redTail) < m₀q + 1 + minAdm(redTail)`,
  this covers ALL `c' < ½·minAdm M`. **Caveat:** this is tight only if the three charges sit on
  DISJOINT variable blocks; the actual loss `‖R̃α‖² + ‖R̃B+S̃Z‖²` **entangles** pivot × Morse (like the
  scalar product `a²‖x‖²`), so the split needs the entanglement handled (dominate `‖R̃α‖² ≥ …` fails;
  the honest handling is B-shells, where on each shell `α` is bounded so the entanglement is inert).

### The crux inequality (what a follow-on must verify exactly)

Both routes reduce to: **`exp − 1 < 0` for all `c' < ½·minAdm(M)`** (B-shells) / equivalently the pivot
+ Morse + reduced charges cover `minAdm(M)`. Verified in the scalar model (`= ½` exactly) and argued in
general via `minAdm M ≤ m₀q + minAdm(redTail)` + the codim-1 pivot slack. **NOT exhaustively checked
for width-general chains** — this is the one bookkeeping obligation to nail (the radius-scaling
exponent `exp` against the codim-1 shell-measure decay, per width-general chain).

---

## LEAN-FRIENDLY PLAN (what the follow-on tide formalises)

The scoped sorry `frontChartIntegral_lt_top` should be **re-shaped**, not closed against
`reducedMorseFront` as-is. Recommended decomposition:

1. **Keep** the front-split, pivot-chart cover (`pivotLocus_eq_iUnion`), MP shears
   (`measurePreserving_shearSub`), `blockShear_step`, `rank_eq_q_add_of_normalForm` — all banked, all
   consumed unchanged.
2. **Replace** the single `reducedMorseFront`-endpoint step with the **B-shells** assembly:
   - `pivotShellDecomp` : `frontChartIntegral = ∑_n (shell_n contribution)` (banked-shaped:
     `lintegral_iUnion_le` over the disjoint dyadic `{|det α|}`-shells; `det` continuous ⟹ measurable).
   - `shellContribution_le` : per shell, `‖α⁻¹‖ ≲ 2^n` ⟹ bounded CoV image ⟹ the banked radius-`T`
     scaling identity + `reducedMorseFront_lt_top` give
     `shell_n ≤ vol(Shell_n)·C·2^{n·exp}·reducedMorseFront M q (…)`.
   - `detSublevel_measure_le` : `vol{|det(q×q)| ≤ t} ≤ C·t·|log t|^{q−1}` (NEW brick; not in Mathlib —
     the codim-1 pivot-measure bound).
   - `geometricSum_lt_top` : `∑_n 2^{n(exp−1)} < ⊤` for `exp < 1` (from the crux inequality).
3. **Consumes the IH** `RouteMBoxThresholdFinite (redTail M q)` exactly as now (per shell, at the
   shifted exponent `c' − m₀q/2 < ½·minAdm(redTail)` via `shiftedThreshold`).
4. **Alternatively**, the conceptually cleanest single new brick is **Ingredient A (Anderson)**: it
   removes the shells entirely (dissolves the unbounded image in one step), at the cost of porting a
   (narrow) Anderson inequality to Mathlib. Recommend the reviewer/formaliser weigh B-shells (banked
   bricks + det-measure + geometric sum) vs Anderson (one deep new brick) for Lean tractability.

Banked bricks consumed either way: `lintegral_eq_polar` (only if the scaling identity is derived
radially), `radial_morse_residual_power_le` (the uniform Morse peel — handles the `A₀` unboundedness
for free, robustly correct), `blockShear_step`, `rank_eq_q_add_of_normalForm`, `pivotLocus_eq_iUnion`,
`measurePreserving_shearSub`, `reducedMorseFront_lt_top`, `shiftedThreshold`, `rpow_add_split_le`.

---

## CODEX (decorrelated, xhigh; my construction withheld) — CONCUR on obstruction, supplied scalar model

`codex/covdomain-{prompt,answer}.md`. Codex INDEPENDENTLY: (i) reached the same loss split
`‖X''G‖²+‖YZ‖²` with the Morse coefficient `G` degenerating as the pivot collapses; (ii) isolated the
**`|det G|^{−m₀}`** factor as uncontrolled by the reduced IH (= my `α`-factor / pivot charge, finding 1);
(iii) gave the **scalar model** pinning the pivot charge to `½` (finding 3); (iv) computed the dyadic
shell sum `∑ 2^{n(2c'−1)}` — which I read the OTHER way: it **converges** on the legal range
`c' < ½`, so it is the FIX, not the wall (Codex, only using `frontCharge(q)=m₀q` and not
`minAdm = min_q frontCharge`, concluded "wall"; correcting the `minAdm` min-over-`q` removes the wall).
The one place I depart from Codex: it declared "no bounded route on the whole chart"; that holds ONLY
under its incomplete charge inequality. With the correct `minAdm` accounting + the pivot charge spent
via disjoint shells (or Anderson), the bounded route closes.

---

## CLOSE

- **Firmest.** (a) The clean `‖R‖²+frobSq(Z)` unit-Jacobian split is FALSE — exact split
  `‖R̃α‖²+‖R̃B+S̃Z‖²`, cleaning needs `det(α)^{−m₀}` (pivot charge / det-inverse). (b) The pivot charge
  is codim-1, threshold `½`, is REAL and is the content the `frontCharge q` accounting omits. (c) The
  reduced-tail unbounded Schur image is DISSOLVED, rigorously `C=1`, by iterated Anderson's inequality
  (each factor a PSD quadratic form). (d) Direction (B) refuted; the bounded route exists via disjoint
  dyadic `|det α|`-shells (geometric series convergent exactly on `c' < ½·minAdm`) or Anderson.
- **Most likely to break / watch.** The width-general **crux inequality** (`exp < 1` per chain / pivot
  + Morse + reduced ≥ `minAdm`) — verified scalar, argued general, not width-general-exhaustive; and
  the entanglement `‖R̃α‖²` (handled on shells where `α` is bounded, NOT by a naive AM-GM split). Both
  new bricks (`detSublevel_measure_le`, or Anderson) are outside Mathlib.
- **Next.** (1) Formaliser/reviewer: verify the crux inequality exactly on a width-general chain (the
  radius-scaling `exp` vs the codim-1 shell decay). (2) Decide B-shells vs Anderson for Lean. (3)
  Surface to the controller that the carrier's `reducedMorseFront` target is **incomplete** (pivot
  charge) and `frontChartIntegral_lt_top` must be re-shaped around the shell decomposition (or Anderson),
  NOT closed against `reducedMorseFront` alone. This is a route re-shape, **not** a genuine wall.
