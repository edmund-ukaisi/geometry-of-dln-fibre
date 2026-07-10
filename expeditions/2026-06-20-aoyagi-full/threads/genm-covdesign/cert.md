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

---

# §CRUX-PROOF (follow-up 1 — the width-general crux, decorrelated-confirmed)

**Headline: the crux is NOT a clean `exp<1` bookkeeping check. Deeper exact analysis (mine + a second
decorrelated Codex, `codex/crux-{prompt,answer}.md`, my conclusion withheld) shows the `A₀`-integral
reduces `frontChartIntegral(M,q)` to a SAME-ARITY sub-problem `(m₀, redTail)`, which the carrier's
ARITY induction does NOT reach. The fix is an induction-measure change (total width); the residual
pivot-charge coupling is the genuine analytic core.**

## 1. The exact `A₀`-peel (mine + Codex agree term-for-term)

Block split `P = [[B,E],[C,D]]` (`B = P[ρ,κ]` invertible), `A₀ = [X | W]` (`X` = `m₀×q` pivot columns,
`W` = `m₀×(m₁−q)` non-pivot). Schur `Z = D − CB⁻¹E`, MP shear `X̃ = X + WCB⁻¹` (Jacobian 1):
> `frobSq(A₀P) = ‖X̃ B‖² + ‖X̃ E + W Z‖²`   (exact; `cov_verify.py`, `crux_verify.py`, diff `=0`).

The **non-pivot columns `W` enter only through `W·Z`** — and `W·Z = W·Y₁···Y_N` is the product of the
chain `N := (m₀, m₁−q, …, m_L−q) = (m₀, redTail)`.

## 2. The Morse peel + the pivot charge (Codex's exact form, adopted)

Whole-space `X̃`-peel, `S := [B E][B E]ᵀ = BBᵀ+EEᵀ` (`q×q`, PD), `Φ = I_{m₀}⊗S`, `d = m₀q`:
> pivot factor `(det Φ)^{−1/2} = (det S)^{−m₀/2} = |det B|^{−m₀}·det(I + B⁻¹EEᵀB⁻ᵀ)^{−m₀/2}`,
> residual core `w = tr((WZ)H(WZ)ᵀ) = ‖(WZ)H^{1/2}‖²`, `H = I − Eᵀ S⁻¹ E` (PD).

`w` is a PD-**output-metric** version of `‖WZ‖²`, **not** `‖WZ‖²` unless `E=0`; the comparability
constant is **not uniform as `B→singular`** (Codex, independently). This non-uniformity IS the pivot
charge — the same `α⁻¹` phenomenon as the unbounded image (finding 1 above).

## 3. SAME ARITY — the decisive structural fact (mine + Codex, exact factor count)

`(m₀, redTail)` has factors `W, Y₁,…,Y_N` = `1 + (L−1) = L` factors. `M = (m₀,…,m_L)` also has `L`
factors. **So the residual is SAME-ARITY as `M`, not the fewer-factor `redTail`.** The carrier's IH
`RouteMBoxThresholdFinite(redTail)` (arity `L−1`) does **NOT** cover it. The carrier's `reducedMorseFront`
(bare `redTail` + a detached isotropic `m₀q` Morse block) is the correct model ONLY on the measure-zero
stratum `{rank P = q}` (there `Z=0`, so `W` is FREE, `‖X̃E+WZ‖²=‖X̃E‖²` folds into the `X̃`-Morse); off
that stratum the `W·Z` coupling is a genuine SAME-ARITY front-integral the shortcut drops.

## 4. THE FIX: total-width induction + the exponent admissibility lemma (exact, 0 violations)

`Σ(m₀,redTail) = Σ(M) − Lq < Σ(M)` for `q ≥ 1` (Codex + `minadm_check.py`). So **induct on total width
`Σ = ∑ m_i` (or lex `(arity, Σ)`)**; then `(m₀,redTail)` is strictly smaller and the IH reaches it. The
current ARITY induction is the wrong measure.

Exponent budget: the reduced problem `routeMLayerBoxIntegral(m₀,redTail; s)`, `s = c'−m₀q/2`, is finite
iff `s < ½·minAdm(m₀,redTail)`. From `c' < ½minAdm(M)`: `s < ½(minAdm(M) − m₀q)`. So need the **ℕ
admissibility lemma**
> **(b)  `minAdm(M) ≤ m₀q + minAdm(m₀, redTail M q)`.**

`minadm_check.py` (exact `minAdmRec`, 4000 chains `L∈{2,3,4}` widths `≤4` × ALL coranks `q`): **(b) has
0 violations.** Contrast **(c) `minAdm(M) ≤ minAdm(m₀,redTail)`: 1936 violations** — so the `m₀q`
Morse charge is ESSENTIAL (no same-exponent direct bound; the peel cannot be skipped). Note
`minAdm(m₀,redTail) ≤ minAdm(redTail)` (prepending can only lower `minAdm`, via the `q'=0` branch), so
(b) is STRICTLY STRONGER than the banked frontCharge `minAdm(M) ≤ m₀q + minAdm(redTail)` — (b) is a
genuine NEW ℕ-lemma, provable from the `minAdmRec` layer-peel (the `t=q` peel branch of `(m₀,redTail)`).

## 5. The residual analytic core (honest — NOT a clean geometric series)

I must **retract the optimistic B-shells `exp<1` reading** of §THE BOUNDED ROUTE above: the naive shell
accounting DIVERGES. On `Shell_n = {|det B|~2^{−n}}`, the pivot factor `(det S)^{−m₀/2} ≤ |det B|^{−m₀}
~ 2^{nm₀}` while `vol(Shell_n) ~ 2^{−n}`, giving `∑ 2^{n(m₀−1)}` — **divergent for `m₀ ≥ 1`** unless the
sub-problem DECAYS on the shell. It does decay (`Z ~ B⁻¹ ~ 2^n` blows up ⟹ `∫_W‖WZ‖^{−2s} ~ 2^{−2ns}`),
but ALSO `det S ~ O(1)` (not `2^{−n}`) precisely WHEN this pivot is comparable to the largest minor —
i.e. the balance holds **only on the dominant-minor sub-chart** `{|det B| ≳ max_μ|det μ|}`, NOT on the
whole chart `{det B ≠ 0}`. And the factorized bound `∫(det S)^{−m₀/2}·routeMLayerBoxIntegral(m₀,redTail)`
is invalid: `∫_{box}(det S)^{−m₀/2}` alone is finite only iff `m₀ < m_L−q+1` (codim-`(m_L−q+1)`
locus `{rank[B E]<q}`), which FAILS for `m₀` large. **The pivot charge and the `(m₀,redTail)` sub-problem
are genuinely COUPLED; no factorization closes them.**

## 6. Crux verdict

- **STRUCTURALLY SOUND & DECISIVE** (mine + decorrelated Codex + exact `minAdm`): the reduction is
  `frontChartIntegral(M,q) → (m₀,redTail)` SAME-ARITY; the fix is **total-width induction**; the
  exponent lemma **(b) holds (0 violations)**; the Morse charge is essential **(c) fails**.
- **NOT a clean `exp<1` bookkeeping check** (my follow-up-1 charge): the residual pivot-charge×sub-problem
  coupling is the genuine analytic content, controlled ONLY on dominant-minor sub-charts (ties back to
  the finite cover), not by a factorized bound or a naive shell sum.
- **NOT a wall** (truth: `frontChartIntegral ≤ routeMLayerBoxIntegral(M)` = Aoyagi-finite). But the
  `reducedMorseFront` shortcut does **not** close — the route needs the `(m₀,redTail)` recursion under
  total-width induction, and the coupled pivot charge is real.

---

# §ROUTE-DECISION (follow-up 2 — B-shells vs Anderson at Mathlib v4.29)

**Mathlib v4.29 inventory** (`.lake/packages/mathlib`, confirmed): HAS `MeasureTheory/Integral/Layercake`
(Cavalieri: `∫f = ∫ measure{f>t}`). MISSING: coarea formula, semialgebraic/polynomial-sublevel-measure
tools, Anderson's inequality, Prékopa–Leindler, Brunn–Minkowski, log-concave rearrangement (none under
`Analysis/Convex`, `MeasureTheory`).

**The decision is dominated by §CRUX-PROOF, not by B-shells-vs-Anderson.** Neither tool closes the crux
alone, because BOTH address only the reduced-tail/domain half and NOT the coupled pivot charge (§5):

| | B-shells | Anderson |
|---|---|---|
| new brick | `detSublevel_measure_le` (`vol{|det|≤t} ≤ C·t·|log t|^{q−1}`) | Anderson ineq. for `(PSD-quad)^{−c'}` |
| in v4.29? | NO (Layercake helps the layer-cake step, but the codim-1 det-measure bound is from-scratch) | NO (from-scratch; narrow even/ellipsoidal-superlevel case) |
| cost | medium (det-measure via Fubini on the last row: `det` linear in it ⟹ slab of width `~t`, a `log` from the cofactor) | medium (even + convex-symmetric superlevel translation-domination over a box) |
| what it buys | keeps each shell bounded | dissolves the shifted-box→centred-box (the unbounded image), rigorously `C=1` |
| closes crux? | **NO** — naive shell sum diverges (§5); needs dominant-minor sub-charts | **NO** — handles reduced tail, NOT the pivot charge |

**RECOMMENDATION (in priority order):**

1. **PREREQUISITE re-architecture (carrier level, before any tide):** change the recursion to
   **total-width (or lex `(arity, Σ)`) induction**, and make the reduced problem `(m₀, redTail)` — i.e.
   `RouteMBoxThresholdFinite` proved for all chains of smaller `Σ`, and `frontChartIntegral(M,q)` reduces
   to `routeMLayerBoxIntegral(m₀,redTail; c'−m₀q/2)`. Land the ℕ admissibility lemma **(b)** (new,
   0-violation-verified, provable from `minAdmRec`). This is the load-bearing fix; without it the
   recursion is not well-founded on the actual residual.

2. **For the reduced-tail domain (the unbounded image):** **Anderson** is the cleaner tool (dissolves it
   in one step, `C=1`, no shells, no det-measure). Port the narrow case: `h = (x↦x^⊤Mx)^{−c'}` (`M` PSD)
   is even with ellipsoidal (convex-symmetric) superlevel sets ⟹ `∫_{box−s} h ≤ ∫_{box} h`; iterate
   per factor. Proof sketch: reduce to the 1-D even-unimodal case along each axis via Fubini + the
   symmetric-decreasing rearrangement of an interval, OR cite Anderson (1955) directly if a Mathlib port
   of Brunn–Minkowski/Prékopa lands. Prefer this over B-shells (avoids the det-measure brick).

3. **For the residual pivot charge (§5 — the genuine hard core):** isolate as a NAMED sub-lemma
   `pivotCharge_coupled_lt_top` and treat on **dominant-minor sub-charts** (`{|det B| ≳ max_μ|det μ|}`,
   finite cover via `pivotLocus`-style), where `det S ~ |Λ^q P|` is comparable to the largest minor so the
   pivot factor is controlled by the reduced decay. This is where Aoyagi's actual §5 recursive resolution
   may be unavoidable — flag to the operator that the `reducedMorseFront` shortcut is insufficient and the
   coupled pivot charge is the last real analytic obligation.

**Bottom line for the tide:** do **not** spin a Lean tide against `frontChartIntegral_lt_top → reducedMorseFront`
as currently shaped — it will not close (same-arity residual + coupled pivot charge). Spin instead: (i) the
ℕ lemma (b) [safe, banked-shaped], (ii) the total-width induction refactor of the carrier, (iii) the
Anderson brick for the reduced domain, and hold (iii+pivot charge) behind a reviewer pass on whether the
recursion genuinely closes or needs Aoyagi's full resolution. The truth is guaranteed; the shortcut is not.

---

# §COUPLED-PIVOT-RESOLUTION (follow-up 3 — the strategic fork, definitive)

**FORK: does the total-width front-peel recursion CLOSE the coupled pivot charge (on dominant-minor
sub-charts), or is Aoyagi's §5 rank-flag resolution required?**

**VERDICT: the per-corank front-peel does NOT close it. The whole-space-Morse-peel UPPER BOUND
DIVERGES at the deeper stratum `{rank P = q−1}` (exact, ~48–85% of `(M,q)` — below), because the bound
is LOSSY exactly where one Morse eigenvalue flattens (the corank drops `q → q−1`). The true `J` is finite
(`J ≤ ∫_{full box} =` Aoyagi), so this is a METHOD failure, not a divergence — and the fix is precisely
what Codex-consult-#1 named: "an additional bounded-domain induction over lower-rank strata", i.e. resolve
the rank flag `{rank≤q} ⊃ {rank≤q−1} ⊃ …` SIMULTANEOUSLY = Aoyagi §5's iterated blow-up / the charter's
native `(S,J)` recursion. The front-peel-to-`reducedMorseFront` is a shortcut that cannot reach the deeper
strata.**

## The positive attempt, and exactly where it fails

On the dominant-minor sub-chart `V = {(ρ,κ) is the largest q-minor}` (finite cover of `{rank≥q}`, the
only place `det S ≍ (det B)²` is controlled — §5 above): peel `X̃` by the whole-space bound. Track the
net power of `det B` as `A' → V`'s boundary `{det B=0}`, which on `V` is exactly `{rank P < q}` (largest
minor vanishes):
- (i) `det S = ∑_{|T|=q} det(P[ρ,T])² ≍ (det B)²` on `V`  ⟹  pivot factor `(det S)^{−m₀/2} ≍ |det B|^{−m₀}`.
- (ii) `B → rank q−1`, `B⁻¹ = adj(B)/det B`, `adj(B)` rank 1 ⟹ `Z = D − CB⁻¹E ≍ |det B|^{−1}·(rank-1)`.
- (iii) `∫_W ‖WZ‖^{−2s} dW ≍ |det B|^{2s}·const` (the blow-up direction is rank 1; `WZ` a rank-`m₀`
  Morse in `W`, finite for `2s < m₀`), `s = c'−m₀q/2`.
- (iv) **The whole-space bound is LOSSY here:** `S = [B E][B E]ᵀ` has rank `< q` at `{rank P<q}` (the `q`
  rows of `P` are dependent), so one `X̃`-Morse eigenvalue `→ 0`; the whole-space `(det S)^{−m₀/2}→∞`
  overestimates, whereas the true **box** `X̃`-integral keeps that flat direction bounded ⟹ effective
  corank `q−1` (Morse charge `m₀(q−1)`, residual exponent `c'−m₀(q−1)/2`). The one-corank bound uses
  charge `m₀q` uniformly — **wrong near `{rank=q−1}`**.

Net whole-space-peel integrand `≍ |det B|^{−(m₀−2s)} = |det B|^{−θ}`, `θ = m₀(q+1) − 2c'`. Since on `V`
`det B ≍ dist(A', {rank<q})`, `∫_V |det B|^{−θ}` converges iff `θ < D := codim{rank(tail prod)≤q−1}`.
At the worst exponent `c' = ½minAdm(M)`: `θ = m₀(q+1) − minAdm(M)`.

**Exact checks** (`fork_check.py`, `fork_codim.py`): `θ ≥ 1` (naive codim-1) in **85%** of `(M,q)`;
`θ ≥ D` (with a single-bottleneck codim PROXY for `D`) in **~48%**. Either way the per-corank
whole-space-peel bound **diverges in a large fraction of chains**, for `c'` up to `½minAdm`. The
divergence persists for the generic term `q = tailMin` (so it is not dodged by the measure-zero subtlety
of the lower strata). **The one-corank method's upper bound is not finite.**

*(Loose end, flagged: `D` used a single-bottleneck PROXY; the sharp verdict wants the EXACT product-rank
codim `codim{rank(A₁···A_{L-1}) ≤ q−1}`. The qualitative conclusion — the bound diverges commonly — is
robust to the proxy, and independently: the corank-drop lossiness (iv) is exact and is itself the
obstruction, regardless of `D`.)*

## What Aoyagi §5 provides that the front-peel lacks

The obstruction is that `frobSq(A₀P)` near `{rank P = q−1}` behaves like a corank-`(q−1)` singularity, near
`{rank=q−2}` like corank-`(q−2)`, etc. — the singularity is **stratified along the entire rank flag**, and a
single-corank Morse peel over-charges every deeper stratum. Aoyagi §5's resolution blows up the flag
`{rank≤q} ⊃ {rank≤q−1} ⊃ … ⊃ {0}` in one **iterated** construction, producing a normal-crossing (monomial)
form whose integral is manifestly finite by reading exponents — resolving ALL coranks simultaneously. This
is a **BOUNDED build** (Aoyagi carries it out explicitly for DLN), and it is exactly the charter's original
**native `(S,J)` recursion** (the `diag(b)` ledger threading the rank-flag state) that the front-peel
attempted to shortcut. Its shape/size: the `(S,J)` joint resolution the STRATEGY section of `stage2-brief.md`
already names — coordinate radial blow-ups + det-1 unit clears + absorption-by-renaming, indexed by the
rank flag; substantial but Aoyagi-guided and bounded.

## Consequence for the strategy

- The `reducedMorseFront` / one-corank front-peel is **insufficient in principle** (not just missing a
  lemma) — confirmed by exact exponent analysis. `frontChartIntegral_lt_top` cannot be discharged by it.
- **Pivot to the native `(S,J)` resolution** (charter's original plan). The total-width induction + ℕ-lemma
  (b) + Anderson are still useful WITHIN it (the reduced-tail domain, the arity/width bookkeeping), but the
  load-bearing new content is the rank-flag blow-up, not a domain patch.
- **Not a wall** (truth guaranteed: `J ≤ ∫_{full box}` = Aoyagi-finite). It is a **route re-selection**:
  the front-peel shortcut → the native rank-flag resolution.

## Decorrelation status — CONFIRMED (fresh fork consult landed)

- **Codex-consult-#3 on THIS fork (`fork-answer.md`, xhigh, my lean withheld) CONFIRMS the verdict
  term-for-term:** *"the one-corank whole-space peel does not close. The deeper stratum `rank P = q−1`
  is a genuine obstruction unless the proof state is refined to a rank-flag / iterated blow-up
  recursion… use the full `(S,J)` / `diag(b)` rank-flag recursion, not a one-corank front-peel followed
  by an undecorated reduced-chain IH."* It independently derived `det S ≍ |Δ|²` (pivot factor
  `|Δ|^{−m₀}`), the corank-`(q−1)` reorganisation of the box `X`-integral (my point (iv)), and
  `θ > m₀ ≥ 1 ⟹` the determinant-shell estimate diverges — with the true `J` finite (*"a failure of
  the method's bound, not of the integral"*).
- **One refinement adopted from #3 (sharpens, does not change the verdict):** on the DOMINANT-minor
  sub-chart the apparent `Z ≍ Δ^{−1}` pole (my (ii)) is TAMED — the dominance inequalities force the
  singular row/col components of `C, E` to vanish to order `Δ`, so `Z ≍ Δ·Γ` (Codex), or `O(1)` (my
  recomputation), NOT `Δ^{−1}`. So the exact net exponent is **analysis-dependent** (`θ = m₀(q+1)−2c'`
  [my (ii)] vs `θ = m₀+2s = 2c'−m₀(q−1)` [Codex, cleaner] vs `θ = m₀` [Z bounded]) — but **ALL THREE
  give `θ ≥ 1`, so the whole-space-peel bound diverges regardless.** The verdict is robust to which
  `Z`-asymptotic is correct; pinning the exact `θ` (and the exact product-rank codim `D`) is a
  reviewer sharpening, NOT verdict-affecting.
- Codex-consult-#1 (`covdomain-answer.md`) had already independently named the fix ("an additional
  bounded-domain induction over lower-rank strata"); consult-#2 (`crux-answer.md`) confirmed the
  same-arity structure. **Three decorrelated passes now agree.** (Consult-#3 failed to run 3× on
  environment issues before landing once Codex recovered — noted for the record.)

## Firmest / watch / next

- **Firmest.** The one-corank whole-space-peel bound diverges at `{rank<q}` (exact; lossy corank-drop);
  `reducedMorseFront` cannot close `frontChartIntegral_lt_top`; the rank flag needs simultaneous
  resolution (= native `(S,J)`). NOT a wall (truth guaranteed).
- **Watch.** The exact product-rank codim `D` (proxy used) — a reviewer/next-scout should pin it to make
  the exponent verdict fully sharp; and re-run the failed fork consult to decorrelate.
- **Next.** Controller decision: **pivot the Lean effort from front-peel-to-`reducedMorseFront` to the
  native `(S,J)` rank-flag resolution** (Aoyagi §5). Keep (b)/total-width/Anderson as sub-tools. The
  `frontChartIntegral_lt_top` sorry should be re-scoped as the endpoint of the `(S,J)` resolution, not the
  reducedMorseFront reduction.

> ⚠️ **THE ABOVE §COUPLED-PIVOT-RESOLUTION VERDICT IS RETRACTED — see §CONCESSION below. The front-peel
> DOES close; no `(S,J)` mountain is needed. The error was mine.**

---

# §CONCESSION (follow-up 4 — `forkreview` REFUTES the no-go; I concede, with independent verification)

**`forkreview` is CORRECT. I withdraw the "needs Aoyagi §5" verdict. The deeper stratum `{rank P=q−1}`
is intrinsically INTEGRABLE — a local, bounded-domain, per-stratum matter — and the front-peel CLOSES.
This vindicates the much cheaper route.**

## My exact error

I correctly showed the whole-space Morse peel `(det S)^{−m₀/2}` is LOSSY at `{rank=q−1}` (a Morse
eigenvalue flattens). **But I then quantified the divergence with the LOSSY exponent** `θ_lossy` instead
of the true box exponent. The decisive 1-D fact I stated but failed to USE:
> `∫_{−1}^{1}(σ²z² + w)^{−c'} dz → 2·w^{−c'}` (bounded) as `σ→0` — **no `σ^{−1}`**. The `σ^{−1}` blow-up
> is the whole-LINE behaviour; the bounded box keeps the collapsing direction at `O(1)`.

So the true integrand `g(P) = ∫_{A₀ box} frobSq(A₀P)^{−c'} dA₀` scales, as `σ_q → 0` (`P → rank q−1`),
with the **box** exponent
> `α = max{0, 2c' − m₀(q−1)}`  (log-borderline at `2c' = m₀(q−1)`),

NOT `θ_lossy`. The only power blow-up is from the `m₀(q−1)` STABLE directions squeezed into a radius-`σ`
ball; the collapsing direction contributes `O(1)`.

## The linchpin closes it (exact, verified)

`∫_{A'} g` near `{rank P ≤ q−1}` converges iff `α < D := codim{rank(tail prod) ≤ q−1}`. The geometric
linchpin (`forkreview`, RlctPayoff:117): `{rank P≤q−1} ∩ {A₀ kills the (q−1)-dim image} ⊆` zero-product
locus (codim `= minAdm(M)`), so `codim = D + m₀(q−1) ≥ minAdm(M)`, i.e.
> **`minAdm(M) ≤ D + m₀(q−1)`.**

Hence for `c' < ½minAdm(M)`: `α = 2c' − m₀(q−1) < minAdm(M) − m₀(q−1) ≤ D`. **`α < D` — CONVERGES.**
(`c' = ½minAdm` gives `α = D` — the log-borderline, correctly excluded by the strict threshold.)

## Independent verification (decorrelated from BOTH forkreview and my old framing)

- **Linchpin `minAdm(M) ≤ D + m₀(q−1)`: 0 violations / 546** single-matrix chains (`linchpin.py`, `D`
  EXACT determinantal `(m₁−q+1)(m_L−q+1)`). `α < D` for `c' < ½minAdm`: holds always (the 179 "`α≥D`"
  are all the `c'=½minAdm` borderline equality `α=D`, excluded by strictness).
- **My OWN MC (independent of forkreview): `d log g / d log σ_q = −0.75`** for `m₀=2, q=3, c'=2.4`
  (`box_scaling.py`) — matches `α = 2c'−m₀(q−1) = 4.8−4 = 0.8`, refutes any `σ^{−m₀}`-type blow-up.
- **A NEUTRAL fresh Codex (`fork-neutral-answer.md`, xhigh, withholding BOTH `θ_lossy` AND `θ_true`,
  NOT told the whole-space peel is "the method")** independently derived `α = max{0, 2c'−m₀(q−1)}`, the
  box-vs-whole-line `σ^{−1}` point verbatim, `α < D` via the linchpin, and the verdict: *"the deeper
  stratum {rank P=q−1} is intrinsically integrable for c'<½minAdm(M). It is NOT a genuine obstruction
  requiring a global simultaneous rank-flag resolution. It is a local bounded-domain, per-stratum
  matter."*

## Why my 3 earlier consults agreed with me (the correlation `forkreview` flagged — CONFIRMED)

All three of my fork/crux/covdomain consults were framed around the **whole-space Morse peel as "the
method"** and asked about ITS bound. They correctly reported that the *lossy bound* diverges — which is
true of that bound but NOT of the intrinsic integral. My framing correlated them. `forkreview`'s neutral
framing (withhold both conclusions, ask for the intrinsic scaling) is the correct decorrelation, and the
neutral Codex reproduced it independently. **Lesson: a consult inherits the framing's error; decorrelate
the FRAMING, not just the model.**

## Corrected verdict + strategy

- **The front-peel CLOSES.** `frontChartIntegral_lt_top` is provable as a **local, per-corank, box
  bound**: peel the `m₀(q−1)`-effective-corank stable directions, keep the collapsing direction bounded
  (box), and integrate `g ≍ σ^{−α}` against the deeper stratum's codim `D` using the linchpin
  `minAdm ≤ D + m₀(q−1)`. NO simultaneous rank-flag / `(S,J)` resolution required.
- **The load-bearing NEW ingredients** (all bounded, local): (i) the box exponent lemma
  `g ≍ σ^{−max{0,2c'−m₀(q−1)}}` (the box keeps the collapsing direction `O(1)`); (ii) the geometric
  linchpin `minAdm(M) ≤ D + m₀(q−1)` (via the zero-product containment, RlctPayoff:117); (iii) the exact
  product-rank codim `D = codim{rank(tail prod)≤q−1}`. Plus the earlier-correct pieces (ℕ-lemma (b),
  Anderson for the reduced domain, total-width/arity bookkeeping).
- **Retained-correct from my earlier passes:** the exact `A₀`-Schur loss split (`‖X̃B‖²+‖X̃E+WZ‖²`); the
  vslice §3–4 unit-Jacobian-loss-split error; the same-arity `(m₀,redTail)` observation (still true — it
  is handled per-stratum by the box bound, not a mountain); `reducedMorseFront` as-shaped is still
  insufficient (needs the box corank-drop treatment), but the FIX is local, not `(S,J)`.
- **What was WRONG:** the `θ_lossy` divergence and the "needs Aoyagi §5" verdict. Retracted.

The controller's task #111 ("native `(S,J)` resolution") can be **DOWNSCOPED**: the target is the local
box-bound closing `frontChartIntegral_lt_top` via the linchpin, not the full `(S,J)` mountain. A cheaper
finish.
