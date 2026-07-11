# genm-catint — is the single-minor bound SUFFICIENT to prove Cat I integrability?

**Seat:** pen-and-paper (obstruction — adjudicating one truth-value). **Task:** the `cbmin` single-minor
lower bound `det(Q_b Q_bᵀ) ≥ minor_{S₀}(Q_b)²` gives the weight upper bound `det^{−a/2} ≤ |minor_{S₀}|^{−a}`.
Does that upper bound PROVE `∫ det^{−a/2} < ∞` over the good stratum for `a` up to `q−b` (Cat I), as
`genm-wtint`'s verdict claims ("sufficient AND sharp"), or only for `a < 1`? **NO Lean.** **Exact algebra:**
`/tmp/catint_check.py`, `/tmp/catint_numeric.py`, `/tmp/catint_thresh.py`, `/tmp/catint_schur.py`.
**Decorrelated:** `/tmp/catint_codex_prompt.md` + `/tmp/catint_codex_out.md` (gpt-5.x, xhigh; my lean
WITHHELD — asked open-ended "for which `a` does `∫|minor_{S₀}|^{−a}` converge vs `∫det^{−a/2}`; same or
different threshold").

---

## VERDICT: **(B) — the single-minor bound is INSUFFICIENT for `a ≥ 1`.**

The single-minor upper bound `det^{−a/2} ≤ |minor_{S₀}|^{−a}` proves integrability **only for `a < 1`**, not
up to `a = q−b`. `genm-wtint` **over-claimed** on the specific point that the single fixed minor is
"sufficient AND sharp" and that "integrability reduces to a single polynomial's power over the transverse
`ℝ^{q−b+1}` (the `a < q−b+1` test)". That reduction is wrong: **a single `b×b` minor is one polynomial, so
`{minor_{S₀}=0}` is a hypersurface (codim 1); it vanishes to order 1 in ONE transverse coordinate, giving
`∫ |minor_{S₀}|^{−a} ≍ ∫ |z₁|^{−a}` — finite iff `a < 1`, independent of `q−b+1`.** The `a < q−b+1`
threshold belongs to `det^{1/2} ≍ ‖z‖` (the FULL transverse radius over `ℝ^{q−b+1}`), which no single minor
reproduces when `q > b`.

The **result** (Cat I converges) is not in dispute — `a ≤ q−b < q−b+1`, and the true integral converges.
What fails is the **proof route**: `cbmin`'s bound cannot certify it for `a ∈ [1, q−b]` (the upper half of
Cat I, non-empty whenever `q > b` — exactly when Cat I is non-trivial past `a<1`).

`genm-wtint`'s WALL conclusion (Cauchy–Binet is load-bearing, not absorbable) stands; only its downstream
"one minor suffices, sharp" corollary is wrong. The correct minimal fact is the **two-sided** comparability
on a dominant-minor chart (needs the full `Σ`-sum), or the determinantal local model `det ≍ ‖z‖²` directly —
strictly more than `cbmin`.

---

## The certifying computations (exact)

**Cert 1 — `b=1, q=2, a=1` (in Cat I: `a ≤ q−b = 1`). `/tmp/catint_check.py`.**
`Q_1 = (x,y)`, `det(Q_1 Q_1ᵀ) = x²+y²`. Cauchy–Binet minors are the `1×1` minors `x, y`; single-minor
bound `det ≥ x²`, weight `≤ |x|^{−a}`.

- TRUE: `∫_{r<1}(x²+y²)^{−a/2}dxdy = 2π∫_0^1 r^{1−a}dr`; at `a=1` this is `2π` (**finite**).
- BOUND: `∫_{|x|,|y|<1}|x|^{−a}dxdy = (∫_{-1}^1|x|^{−a}dx)·2`; at `a=1`, `∫_0^1 x^{−1}dx = [\ln x]` **diverges
  (log)**. So the single-minor upper bound is `+∞` at `a=1`, while the true integral is `2π`.

**Cert 2 — `b=2, q=3`. `/tmp/catint_check.py`.** Cauchy–Binet `det(Q Qᵀ) = m_{12}²+m_{13}²+m_{23}²`
(residual 0). At `Q = [[1,0,0],[0,0,1]]`: `m_{12}=0` but `det = 1` (rank 2, weight finite). So `{m_{12}=0}`
contains rank-2 points where `|m_{12}|^{−a} → ∞` while the true weight is bounded — the bound is lossy on a
**codim-1 hypersurface** strictly larger than `{det=0}` (codim `q−b+1 = 2`).

**Cert 3 — numeric divergence/convergence gap, `b=2, q=3, a=1`. `/tmp/catint_numeric.py`.** MC over `[−1,1]⁶`:
`∫det^{−1/2}` mean stabilises at `≈143.5`, max stable (finite); `∫|m_{12}|^{−1}` mean grows `1553→6070` and
max grows `10⁵→10⁷` with `N` (heavy tail = log divergence). The bound diverges where the true integral
converges.

**Cert 4 — the threshold gap, exact. `/tmp/catint_thresh.py`.** Transverse `ℝ^n`, `n = q−b+1`:
`∫‖z‖^{−a} ≍ ∫ r^{n−1−a}dr` finite iff `a < n = q−b+1`; `∫|z₁|^{−a} = (∫|z₁|^{−a}dz₁)·vol` finite iff
`a < 1` (independent of `n`). The single minor controls `|z₁|` (one coordinate), det^{1/2} controls `‖z‖`.

**Cert 5 — the clean top-stratum local model, exact. `/tmp/catint_schur.py`.** Gram–Schur identity, max
relative error `4.5e−9` over 20000 random `(b,q)`:

    det(Q_b Q_bᵀ) = det(G_{b−1}) · ‖z‖²,   z = orthogonal residual of the last row against the
                                            span of the first b−1 rows,  z ∈ ℝ^{q−b+1}.

`det(G_{b−1})` is bounded away from 0 near a smooth rank-`(b−1)` point, so `det ≍ ‖z‖²` and
`∫ det^{−a/2} ≍ ∫_{ℝ^{q−b+1}} ‖z‖^{−a}dz`, finite iff `a < q−b+1`. **This is the elementary radial model
that actually closes the top stratum — and it is NOT the single-minor bound.**

---

## Why the dominant-minor cover works but is NOT `cbmin`

The only route by which a minor bound closes Cat I is a **cover** `C_S = {|m_S| ≥ |m_T| ∀T}`. On `C_S`,
Cauchy–Binet gives the **two-sided** bound (verified `det/max_S m_S² ∈ [1,3]` for `b=2,q=3`,
`/tmp/catint_numeric.py`):

    m_S² ≤ det = Σ_T m_T² ≤ N·m_S²   (N = C(q,b)),   so  det^{1/2} ≍ |m_S|  on C_S.

The **upper** half `det ≤ N·m_S²` is what forces `{m_S=0} ∩ C_S = {det=0}` (dominance kills the extra
hypersurface directions), so on `C_S` the minor recovers `|m_S| ≍ ‖z‖` (full radius) and the chart integral
is `≍ ∫‖z‖^{−a}`, threshold `a < q−b+1`. But that upper half **is the full `Σ`-sum** — it is NOT provided by
`cbmin`'s single-term lower bound, and the per-chart finiteness still ultimately rests on `det ≍ ‖z‖²`. So
the repair is real, but its load-bearing input is the two-sided comparability + the determinantal local
model, strictly beyond `cbmin`.

---

## Codex independent read (my lean withheld — quoted)

> **Q1 (single minor):** "the fixed-minor integral converges exactly for `0 < a < 1`, not up to `q−b` in
> general. … a single `b×b` minor is one polynomial. Its zero set is a hypersurface, codimension 1, and at
> smooth points it vanishes to order 1 in one transverse coordinate. It does not see the full codimension
> `q−b+1` rank-drop geometry."

> **Q2 (true integral):** "converges exactly for `0 < a < q−b+1`. … By the Gram determinant Schur
> complement, `det(QQᵀ) = det(G_{b−1})·‖z‖²` … `det(QQᵀ)^{−a/2} ≍ ‖z‖^{−a}` … `∫_0^ε r^{c−1−a}dr` converges
> iff `a < c = q−b+1`." (Plus the SVD-Jacobian global argument: `dQ ∼ ∏σ_i^{q−b}∏_{i<j}|σ_i²−σ_j²|dσ`,
> `det^{−a/2}=∏σ_i^{−a}`, integrability near `σ_i=0` needs `q−b−a > −1`.)

> **Q3 (comparison):** "the thresholds are different when `q > b`. Single fixed minor: `a < 1`. True Gram
> determinant: `a < q−b+1`. Simplest explicit instance: `b=1, q=2, a=3/2` … `∫(x²+y²)^{−3/4}` finite,
> `∫|x|^{−3/2} = ∞`."

> **Q4 (chart repair):** "yes, but only with a dominance/comparability fact using all minors, not from the
> single-minor lower bound alone. … `m_S² ≤ det ≤ N·m_S²` … So the repair works, but it ultimately relies on
> the true local structure of `det(QQᵀ)` as a sum of squares of all minors. It is not a consequence of the
> single fixed-minor inequality alone."

> **Final:** "does the single-minor bound suffice for `a` up to `q−b`? **NO in general.** It only gives
> `a < 1`; the true threshold is `a < q−b+1`."

Fully decorrelated agreement with (B): the `a<1` single-minor threshold, the `a<q−b+1` true threshold, the
codim-1-hypersurface mechanism, the Gram–Schur local model, and the cover needing the full `Σ`-sum.

---

## Follow-up — does Cat I fold into the operator-gated determinantal atom?

**No. The Cat I top stratum is SEPARABLE and elementary; it does NOT enlarge the operator-gated atom — but
it is above `cbmin`.**

- **The binding stratum for the emitted weight is the TOP stratum `{rank Q_b = b−1}`** (`genm-wtint` §"Deeper
  strata are non-binding": deeper strata `{rank ≤ b−r}` give the weaker condition `a < q−b+r`, `r ≥ 2`). So
  Cat I integrability is a **top-stratum** question.
- **The operator-gated atom (`genm-cornrev`) is scoped to the DEEPER strata `{rank ≤ b−2}`, `b ≥ 2`**, not
  the top stratum. `cornrev/review.md` §3 and its "sufficient conditions" list the **top stratum
  `{rank=b−1}` at any width as CLOSING** (elementary), with the atom = the deeper strata. So Cat I does not
  fold into the atom; the atom's `{rank≤b−2}` boundary and decbuild's `(□)` "buildable above the atom" line
  are drawn where `cornrev` drew them. Cat I sits on the *buildable* side.
- **But the buildable top-stratum route is the `det ≍ ‖z‖²` model (Cert 5), NOT `cbmin`.** `cbmin`'s
  single-minor bound reaches only `a < 1`; it is **below** the boundary for Cat I when `q > b`. The Cat I
  formaliser must build the Gram–Schur local model `det(Q_b Q_bᵀ) = det(G_{b−1})·‖z‖²` → radial
  `∫_{ℝ^{q−b+1}}‖z‖^{−a}` (or the dominant-minor cover with the two-sided Cauchy–Binet comparability),
  **not** discharge Cat I from `cbmin` alone.
- **One refinement to flag on `cornrev`'s top-stratum closure.** `cornrev` verified the top stratum
  exactly on `(2,3,3,2)` where the effective `(b,q)=(2,2)`, i.e. `q=b`, codim `q−b+1 = 1`: there is a single
  `b×b` minor equal to `det`, `{minor=0}={det=0}`, and `z := det` is one coordinate — the single-minor gap
  is **absent** at `q=b`. The gap (codim `≥ 2`, single minor lossy) appears precisely at `q > b`, which is
  exactly where Cat I is non-trivial past `a<1`. So `cornrev`'s "`z:=det` is a coordinate, measure
  `|z|^{a−1}`" is the `q=b` special form; for `q > b` the top-stratum closure needs the genuinely
  `(q−b+1)`-dimensional radial model `‖z‖²`. Still elementary (Gram–Schur + polar), no blow-up — but not a
  single coordinate.

---

## CLOSE

- **Firmest.** (B). The single-minor upper bound `det^{−a/2} ≤ |minor_{S₀}|^{−a}` proves `∫det^{−a/2} < ∞`
  only for `a < 1`; the true threshold is `a < q−b+1`. Explicit in-Cat-I failure: `b=1, q=2, a=1` — true
  `= 2π`, bound `= +∞` (log). Mechanism: one minor is one polynomial, `{minor=0}` is codim-1, controls one
  transverse coordinate (`|z₁|`), not the full transverse radius (`‖z‖`). `genm-wtint`'s "single minor
  sufficient AND sharp / reduces to the `a<q−b+1` test" is wrong at the `q>b` case; its WALL (Cauchy–Binet
  load-bearing) stands. Decorrelated Codex reached (B) independently at PROVEN level.
- **Most likely to break it.** If `a` in the DLN application is always `< 1` at the operative cut (e.g. the
  charge always caps below 1 on the charts that use the whole-stratum peel), then `cbmin` would suffice in
  practice and the over-claim would be harmless. Worth a check: are there Cat I charts with `a ≥ 1` that
  route through the good-stratum peel? `genm-wtint`'s own `(2,2,1)`-type examples and the `min(a,q−b+1)`
  charge suggest `a ≥ 1` does occur — but the operative `a` per chart should be confirmed before re-scoping.
- **Next.** Spawn the Cat I formaliser on the **Gram–Schur top-stratum model** `det(Q_b Q_bᵀ) =
  det(G_{b−1})·‖z‖²` + the radial `∫_{ℝ^{q−b+1}}‖z‖^{−a}` integrability (`a < q−b+1`), Lean-friendly via
  Gram–Schmidt/QR + Mathlib's `‖·‖^{−a}` integrability near 0 — **not** on `cbmin`'s single-minor bound.
  `cbmin` is still a correct, bankable lemma (single-minor lower bound); it just does not close Cat I for
  `a ≥ 1`. Keep it, but do not name it as the Cat I weight-control step.
