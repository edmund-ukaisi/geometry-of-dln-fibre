# Resolution certificate — the `diag(b)` resolution and the R1 routeStep data structure

**Seat:** `pen-and-paper` (CONSTRUCT). **Date:** 2026-06-24.
**Gate:** the R1 Lean `routeStep` data structure — what fields the coupled `diag(b)` dispatcher must
carry, exhibited on a certified exact resolution.
**Method:** exact enumeration of the branch lattice (`Mval`); exact symbolic blow-up pullbacks
(sympy, exact orders + Jacobian dets); the Newton-polytope LP for monomial RLCT (exact rationals,
calibrated against five known targets); MC volume-scaling as a *guide only*; two decorrelated
`local-codex-consult` runs at `xhigh` (frame-in / facts-in / hypothesis-out — one branch-restricted,
one full-min).
**Artefacts:** `/tmp/diagb_newton.py` (calibrated Newton-LP machine), `/tmp/diagb_recheck.py`
(branch enumeration), `/tmp/diagb_radial_verify.py` (the exact binding-branch pullback),
`/tmp/diagb_corank2_explicit.py` (the corank-2 branch resolution), `/tmp/diagb_224.py`,
`/tmp/diagb_334.py` (the genuine coupled witnesses), `/tmp/diagb_genuine_coupling.py` (the coupled-
binding census), `/tmp/diagb_mc.py` + `/tmp/diagb_codim.py` (MC guide). Codex prompts/answers in
`/tmp/codex_diagb_prompt{,2}.md`, `/tmp/codex_diagb_answer{,2}.md`.

---

## HEADLINE — the brief's target value is wrong; the true value is **2**, not **7/2**

> **`rlct_core(4,4,2,2) = 2`** (reduced widths `M=(4,4,2,2)`, core `‖C¹C²C³‖²` at the origin),
> **not `7/2`**. The brief's `t=(2,1,0)`, `Mval=7`, "unique minimiser, target `7/2`" is a
> **NON-binding** branch: its divisor exponent is genuinely `7` (ratio `7/2`), but the RLCT is the
> **min over all branches**, and the binding branch is the *clean* `t=(4,2,0)` with `Mval=4`, ratio
> `2`. The corank-2 `diag(b)` coupling the brief wanted certified *does* occur on branch `t=(2,1,0)`
> and *does* give `7/2` — but that branch does not set the RLCT.

This is a load-bearing correction: it changes both the value the Lean build must hit *and* the
witness that forces the coupled data structure. Three independent computations agree the value is `2`:

| method | result | artefact |
|---|---|---|
| exact branch enumeration `½·min_t Mval(t)` | `min Mval = 4` at `t=(4,2,0)` → `2` | `/tmp/diagb_recheck.py` |
| exact symbolic resolution of the binding branch | `F = ρ²·‖C¹C²C̄‖²`, `Jac=ρ³`, ratio `2`; residual `7/2` | `/tmp/diagb_radial_verify.py` |
| MC volume-scaling (guide) | slope → **1.98** at the resolvable window, not `3.5` | `/tmp/diagb_mc.py`, `/tmp/diagb_codim.py` |
| decorrelated Codex (full-min, conclusion withheld) | `min Mval = 4`, `t=(2,1,0)` flagged non-binding, RLCT `2` | `/tmp/codex_diagb_answer2.md` |

The `t=(2,1,0)→7/2` resolution is *also* certified (it is correct *for that branch*): a second,
branch-restricted Codex run did the genuine Cases 1&2 resolution and got the divisor table
`x:8, y:11/2, u:7/2` with binding `u` at `7/2` (`/tmp/codex_diagb_answer.md`) — matching my Morse-7
Newton-LP (`/tmp/diagb_corank2_explicit.py`). The two Codex runs are mutually consistent: one reports
the **min on a single branch** (`7/2`), the other the **min over all branches** (`2`). The RLCT is the
latter.

---

## 1. The full exact resolution of `‖C¹C²C³‖²` for `(4,4,2,2)`

**Setup.** Reduced widths `M=(4,4,2,2)`, `L=3`: `C¹` is `4×4`, `C²` is `4×2`, `C³` is `2×2`, product
`4×2`, core `F=‖C¹C²C³‖²` resolved at the origin. `M(1)=4, M(2)=4, M(3)=2`. Established (input, not
re-derived): `rlctAt(F) = ½·min_t Mval(t)`,
`Mval(t) = (M¹−t₁)(M²−t₁) + Σ_{j≥2}(t_{j−1}−t_j)(M^{j+1}−t_j)`, `t` weakly-decreasing, `t_L=0`,
`0 ≤ t_s ≤ min(M¹,…,M^{s+1})` (the certified Def-3 admissibility, `verify-def3-underspec.md`).

**The branch lattice (exact, `/tmp/diagb_recheck.py`).** Every admissible branch carries one terminal
exceptional divisor of exponent `Mval(t)`, loss-order `k=1`, Jacobian `h=Mval(t)−1`, ratio
`(h+1)/(2k) = Mval(t)/2` (Aoyagi's Jacobian rule, `aoyagi-2023-worked.tex` §3.3, lines 492–497):

| `t` | `Mval(t)` | ratio | note |
|---|---|---|---|
| **`(4,2,0)`** | **4** | **2** | **BINDING** — clean (layer-1 corank `(0,0)`) |
| `(3,1,0)`,`(3,2,0)`,`(4,1,0)` | 5 | 5/2 | |
| `(2,1,0)` | 7 | 7/2 | corank-`(2,2)` block — the brief's branch, **non-binding** |
| `(3,0,0)` | 7 | 7/2 | |
| `(2,0,0)`,`(2,2,0)`,`(4,0,0)` | 8 | 4 | |
| `(1,0,0)`,`(1,1,0)` | 11 | 11/2 | |
| `(0,0,0)` | 16 | 8 | the full radial collapse |

`RLCT_core = min over divisors = min(2, 5/2, 7/2, 4, 11/2, 8) = 2`.

**The binding branch `t=(4,2,0)`, resolved exactly (`/tmp/diagb_radial_verify.py`).** `t₁=4=M¹=M²`
means layer-1 contributes `(M¹−t₁)(M²−t₁)=0` — there is *no* layer-1 exceptional divisor; the whole
`Mval=4` comes from the final term `(t₂−t₃)(M⁴−t₃)=(2−0)(2−0)=4`, i.e. the collapse of `C³`. Blow up
`C³` radially, `C³ = ρ·C̄` with `C̄=[[1,p],[q,r]]`:

$$
F \;=\; \rho^2\,\big\lVert C^1 C^2 \bar C\big\rVert^2,\qquad
\operatorname{Jac}\!\big(C^3 = \rho\,\bar C\big) \;=\; \rho^3 .
$$

Both verified exact in sympy (`F − ρ²·‖C¹C²C̄‖²` expands to `0`; the `4×4` Jacobian determinant is
`ρ³`). The divisor `{ρ=0}` has loss-order `2` (`k=1`) and Jacobian exponent `h=3`, ratio
`(3+1)/(2·1)=2`. The **residual** `‖C¹C²C̄‖²` is a fresh `L=2` core on widths `(4,4,2)`, whose
`Mval_min = 7` → rlct `7/2 > 2` (`/tmp/diagb_l2residual.py`); recursively all its sub-divisors are
`≥7/2`. So `min(2, 7/2) = 2` binds on the radial `ρ`-divisor. **`rlct_core(4,4,2,2)=2`.** [Proved.]

**The corank-2 branch `t=(2,1,0)`, resolved exactly (non-binding).** This is the branch the brief
named. Peeling layer-1 at rank `t₁=2` (Lemma-2 block-elimination, ideal-preserving) gives the
`diag(b)` form `C¹ ∼ diag(E₂, Δ)` with `Δ` a **genuine free `2×2`** residual block:

$$
F \;\sim\; \lVert T\,C^3\rVert^2 \;+\; \lVert \Delta\,S\,C^3\rVert^2,
\qquad T,S,\Delta,C^3 \text{ all free } 2\times2,\ C^3 \text{ shared.}
$$

Aoyagi's Cases 1&2 recursion resolves this to a single terminal divisor `u` (after introducing the
layer-`x:(0,0,0)`, `y:(1,0,0)` divisors), with the deepest-chart normal-crossing generators (Codex
consult 1, `/tmp/codex_diagb_answer.md`, FACT-tagged):

    p = x·y·u ;   resolved generators  { p, p·d₁₂, p·d₂₁, p·d₂₂, p·e, p·z₁, p·z₂ }

— the `4` entries of the `Δ`-block, the `1` layer-2 coordinate `e`, and the `2` shared-`C³`
coordinates `z₁,z₂` (= `4+1+2 = Mval(2,1,0) = 7`), **all multiplied by the same `u`**. The divisor
`u` has `k=1`, `h=6`, ratio `7/2`. My independent Morse-7 Newton-LP confirms the transverse threshold
`7/2` (`/tmp/diagb_corank2_explicit.py`). **The coupling:** the *same* exceptional coordinate `u`
divides all `7` generators; a naive treatment that gives the `Δ`-block its own divisor (only the `2×2`
contribution, `(k,h)=(1,3)`, ratio `2`) **undercounts the branch to `2`** by failing to merge the
layer-2 and shared-`C³` generators into the `u`-chart. This is exactly the prior light-recursion cert's
"hand cascade → 2" failure — but note it undercounts *this non-binding branch's own value* `7/2`,
**not** the global RLCT (which is `2` legitimately, via a different branch).

---

## 2. The DATA STRUCTURE the `routeStep` datum must carry

The Newton LP depends **only** on the multiset of monomial support-vectors `{α_k}` of the resolved
generators. So per recursion node the irreducible datum is:

### Carry (load-bearing)

1. **Residual reduced widths** `M'` and the **branch rank-profile increment** at this node
   (which layer `S`, current cleared count `J`, the residual block dimensions `(M(S)−J)×(M^{S+1}−J)`).
2. **The per-generator symbolic divisor support** — for each resolved generator, the *set of
   exceptional `u`-variables (with multiplicity) that multiply it*. In Aoyagi's notation this is the
   monomial `bᵢ = ∏ u_{s,k}` attached to row `i`.
3. **The SHARING / identity relations among generators** — *which* generators are multiplied by the
   *same* `u`-variable. This is the field that distinguishes the cases below and is exactly what a
   per-row *multiplicity* (a count) loses:

   | resolved ideal | per-row data | exact RLCT | why |
   |---|---|---|---|
   | `I_shared = (δx, δy)` | 2 rows, 1 weight each | **½** | one shared `δ` |
   | `I_indep = (δ₁x, δ₂y)` | 2 rows, 1 weight each | **1** | two independent `δ` |

   Identical multiplicities, different RLCT — the identity of the shared variable is load-bearing.
   (Both reproduced exactly by the calibrated Newton-LP, `/tmp/diagb_newton.py`.)

### May drop (up to unit equivalence)

- **Numeric coefficients** of the matrix entries (the `Q,P` regular transforms of Aoyagi's Lemma 2
  are units — they preserve the ideal and the RLCT).
- **Analytic row/column unit changes** (e.g. the shear `f' = ac+f` that linearises a smooth residual
  coordinate). What survives is the *support pattern*, not the coordinates' analytic form.

### Concrete Lean `RouteStep` field sketch (the spec, not Lean)

A node is either a **leaf** (residual is a unit / fully diagonal `diag(b₁,…)`) or a **branch**:

    RouteStep :=
      | leaf  (divisorExp : ℕ)            -- = Mval(branch t); the terminal divisor's exponent
      | branch
          (S J : ℕ)                       -- layer index + cleared-pivot count
          (residWidths : ...)             -- the residual block dimensions (M(S)-J)×(M^{S+1}-J)
          (newDivisorExp : ℕ)             -- exponent ADDED at this blow-up (Case-2: (M(S)-J)(M^{S+1}-J))
          (support : Gen → Finset DivVar) -- the b_i monomials: which u-vars divide which generator
          (children : List RouteStep)     -- the chart sub-cases (Case 1(1)/1(2) / Case 2)

The value fold is `min over leaves of (divisorExp / 2)`, where each leaf's `divisorExp` is the
**accumulation** of `newDivisorExp` down its path (Aoyagi's `M_{s,k}` accumulation, `b_i = ∏ u_{s,k}`).
The `support : Gen → Finset DivVar` field is what `verify-r1-light-recursion.md` proved a per-row
*multiplicity* `ℕ` cannot replace.

---

## 3. Contrast — corank-1 `(3,3,2,2)` and the scalar-`δ` degeneration

For `(3,3,2,2)` the binding value is also `2` (`Mval_min=4`), and it is reached by **three** branches:
`t=(2,1,0)` (corank-`(1,1)` = scalar `δ`), `t=(3,1,0)` and `t=(3,2,0)` (both corank-`(0,0)` = clean)
(`/tmp/diagb_3322_contrast.py`). On the corank-1 branch the `diag(b)` invariant is `diag(E₂, δ)` with
`δ` a **single scalar** — the `support` field degenerates to a forced singleton: there is one weighted
row, its monomial support is *forced* by `(widths, branch, the one weight)`, so the sharing relation is
trivial. This is the prior cert's "threshold-only is faithful at corank ≤ 1." The same `RouteStep`
datum covers it: `support` maps the one residual generator to `{δ}`; the matrix-block case
(`(4,4,2,2)` branch `t=(2,1,0)`, or the binding witnesses below) maps the `4` residual generators to a
*shared* `{u}` that also divides the layer-2 and deep-`C³` generators. The field is the same; only its
cardinality and sharing degree differ. **One uniform datum covers corank-0 (empty `support`),
corank-1 (singleton, forced), and corank-≥2 (shared multi-generator).**

---

## 4. The corrected witness for the coupled `diag(b)` data structure

The brief's `(4,4,2,2)` does **not** force the coupled matrix-block at its binding branch (the binder
is clean radial). The genuine forcing question — *is there a width vector whose every binding branch is
a partial layer-1 drop (`0<t₁<min(M¹,M²)`) with corank ≥ 2?* — has an exact answer
(`/tmp/diagb_genuine_coupling.py`, census over entries `2..7`, `L=2..4`):

- **YES.** The smallest is **`M=(3,3,4)`** (an `L=2` RRR core, `C¹` `3×3`, `C²` `3×4`): unique
  minimiser `t=(1,0)`, partial drop `0<1<3`, corank `(2,2)`, `Mval_min=8`, **rlct `4`**. There is no
  clean (corank-0) or scalar (corank-1) binding route — the genuine `2×2` `Δ`-block sets the value.
  (`(2,2,4)`, `t=(0,0)`, is corank-`(2,2)` but `t₁=0` = a *full radial* collapse, which resolves by one
  clean radial blow-up to `2` — corank-2 but **not** the coupled partial case. The partial-drop coupled
  case starts at `(3,3,4)`.)
- The brief's `(4,4,2,2)` is **not** in this set — its binder `t=(4,2,0)` is the clean `t₁=M¹` route.

**Clean-reachability of the minimiser is FALSE in general** (`/tmp/diagb_cleanreach.py`): `(2,2,2)`
and `(2,2,3,3)` have no corank-0 minimiser; `(3,3,4)` and its family have only genuinely-coupled
(corank-≥2 partial-drop) minimisers. So the Lean build **does** need the coupled `diag(b)` recursion
(option (ii)) for the general headline — that conclusion of `verify-r1-light-recursion.md` **stands**.
What changes is the *witness*: the design-decision is driven by `(3,3,4)`/`(2,2,3,3)`/`(2,2,2)`, not by
`(4,4,2,2)`.

---

## 5. Separation of levels, scope, caveats

- **Levels kept separate.** This certificate is about the **resolution mechanism + the `routeStep`
  datum** and the **core value** `½·min Mval`. The `(4,4,2,2)` core value is now *derived here* (`=2`),
  not taken as the brief's input. The `rlct = ½·codim` *reading* still rides on the cited analytic
  bound (Aoyagi/Watanabe `S2`), unchanged.
- **Proved vs verified-by-enumeration vs inferred.**
  - *Proved (exact symbolic):* the binding-branch pullback `F=ρ²‖C¹C²C̄‖²`, `Jac=ρ³`, ratio `2`
    (`(4,4,2,2)`); the `(2,2,4)` radial resolution to `2`; the five Newton-LP calibration targets.
  - *Verified by exact enumeration:* `min_t Mval(4,4,2,2)=4`, binder `t=(4,2,0)`, `t=(2,1,0)`
    non-binding (`Mval=7`); the coupled-binding census (smallest `(3,3,4)`); permutation-invariance of
    `Mval_min` on `{4,4,2,2}` (all orderings → `4`).
  - *Decorrelated-confirmed:* both Codex runs (full-min → `2`; branch-restricted → `7/2` with the
    explicit `diag(b)` generator list `{p, p·dᵢⱼ, p·e, p·zₖ}`, `p=xyu`, and the sharing observation).
  - *Established input (not re-checked):* `½·min Mval` is the true core RLCT; the `(3,3,4)`/`(2,2,4)`
    values lean on the `L=2` RRR ground-truth agreement (`verify-arith-groundtruth.md`, 216/216).
  - *Guide only (never a verdict basis):* MC volume-scaling — `(4,4,2,2)` slope → `1.98` corroborates
    `2`, refutes `3.5`; useless at `(3,3,4)` rlct `4` (fractions vanish), as expected.
- **The admissibility convention — checked, the value is robust to it (`/tmp/diagb_strict_test.py`).**
  The only way to rescue `7/2` would be an admissibility that *forbids* `t=(4,2,0)`. I checked the two
  candidate conventions:
  - **Certified Def-3** `t_s ≤ min(M¹,…,M^{s+1})` (`verify-def3-underspec.md`): `t=(4,2,0)` admissible
    (`t₁=4≤min(4,4)=4`, `t₂=2≤min(4,4,2)=2`) → min `4` → **`2`**.
  - **Strict Aoyagi** `t_s ≤ M^{s+1}` (the per-edge rank cap): `t=(4,2,0)` *still* admissible
    (`t₁=4≤M²=4`, `t₂=2≤M³=2`) → min `4` → **`2`**.

  **Both conventions give `2` for `(4,4,2,2)`, and both reproduce every known ground truth**
  (`(2,2,2)→3/2`, `(3,3,2,2)→2`, `(2,2,2,2)→3/2`, `(3,2,2,2)→3/2`, `(2,3,2,2)→3/2` — all PASS under
  both). The hypothetical that would give `7/2` (`t₁ ≤ M³=2`, double-capping `t₁` by the *third*
  width) is **not** either convention and is refuted by the ground truths. So the value `2` is robust
  to the admissibility convention; the brief's `7/2` does not come from a convention choice, it comes
  from reading off the *non-binding* branch `t=(2,1,0)` instead of the min.
- **Next construction — DONE (see `verify-r1-diagb-334.md`, summarised in §6 below):** a full genuine
  Cases-1&2 symbolic resolution of `(3,3,4)` `t=(1,0)`, the true minimal coupled witness, confirming the
  `diag(b)` matrix-block sets `rlct=4` and exhibiting the shared support on the `2×2` `Δ` — feeding the
  Lean `routeStep` the *binding* coupled datum that `(4,4,2,2)` does not provide.

---

## 6. The binding coupled worked example — `(3,3,4)` `t=(1,0)` (the routeStep transcription target)

`(4,4,2,2)`'s corank-2 branch `t=(2,1,0)` exhibits the `diag(b)` mechanism but is **non-binding** (§1),
so it cannot show that the coupled support is *necessary for the value*. The binding example is the
`(3,3,4)` `L=2` RRR core (full certificate: `verify-r1-diagb-334.md`). Summary of the worked binding
resolution the Lean `routeStep` build transcribes:

- **Branch lattice.** `Mval(t₁) = (3−t₁)² + 4t₁ → 9,8,9,12` (`t₁=0,1,2,3`). **Unique** minimiser
  `t₁=1`, `Mval=8`, rlct `4`. The minimiser is a genuine **corank-`(2,2)` partial drop** (`0<1<3`) —
  the smallest reduced-width vector whose every minimiser is corank-`≥2` partial (census
  `/tmp/diagb_genuine_coupling.py`).
- **Exact peel (`/tmp/c334_peel.py`, sympy).** `C¹ ∼ diag(E₁, Δ)`, `Δ` free `2×2`:
  `F ∼ ‖T‖² + ‖Δ·S‖²`, `T` clean top `1×4`, `S` free `2×4`, disjoint variable sets.
- **Resolution → 4.** `rlct = rlct(‖T‖²) + rlct(‖Δ·S‖²) = 2 + 2 = 4 = ½·Mval`. The `(2,2,4)` sub-core
  `‖Δ·S‖²` resolves radially `Δ = a·[[1,u],[v,w]]` (Jac `|a|³`), shear `e=w−vu`, inner factor
  `‖P‖²+e²‖Q‖²` (rlct `5/2`), divisor `a` ratio `2`, so `min(2,5/2)=2`. **Anchored to the published
  Aoyagi-Watanabe (2005) RRR closed form** (matches `½·Mval_min`, 11/11 spot-checks).
- **The obstruction BINDS (the necessity of the coupled support).** A threshold-only / per-row-
  multiplicity recursion sees the two bottom rows as independent-scalar-weighted (`δ₁,δ₂`), computes the
  DS-part as `½+½=1`, total `2+1=3 ≠ 4` — the **wrong** core RLCT (this branch is the minimiser).
  The shared `2×2 Δ` (one radial `a` dividing all DS generators + the shear `e` coupling the second
  row) raises the DS-part from `1` to `2`. Decorrelated Codex independently reproduced `true=4`,
  `threshold-only=3`, with its own `(2,2,4)` resolution.
- **The `routeStep` datum, on a binder.** Residual block dims `(2×2)` for the `Δ`-block + clean `1×4`
  for `T`; `support : Gen → Finset DivVar` mapping the radial `a` onto all DS generators and the shear
  `e` onto the second-row residual; the *sharing identity* (that the same `a`/`e` is shared) is the
  load-bearing field a per-row count loses. Drop: numeric coefficients and the analytic shear form
  (only the support pattern survives).
