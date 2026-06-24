# Resolution certificate — `(3,3,4)`: the genuinely-binding coupled `diag(b)` witness

**Seat:** `pen-and-paper` (CONSTRUCT). **Date:** 2026-06-24.
**Gate:** the R1 Lean `routeStep` — exhibit, on a branch that *genuinely binds*, that the coupled
`diag(b)` symbolic support is **necessary** (threshold-only computes the wrong RLCT). This is the
binding obstruction `(4,4,2,2)` failed to provide (there threshold-only got the right answer via the
clean binder; see `verify-r1-diagb-4422.md`).
**Method:** exact symbolic peel (sympy); the calibrated Newton-polytope LP (exact rationals); the
**published Aoyagi-Watanabe (2005) RRR closed form** as an independent value anchor; one decorrelated
`local-codex-consult` at `xhigh` (conclusion withheld).
**Artefacts:** `/tmp/c334_peel.py` (the exact peel), `/tmp/c334_ds_precise.py` (true-vs-threshold DS),
`/tmp/c334_rrr_published.py` (the published RRR cross-check), `/tmp/c334_genuine_resolve.py`.
Codex prompt/answer: `/tmp/codex_334_prompt.md`, `/tmp/codex_334_answer.md`.

---

## VERDICT: **HOLDS** — `(3,3,4)` binds at `4`, and threshold-only gets `3` (wrong)

> **`rlct_core(3,3,4) = 4`** (core `‖C¹C²‖²`, `C¹` `3×3`, `C²` `3×4`, origin), at the **binding** branch
> `t=(1,0)` (corank-`(2,2)` partial drop, `Mval=8`, the *unique* minimiser). A **threshold-only /
> per-row-multiplicity** recursion computes **`3`** — it undercounts the binding value by `1`. So the
> symbolic `diag(b)` support (which exceptional variable multiplies which generator, with sharing) is
> **necessary** here. Unlike `(4,4,2,2)`, this is a branch that *sets the RLCT*, so the error is not
> harmless.

---

## 1. The exact peel and the genuine resolution → `4`

`(3,3,4)` is an `L=2` (reduced-rank-regression) core. The branch lattice (exact):
`Mval(t₁) = (3−t₁)² + (t₁)(4−0) → 9, 8, 9, 12` for `t₁=0,1,2,3`. The **unique** minimiser is `t₁=1`,
`Mval=8`, rlct `4`. The minimiser has layer-1 corank `(3−1,3−1)=(2,2)` and is a **partial** drop
(`0<1<3`) — a genuine `2×2` residual block, **not** clean (corank-0) and **not** scalar (corank-1).
(`/tmp/diagb_genuine_coupling.py` census: `(3,3,4)` is the smallest reduced-width vector whose every
minimiser is a corank-≥2 partial drop.)

**Exact peel (`/tmp/c334_peel.py`, sympy-verified).** Block-eliminate `C¹` at rank `t₁=1`
(Lemma-2, ideal-preserving): `C¹ ∼ diag(E₁, Δ)`, `Δ` a free `2×2` residual; absorb units into `C²'`:

$$
F \;\sim\; \lVert T\rVert^2 \;+\; \lVert \Delta\,S\rVert^2,
\qquad T = \text{top }1\times4\text{ row of }C^{2\prime}\ (4\text{ free}),\quad
S = \text{bottom }2\times4\ (8\text{ free}),\quad \Delta\ \text{free }2\times2 .
$$

`T` and `(Δ,S)` are in **disjoint** variable sets (verified: `T ⊂ {B₀..B₃}`, `Δ·S ⊂ {d₀..d₃, B₄..B₁₁}`).
For disjoint-variable sum-of-squares the RLCTs add (Watanabe product rule):
`rlct(F) = rlct(‖T‖²) + rlct(‖ΔS‖²)`.

- `rlct(‖T‖²) = 2` (Morse rank-4, Newton-LP).
- `rlct(‖ΔS‖²) = 2` — the `(2,2,4)` matrix-product core. **Genuine resolution** (Codex, independently
  constructed, `/tmp/codex_334_answer.md`): radial `Δ = a·[[1,u],[v,w]]`, Jacobian `|a|³`; after unit
  transforms with the shear `e = w−vu`, `‖ΔS‖²∘π ∼ a²(‖P‖² + e²‖Q‖²)`, `P,Q` disjoint `1×4` rows. The
  inner factor `‖P‖²+e²‖Q‖²` has rlct `2 + ½ = 5/2`; the divisor `a` (Jac `|a|³`) gives `(3+1)/2 = 2`;
  so `min(2, 5/2) = 2`. (The shared shear `e` coupling the second row to the first is exactly the
  `diag(b)` content.)

`rlct_core(3,3,4) = 2 + 2 = 4 = ½·Mval(1,0) = ½·8`. [Proved — exact peel + Newton-LP + the Codex
resolution.]

**Independent value anchor (`/tmp/c334_rrr_published.py`).** The published Aoyagi-Watanabe (2005) RRR
learning coefficient for `(H,N,M)=(3,3,4)`, true rank 0, is `4`; the closed form agrees with
`½·Mval_min` on all 11 spot-checked `(H,N,M)` (incl. `(2,2,2)→3/2`, `(2,2,4)→2`, `(4,4,4)→6`,
`(5,3,4)→11/2`). So `4` does not rest on the internal IP alone — it matches the literature RRR formula.
*(MC is useless here: rlct `4` is far beyond the resolvable `ε` window, `/tmp/c334_aoyagi_rrr_explicit.py`
— consistent with the prior cert's finding that MC is a guide only and near-useless at high RLCT.)*

---

## 2. The obstruction BINDS — threshold-only computes `3`, not `4`

The threshold-only invariant (`verify-r1-light-recursion.md`) carries, per output row, only an integer
**multiplicity** (count of accumulated divisor scalars) + residual widths — **not** which divisor
variable weights which generator, nor sharing. At the `t₁=1` peel it sees: `T` clean (mult 0), the two
bottom rows "each weighted by one scalar" (mult 1 each). Lacking the weight's identity, it models the
bottom rows as weighted by **independent** scalars `δ₁,δ₂`:

$$
\lVert T\rVert^2 \;+\; \lVert \delta_1 R_1\rVert^2 \;+\; \lVert \delta_2 R_2\rVert^2,
\qquad R_1,R_2 \text{ the two }1\times4\text{ rows of }S\ (\text{disjoint}).
$$

| | shared `Δ` (true) | independent `δ₁,δ₂` (threshold-only) |
|---|---|---|
| DS-part `‖ΔS‖²` rlct | **2** (the `(2,2,4)` core) | `½ + ½ = 1` (two `⟨δ x₁..x₄⟩` blocks) |
| total `(3,3,4)` rlct | `2 + 2 = ` **4** | `2 + 1 = ` **3** |

(`/tmp/c334_ds_precise.py`, exact Newton-LP: `⟨δ x₁,…,δ x₄⟩` → `½`; two disjoint → `1`. Codex
independently: `rlct(‖δR‖²)=½`, threshold-only DS `=1`, total `3`.)

**Threshold-only undercounts the binding value by exactly `1`.** Because `t=(1,0)` is the *minimiser*,
this is not a harmless non-binding miss (as it was on `(4,4,2,2)` branch `t=(2,1,0)`) — it makes the
threshold-only recursion report `rlct(3,3,4)=3`, which is **wrong**. The symbolic shared-`Δ` support is
**necessary** at this genuinely-binding DLN branch.

**The atomic mechanism** is exactly the prior cert's `I_shared` / `I_indep` boundary, now realised at a
binder: replacing the shared `2×2` residual `Δ` by two independent row-scalars `δ₁,δ₂` changes the
Newton polytope of the DS-part from threshold `2` to threshold `1`. The shared columns of `S` seen
through the *same* `Δ` (the radial `a` + the shear `e`) is the load-bearing structure.

---

## 3. The data-structure spec, on a binding witness

The `routeStep` datum, exhibited here (refines `verify-r1-diagb-4422.md` §2 — same fields, now on a
branch that binds):

1. **Residual widths + branch profile**: at the `t₁=1` node, residual block `(M(1)−1)×(M²−1)=2×2`
   (the `Δ`-block dimensions) + the clean top `1×4` (`T`).
2. **Per-generator symbolic divisor support** (`b_i` monomials): after the radial `Δ`-blow-up, the
   divisor variable `a` multiplies **all** of the DS-part's generators; the shear coordinate `e`
   multiplies the second row's residual `‖Q‖²`. This is the support map `Gen → Finset DivVar`.
3. **Sharing / identity** (the load-bearing field): the second-row residual is `e·Q` with `e=w−vu`
   *shared from the same `Δ`-chart* as the first row `P` — this raises the inner threshold from `2`
   (if `P,Q` were independent) to `5/2`, and the radial `a` to `2`. A per-row multiplicity (mult-1 on
   each bottom row, identical) cannot encode it and collapses the DS-part to `1`.

**Drop (up to unit equivalence):** numeric coefficients; the analytic shear `e=w−vu` itself (only the
*support pattern* — that one residual generator is `a·e·Q` — survives).

---

## 4. Why `(3,3,4)` is the right witness and `(4,4,2,2)` is not

| | `(4,4,2,2)` `t=(2,1,0)` | `(3,3,4)` `t=(1,0)` |
|---|---|---|
| corank at layer-1 | `(2,2)` (genuine matrix `Δ`) | `(2,2)` (genuine matrix `Δ`) |
| binding? | **NO** (`Mval=7`; binder is clean `t=(4,2,0)`, `2`) | **YES** (`Mval=8`, unique minimiser) |
| threshold-only on the core | **right** (`2`, via the clean binder) | **wrong** (`3` ≠ `4`) |
| forces coupled `diag(b)`? | demonstrates the mechanism, but non-binding | **yes — necessary for the value** |

`(4,4,2,2)` exhibits the corank-2 `diag(b)` mechanism on a *non-binding* branch (ratio `7/2`), so a
recursion that mishandles it still lands the right RLCT `2` (a different, clean branch binds).
`(3,3,4)` is the smallest reduced-width vector where the corank-≥2 partial-drop branch is the *unique
minimiser*, so mishandling it gives the wrong answer. **`(3,3,4)` is the witness the Lean `routeStep`
test must use; `(4,4,2,2)` must not be used to assert a `7/2` value or as the binding corank-2 case.**

---

## 5. Separation of levels, scope, caveats

- **Levels kept separate.** This certificate is about the **resolution mechanism + the `routeStep`
  datum** and the **core value** `½·Mval`. The value `4` is anchored to the published RRR formula
  (literature), not just the internal IP. The `rlct = ½·codim` reading still rides on the cited
  analytic bound (unchanged).
- **Proved vs anchored vs inferred.**
  - *Proved (exact symbolic + Newton-LP):* the peel `F∼‖T‖²+‖ΔS‖²` (disjoint vars); `rlct(‖T‖²)=2`;
    the threshold-only DS-part `=1`; the `(2,2,4)` core `=2` (radial resolution).
  - *Anchored (literature):* `rlct(3,3,4)=4` matches Aoyagi-Watanabe (2005) RRR closed form (11/11
    spot-checks agree with `½·Mval_min`).
  - *Decorrelated-confirmed:* Codex (conclusion withheld) reached `true=4`, `threshold-only=3`,
    "shared-`Δ` necessary," with its own radial resolution of the `(2,2,4)` core.
  - *Used (disjoint-sum additivity):* `rlct(f(x)+g(y)) = rlct(f)+rlct(g)` for disjoint `x,y` — the
    standard Watanabe product rule; load-bearing for the `2+2=4` split. (Independently consistent with
    the literature value, so not a single point of failure.)
- **The one thing most likely to break this:** if the intended "threshold-only" invariant is *stronger*
  than the per-row multiplicity I modelled (e.g. one that records a per-row *width* of the weighting
  block, not just a count). The prior cert's invariant is the per-row multiplicity (a count), under
  which the obstruction binds as shown; if R1 instead carries a per-row *block-width*, re-test —
  though `I_shared` vs `I_indep` (the identity, not the width) is the residual obstruction even then.
- **Next construction (already flagged):** the same coupled mechanism on an `L=3` DLN core whose binder
  has both corank-≥2 *and* a shared deep factor `Cˢ` (`(3,3,4)` is `L=2`, so its DS-part has no shared
  deeper layer — the coupling is the `Δ`-internal shear `e`, not a shared `C³`). An `L=3` binder would
  exercise the *deep-factor* sharing too. Census candidates (corank-≥2 partial-drop binder, `L=3`):
  `(3,3,4,*)`-type — a worked one would round out the deep-sharing leg.
