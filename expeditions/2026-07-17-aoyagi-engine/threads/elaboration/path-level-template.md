---
title: "Aoyagi's resolution — the path-level template (chart map, cover, read-off, value)"
status: draft
source: original
topics: [aoyagi, resolution, cover, jacobian, rlct, value-assembly, template, formalisation-spec]
created: "2026-07-22T11:00:00"
updated: "2026-07-22T11:00:00"
---

# Aoyagi's resolution — the path-level template

Companion to [`fold-recursion-template.md`](fold-recursion-template.md) (the per-step fold recursion,
pp.14–22). This document elaborates the **path-level** content — the composition of the per-step charts
along a root-to-leaf path, the cover argument, the terminal exponent read-off, and the assembly into
the learning-coefficient value `λ = C/2` (pp.6, 13, 22–26). It is the pre-mortem for the next-wave
leaves (composed chart map, coverage, read-off, value seam) **before** their proofs start.

Same discipline as the fold template: blind to the Lean, exact algebra (`sympy`, scripts in
`verify/`), worked on both standing instances `d=(3,3,4)` and `d=(3,3,2,2)`, one decorrelated Codex
consult on the hardest reading (the cover), open readings flagged **Question** not silently resolved.
All index conventions are those declared in `fold-recursion-template.md §0` (1-indexed; `M(S)` running
min caps the row axis; state `(S,J)`; exceptional `u_{s,k}` with profile `T_{s,k}`, exponent `M_{s,k}`,
`t̃_{s,k} = min_S t^{(S)}_{s,k}`).

The story is short: 1. a root-to-leaf path composes into one analytic chart `g` fixing the origin,
a.e.-injective, with a **pure-monomial** Jacobian `∏ u_{s,k}^{M_{s,k}−1}` (the det-1 shears contribute
nothing); 2. the charts of all paths **cover** a neighbourhood a.e. (excluding the measure-zero
exceptional loci); 3. at a terminal the loss is `b_1²·(unit)` with `b_1` squarefree, so each binding
axis contributes ratio `M_{s,k}/2` and `λ_core = ½·min`; 4. Theorem 3 adds the regular Morse block, and
`λ = prefactor + ½·cCodim = C/2`, the min entering as `min_t Mval(t) = minAdm = cCodim`.

---

## 1. The composed chart map along a root-to-leaf path

### 1.1 The composite `g` and its properties

A root-to-leaf path of the blow-up tree (§1.4 of the fold template — a sequence of Edge A/B/C clears,
punctuated by Edge D rollovers, ending at `S = L+1`) composes into a single map

$$
g = g_1 \circ g_2 \circ \dots \circ g_N : \ U \longrightarrow V,
$$

where each `g_m` is either a **blow-up chart substitution** (a monomial map in the pivot chart:
`x_pivot = u`, `x_other = u·x'_other`) or a **shear** (the `Q` right-multiplication and the
`b'`-conjugated `P` left-multiplication of the fold template §2, plus the `Q^{-1}` recoordinatization of
the next layer). Its properties, all inherited step-by-step:

- **Analytic**: each `g_m` is polynomial (blow-up chart) or a unipotent linear change with monomial
  entries (shear); the composite is analytic on the chart domain.
- **Origin-fixing**: `g(0) = 0`. Each blow-up chart fixes the origin (`x = 0 ⟹ u = 0`), each shear is
  linear hence fixes `0`.
- **a.e.-injective / proper**: `g` is a composition of proper blow-up charts and linear isomorphisms;
  it is a biregular isomorphism away from the union of blow-up centres (a lower-dimensional, hence
  measure-zero, analytic set — the exceptional locus). See §2 for the precise a.e. statement.

!!! note "The shear is where cross-layer coupling lives (from the fold template §2.2)"
    The `Q^{-1}` recoordinatization writes **only the pivot row of the immediately-next layer**
    `C^{(S+1)}`; deeper layers `C^{(S+2)}, …, C^{(L)}` are untouched. So along the path, layer `s`'s
    residual couples only into layer `s+1`. This is the "one factor per layer" structure of a cross-
    layer residual.

### 1.2 The ledger Jacobian (the determinant bookkeeping)

The paper's p.15 display is the Jacobian ledger. At state `(S, J)` along the path:

$$
\prod_{s=1}^{L}\prod_{i=1}^{M^{(s)}}\prod_{j=1}^{M^{(s+1)}} \mathrm{d}c^{(s)}_{ij}
= \Big(\prod_{s=1}^{S-1}\prod_{k=1}^{M^{(s+1)}} u_{s,k}^{\,M_{s,k}-1}\,\mathrm{d}u_{s,k}\Big)
  \Big(\prod_{k=1}^{J} u_{S,k}^{\,M_{S,k}-1}\,\mathrm{d}u_{S,k}\Big)
  \Big(\prod_{i=J+1}^{M(S)}\prod_{j=J+1}^{M^{(S+1)}} \mathrm{d}d_{ij}\Big)
  \Big(\prod_{s=S+1}^{L}\prod_{i,j} \mathrm{d}c^{(s)}_{ij}\Big).
$$

- **Each exceptional divisor `u_{s,k}` contributes `u_{s,k}^{M_{s,k}−1}`** to `|g'|` — i.e. its
  Jacobian power is exactly `h_{s,k} = M_{s,k} − 1`, where `M_{s,k}` is the **final accumulated**
  exponent. The residual coordinates `d_{ij}` and the untouched deeper layers keep their flat
  differentials (Jacobian factor `1`).
- **Product formula / accumulation (verified exact, `verify/path_verify.py`)**: the power and the
  exponent grow together, step by step. A codim-`c` blow-up chart contributes `u^{c-1}` to the pivot's
  Jacobian (standard blow-up chart determinant, checked for `c = 2,3,4,6`). A **Case-2 birth** has
  `c = (M(S)−J)(M^{(S+1)}−J) = M_{s,k}`, giving `u^{M_{s,k}-1}`. A **Case-1 boost** blows up a centre of
  codim `J_1·(M^{(S+1)}−J) + 1`, adding `J_1·(M^{(S+1)}−J)` to the pivot's Jacobian power — **exactly**
  the amount the exponent `M_{s,k}` grows by (fold template Edge B/C). Hence

$$
\text{Jacobian power of } u_{s,k} \ =\ M_{s,k} - 1 \quad \text{at every state, birth and after every boost.}
$$

- **Why the unit is `≡ 1` (det-1 shears ∘ monomial blow-ups)**: the only non-blow-up maps are the
  shears `Q, P` (and `Q^{-1}` on the next layer), all **unipotent, det exactly `1`** (fold template §2,
  `verify/step_verify.py`). So they contribute **no** factor to `|g'|`. The composite Jacobian is
  therefore a **pure monomial** `∏_{s,k} u_{s,k}^{M_{s,k}-1}` — there is **no leftover analytic unit** in
  `|g'|`. (This is `|g'|`; the *prior* `φ(g(u))` is a separate positive unit with `φ(0) > 0`, absorbed
  into the leading behaviour — it never affects the threshold.)

### 1.3 The squarefree-`b_1` claim

In a terminal chart the loss pulls back (as an ideal, via Lemma 1) to `b_1² + ⋯ + b_{M(L+1)}²`.

- `b_1 = ∏_{t̃_{s,k}=0} u_{s,k}` is a product of **distinct** exceptional coordinates, each to the
  **first power** — a **squarefree** monomial. (Automatic: each `u_{s,k}` is a distinct coordinate; no
  coordinate repeats in `b_1`.) Consequently the loss vanishes to order **exactly 2** along each binding
  axis `{u_{s,k} = 0}`: `K(g(u)) = b_1²·(unit) = ∏_{t̃=0} u_{s,k}^{2}·(unit)`, i.e. `2k_{s,k} = 2`,
  `k_{s,k} = 1` for each binding axis. This `k = 1` is what makes the read-off ratio `(h+1)/(2k) =
  M_{s,k}/2` (§3).

!!! danger "PM-P1 — `|g'|` unit is `≡ 1`; the loss unit is a *function* `= 1` at the origin"
    Two different "units" appear and must not be conflated. `|g'| = ∏ u^{M-1}` is a **pure monomial** —
    its unit factor is **identically `1`** (det-1 shears). The loss `K(g(u)) = b_1²·U(u)` has
    `U` a **unit-valued analytic function** with `U(0) = 1` but `U ≢ 1` (it is `1 + Σ (b_i/b_1)²`). A
    formalisation that claims the loss factor is `≡ 1`, or that the Jacobian carries a non-trivial
    function unit, is wrong in opposite directions. Assert: `|g'|` monomial (unit `≡ 1`); loss `= b_1²·U`,
    `U(0) = 1`, `U` continuous, `U ≢ 1` in general.

---

## 2. The cover argument

### 2.1 What the charts cover, and what "a.e." excludes (Codex-confirmed, high)

The terminal pivot charts, over **all** root-to-leaf paths of the blow-up tree, form an **open cover of
the blown-up manifold `Q`**: each blow-up of a codim-`c` centre has `c` standard charts covering its
projective exceptional directions, and inductively the leaves cover `Q`. The resolution map `g` is
**proper**, so `g(Q) = V` (a neighbourhood of the singular point). `g` is a **biregular isomorphism off
the exceptional locus** `E ⊂ Q` (the union of blow-up centres' preimages), and `E` and its image are
**lower-dimensional analytic sets — measure zero**.

- **"a.e." excludes exactly `E`** (equivalently, the blow-up centres downstairs). Away from `E`, `g` is
  one-to-one and the change of variables is valid; on `E` (measure zero) it may be ignored in the
  integral.

### 2.2 The integral identity (the correction — NOT a naive chart sum)

!!! warning "PM-P2 — `∫_V ≠ Σ_charts ∫_chart` (open charts overlap)"
    The open pivot charts **overlap**, so the unweighted chart sum overcounts. The correct identity
    (standard resolution / Watanabe–Aoyagi lineage) integrates over `Q` with a **partition of unity**
    `{ρ_U}`:

        ∫_V |F|^{-c} φ dw  =  ∫_Q |F∘g|^{-c} φ(g) |g'| du  =  Σ_U ∫_U |F∘g|^{-c} φ(g) |g'| ρ_U du.

    Equivalently one may restrict each pivot chart to its **largest-coordinate sector**
    `{ |x_pivot| ≥ |x_other| }` with ties assigned measurably; the sector boundaries are null and the
    pieces are **a.e. disjoint** — then the sum is honest. Both are valid; the boxed-rule lineage uses
    the proper-map / open-atlas + partition-of-unity form (integrate over `Q`, not an unweighted chart
    sum). A formalisation must pick one and **not** assert `∫_V = Σ_U ∫_U` bare.

### 2.3 Min-over-charts for `λ`, max for `θ`

On a relevant chart, with `k_j > 0` on the binding axes,

$$
|F(g(u))|^{-c}\,|g'(u)|\,\varphi(g(u)) \ =\ a(u)\,\textstyle\prod_j |u_j|^{\,h_j - 2 c k_j}, \qquad a>0 \text{ bounded},
$$

which is integrable near the point **iff** `h_j − 2 c k_j > −1` for every `j` with `k_j > 0`, i.e.
`c < (h_j+1)/(2k_j)`. Aggregating:

- **`λ = min_U min_j (h_j+1)/(2k_j)`** (the boxed rule, p.6): the global integral converges iff `c` is
  below **every** chart's threshold, so the global threshold is the **minimum**. One divergent local
  piece forces global divergence; all-convergent gives global convergence by a finite localization.
- **`θ = max_u Card{ j : (h_j+1)/(2k_j) = λ }`** — the pole order is a **maximum** over points/charts of
  the count of binding axes, **not a sum**: adding localized zeta integrals preserves the largest pole
  order, and positivity (`a > 0`) prevents cancellation.

!!! danger "PM-P3 — exclude `k_j = 0`; and the p.6 'non-positive integers' is a sign typo"
    The boxed min is over `j` with **`k_j > 0`** only (axes the loss actually vanishes along); an axis
    with `k_j = 0` has ratio `+∞` and must be excluded, else the min is spuriously `0`. Separately, p.6
    prints "`k_1, …, k_d, h_1, …, h_d` are **non-positive** integers"; with `h_j = M_{s,k} − 1 ≥ 0` and
    `k_j ≥ 1` this must read **non-negative** — a sign typo. Assert: `k_j ≥ 1` on binding axes,
    `h_j ≥ 0`; the min ranges over `k_j > 0`.

### 2.4 What the paper proves vs asserts (the named hard part)

- **Cited as standard** (p.6, via Hironaka): the existence of the proper resolution `g`, the monomial
  change-of-variables identity, and the boxed min/max rule. The cover, the partition-of-unity
  localization, and the pole-order aggregation are **not proved** — they are standard resolution theory.
- **Proved locally** (pp.14–22): the recursive algebra — centres, representative pivot charts, the
  monomial/Jacobian bookkeeping, the terminal ideal, the candidate ratios.
- **NOT established** (the gap): that the representative Case 1/Case 2 pivot calculations generate
  **every** necessary pivot chart, that **every branch terminates**, and that the terminal domains form
  a **proper covering atlas**. A displayed `d_{J+1,J+1}`-pivot normalization implicitly stands for all
  symmetric matrix-entry pivots, but the relabelling and coverage argument is not written.

!!! danger "PM-P4 — the SHARPEST GAP: the exhaustive terminal-chart atlas"
    Constructing and proving **coverage + termination** of the exhaustive terminal-chart atlas from the
    representative recursive pivot cases is the single step most likely to need reconstruction (not
    citation). This is exactly worked.tex's named hard part **C** and the sorried Lean leaves
    `rlctAt_sumSqFam_eq_iInf_charts` (the min-over-charts CoV) + `exists_coreResolution` (that this
    recursion inhabits the certified atlas record). A formalisation must **build** this, not cite it.

---

## 3. The exponent read-off at a terminal

### 3.1 `bindingAxes ↔ t̃ = 0` divisors; the `jac + 1 = divExp` seam

At a terminal chart:

- The **binding axes** are the exceptional coordinates dividing the dominant monomial `b_1`, i.e. the
  `u_{s,k}` with **`t̃_{s,k} = 0`** (fold template §4). These are the only candidates in that chart.
- For each binding axis: `k_{s,k} = 1` (squarefree `b_1`, §1.3) and the Jacobian power
  `h_{s,k} = M_{s,k} − 1` (§1.2). Hence the **seam clause**

$$
\text{jac} + 1 \;=\; (M_{s,k}-1) + 1 \;=\; M_{s,k} \;=\; \text{divExp}, \qquad
\text{ratio} \;=\; \frac{h_{s,k}+1}{2 k_{s,k}} \;=\; \frac{M_{s,k}}{2}.
$$

- **Per-chart read-off**: `λ_chart = min{ M_{s,k}/2 : t̃_{s,k} = 0 in this chart }`. **Global**:
  `λ_core = min over charts = ½·min{ M_{s,k} : t̃_{s,k} = 0 } = ½·min_t Mval(t)`.

Verified (`verify/path_verify.py`): the ledger `jac = M − 1` holds for **every** realized divisor
across **every** leaf, for `(3,3,4)`, `(3,3,2,2)`, `(2,2,2)`, `(2,2,2,2)`; and `min` over leaves of
`M_{s,k}/2` equals `minAdm/2` for all four.

### 3.2 The input shape the terminal principal-invariance step consumes

The terminal collapse (fold template §4.3) consumes exactly:

- a family `{b_1, …, b_{M(L+1)}}` of `u`-monomials with the **divisibility chain** `b_1 | b_2 | ⋯ | b_{M(L+1)}`;
- from which principality: `⟨b_1, …, b_{M(L+1)}⟩ = ⟨b_1⟩`, and

$$
b_1^2 + \dots + b_{M(L+1)}^2 = b_1^2 \cdot \underbrace{\Big(1 + \textstyle\sum_{i\ge2}(b_i/b_1)^2\Big)}_{U,\ U(0)=1};
$$

- the dominant `b_1` **squarefree** (`k = 1`), and each of its factors' Jacobian power `h = M_{s,k} − 1`.

The step outputs `λ_chart = ½·min{ M_{s,k} : u_{s,k} | b_1 }`. **Cross-check against the fold template's
Edge exponents** (§5 there): every `M_{s,k}` consumed here equals `Mval(T_{s,k})` (Edge A birth
`(M(S)−J)(M^{(S+1)}−J)`, Edge B/C accumulation `+J_1(M^{(S+1)}−J)`), verified identically. The
principal-invariance step never re-derives an exponent — it reads the ledger.

!!! warning "PM-P5 — the ratios `b_i/b_1` must be genuine monomials (divisibility), and `U(0)=1` not `U≡1`"
    `U = 1 + Σ(b_i/b_1)²` is a unit **iff** each `b_i/b_1` is a polynomial (monomial), which holds **iff**
    `b_1 | b_i` — the divisibility chain. Assert the chain as the hypothesis of principality; assert
    `U(0) = 1` (so `U` is a local unit) but **not** `U ≡ 1`. This is the same unit-vs-function trap as
    PM-P1, now on the loss side.

---

## 4. The fold-to-value seam (`λ = C/2`)

### 4.1 Theorem 3: the regular Morse block + the core

Theorem 3 (paper p.13) peels the regular part of the product and splits the RLCT:

$$
\lambda_{\bar w}\Big\langle \textstyle\prod_s A^{(s)} - \prod_s \bar A^{(s)} \Big\rangle
= \underbrace{\frac{-r^2 + r(H^{(1)} + H^{(L+1)})}{2}}_{\text{regular Morse block (once, at the top)}}
\;+\; \underbrace{\lambda_0\Big\langle \textstyle\prod_s C^{(s)} \Big\rangle}_{= \, \tfrac12 \, \mathrm{cCodim}}.
$$

- The **prefactor** counts `½·#{ regular independent coordinates } = ½(−r² + r(H^{(1)}+H^{(L+1)}))` — a
  genuine `n/2` Morse contribution, occurring **once at the top**, not per layer.
- The **core** `λ_0⟨∏ C⟩` is exactly what §1–§3 resolve: `= ½·min_t Mval(t)`.

### 4.2 What is minimised over charts; where `minAdm` enters

The min-over-charts of §2.3, applied to the terminal read-off of §3, is:

$$
\lambda_{\mathrm{core}} = \tfrac12 \min\{ M_{s,k} : \tilde t_{s,k} = 0, \text{ over all charts} \}
= \tfrac12 \min_t \mathrm{Mval}(t) = \tfrac12\, \mathrm{minAdm} = \tfrac12\, \mathrm{cCodim}.
$$

- The **quantity minimised over charts** is the per-chart binding-axis exponent `M_{s,k}` (equivalently
  the ratio `M_{s,k}/2`). Each chart contributes its `t̃ = 0` divisors; the union over charts is the
  admissible rank-profile lattice.
- **`minAdm` enters** as the identity `min_t Mval(t) = minAdm = cCodim` (the QIP minimum = the geometric
  codimension; worked.tex Object D, `divisorMin_eq_cCodim`). The chart minimisation and the QIP/codim
  arithmetic meet here.

### 4.3 The value

Combining §4.1 and §4.2, with `C := ` full codimension of the zero fibre
`= −r² + r(H^{(1)}+H^{(L+1)}) + cCodim`:

$$
\boxed{\ \lambda = \frac{-r^2 + r(H^{(1)}+H^{(L+1)})}{2} + \tfrac12\,\mathrm{cCodim} = \frac{C}{2}.\ }
$$

Verified exact (`verify/path_verify.py`) including general `r`: `(3,3,4) r=0 → 4`; `(3,3,2,2) r=0 → 2`;
`(5,4,4) r=1 → 8`; `(4,4,4,4) r=2 → 15/2` — each equal to `C/2`.

!!! warning "PM-P6 — per-chart vs global; the prefactor is top-level, not per-layer"
    The core value is a **global** min over charts (`min_t`), not a per-chart or per-layer quantity. The
    Theorem-3 prefactor is a **single** top-level Morse block, added **once**; the drifted build's error
    was placing an `n/2` Morse term into **every** recursion node (worked.tex §3 gnote). Assert: exactly
    one prefactor, at the top; the core is `½·(global min over charts)`; do not sum per-chart values and
    do not add a Morse term per layer.

---

## 5. Worked instantiations (path-level)

Both cross-checked in `verify/path_verify.py`; the per-step exponents are from the fold template §5.

### 5.1 `d = (3,3,4)`, `L = 2`

- **Binding leaf's `b_1`**: the `t̃ = 0` divisors are `u_{1,1}` (`M = 9`) and `u_{1,2}` (`M = 8`, the
  boosted binder). So `b_1 = u_{1,1}·u_{1,2}` — squarefree, `k = 1` each.
- **Loss in the terminal chart**: `K(g(u)) = b_1²·U = (u_{1,1}u_{1,2})²·U`, `U(0)=1`.
- **Jacobian**: `|g'| = u_{1,1}^{8}·u_{1,2}^{7}·(other divisors)` — pure monomial, powers `M − 1`.
- **Read-off**: ratios `u_{1,1}: 9/2`, `u_{1,2}: 8/2 = 4`. Per-leaf min `= 4`.
- **Global**: over all leaves, `min = 4` at profile `t=(1,0)` ⟹ `λ_core = 4`.
- **Value**: `r = 0`, prefactor `= 0`, `C = cCodim = 8`, `λ = 4 = C/2`. ✓

### 5.2 `d = (3,3,2,2)`, `L = 3`

- **Three binding leaves**, all with `min M_{s,k} = 4`: the coupled `t=(2,1,0)` (born layer 1, boosted
  at `S=2` then `S=3`), and the clean `t=(3,1,0)`, `t=(3,2,0)` (born deep). Each contributes a `t̃=0`
  divisor of exponent `4`, ratio `4/2 = 2`.
- **Read-off / global**: `min = 4` ⟹ `λ_core = 2`.
- **Value**: `r = 0`, `C = cCodim = 4`, `λ = 2 = C/2`. ✓
- **Contrast (cover)**: the three binding leaves are **distinct charts** of the atlas; the global `λ` is
  the `min` over them (all tie at `2`). The pole order `θ` is a `max`-count over the tying charts — the
  `θ = a(ℓ−a)+1` combinatorics (out of scope here; charter Object E).

---

## 6. Pre-mortem list (path-level, concrete checkable assertions)

- **PM-P1 (two units).** `|g'| = ∏ u^{M-1}` is a pure monomial (unit `≡ 1`, from det-1 shears). The loss
  `K(g(u)) = b_1²·U` has `U` a unit-valued **function**, `U(0)=1`, `U ≢ 1`. Assert both; do not swap.
- **PM-P2 (integral identity).** `∫_V = ∫_Q = Σ_U ∫_U ρ_U` (partition of unity) **or** the a.e.-disjoint
  max-|pivot| sector partition. Assert one; **never** `∫_V = Σ_U ∫_U` bare (charts overlap).
- **PM-P3 (`k_j > 0` + sign typo).** The boxed min ranges over axes with `k_j > 0` (`k_j = 0` ⟹ ratio
  `+∞`, excluded). `h_j ≥ 0`, `k_j ≥ 1` on binding axes. The p.6 "non-positive integers" is a sign typo
  for **non-negative** — do not transcribe literally.
- **PM-P4 (the atlas gap — SHARPEST).** Coverage + termination of the exhaustive terminal-chart atlas
  from the representative pivot cases is **not** in the paper; it must be **built** (worked.tex hard part
  C; leaves `rlctAt_sumSqFam_eq_iInf_charts`, `exists_coreResolution`). Assert: this is a build target,
  not a citation; the single-`d_{J+1,J+1}`-pivot display stands for all symmetric pivots (relabelling
  owed).
- **PM-P5 (divisibility ⟹ principality).** `U = 1 + Σ(b_i/b_1)²` is a unit **iff** `b_1 | b_i` for all
  `i` (the chain). Assert the chain as the principality hypothesis; assert `U(0)=1`, not `U≡1`.
- **PM-P6 (per-chart vs global; prefactor top-level).** `λ_core = ½·(global min over charts)`, not a sum,
  not per-layer. Exactly one Theorem-3 Morse prefactor, at the top — never one per recursion node.
- **PM-P7 (Jacobian ledger accumulation).** For every divisor, Jacobian power `= M_{s,k} − 1` at all
  times; a Case-1 boost adds `J_1(M^{(S+1)}−J)` to **both** the exponent and the Jacobian power (they
  stay in lockstep). Assert: `jac = divExp − 1` is an invariant, not just a terminal coincidence.
- **PM-P8 (squarefree `b_1` ⟹ `k = 1`).** `b_1 = ∏_{t̃=0} u` is squarefree, so `k_{s,k} = 1` for every
  binding axis and the ratio is `M_{s,k}/2`. Assert `b_1` squarefree (distinct coords); a repeated
  coordinate (`k ≥ 2`) would halve the ratio and is a defect.
- **PM-P9 (θ is a max, not a sum).** The pole order aggregates as `max` over charts/points of the
  binding-axis count, not a sum (positivity, no cancellation). Assert the aggregator; do not sum `θ`
  across charts. (Relevant to charter Object E, not `λ`.)
- **PM-P10 (`minAdm` seam).** `min_t Mval(t) = minAdm = cCodim`. The chart-min meets the QIP/codim
  arithmetic here. Assert the identity is the join between the geometric read-off and the closed form;
  it is exact-enumeration-verified for bounded `(L, M)` but the general-`(L,M)` proof is the QIP identity
  (worked.tex owed item O5), not this template's scope.

---

## Open questions (registered)

- **Q-P1.** Which integral formalisation does the build use — partition of unity over `Q`, or the
  max-|pivot| sector partition? Both are sound (§2.2); they differ in the measure-theory API. Flagged for
  the formaliser; §2.2 states both.
- **Q-P2.** The p.6 change-of-variables display `|g'(u)|φ(g(u)) = u^h` folds the prior `φ(0) > 0` into the
  monomial. Reading adopted: `|g'|` is the pure monomial `∏ u^{M-1}`; `φ(g(u))` is a separate positive
  unit not affecting the threshold. Confidence high; flagged so the formaliser separates the two.
- **Q-P3.** The cover/termination atlas (PM-P4) is the named build target; its precise decomposition into
  lemmas (coverage, termination, pivot-relabelling) is for the formaliser/controller to route — this
  template states *what* must hold, not the Lean proof route (per the pen-and-paper boundary).

## Cross-references

- Per-step fold recursion: [`fold-recursion-template.md`](fold-recursion-template.md) (state, edges,
  clearing steps, terminal, worked traces, pre-mortem PM-1…PM-14).
- Paper: p.6 (boxed Hironaka rule), p.13 (Theorem 3 split), p.15 (Jacobian ledger), pp.22–26 (candidates,
  completing-the-square, Lemma 3, envelopes, Lemmas 4–5).
- Worked reproduction: `theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex` §1 (Lemma 1 ideal-
  invariance), §2.3 (boxed rule S2), §4 (candidates + minimisation); ledger items T-C/T-E/T-F/N-1.
- Verification: `threads/elaboration/verify/path_verify.py` (Jacobian monomial, ledger accumulation,
  read-off, value assembly); `step_verify.py`, `tree_final.py` (fold template).
- Decorrelated consult: `threads/elaboration/codex/cover-argument-{prompt,answer}.md`.
