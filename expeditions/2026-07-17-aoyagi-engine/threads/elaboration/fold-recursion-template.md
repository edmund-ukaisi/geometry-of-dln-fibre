---
title: "Aoyagi's fold recursion — a fully worked template"
status: draft
source: original
topics: [aoyagi, resolution, fold-recursion, blow-up, template, formalisation-spec]
created: "2026-07-22T09:30:00"
updated: "2026-07-22T09:30:00"
---

# Aoyagi's fold recursion — a fully worked template

This document elaborates the recursive blow-up of Aoyagi (2023), *Consideration on the learning
efficiency of multiple-layered neural networks with linear units*, pp.14–22 (the "mountain" of the
worked reproduction `theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex` §4). It is written so a
formaliser can render statements from it **without guessing**: every index convention is declared
before use, every clearing step is given in full block-display form, the residual / support /
coefficient windows are stated at every state, and the two standing instances are traced state by
state. A pre-mortem list at the end states each place a formalisation could go wrong as a concrete
checkable assertion.

Everything load-bearing here is checked with exact algebra (`sympy`), scripts banked under
`threads/elaboration/verify/`; one decorrelated Codex consult (`codex/fold-semantics-{prompt,answer}.md`)
independently confirmed the three hardest readings (start convention, whole-tail `b'`, Q/P shear
read-write). Where a reading of the paper is genuinely open, it is flagged **Question**, never
silently resolved.

The story is short: 1. the recursion carries a state `(S, J)` plus a monomial diagonal
`diag(b)` and a residual block `D_J`; 2. each step blows up the residual, normalises one pivot to
`1`, and clears one row (Q) and one column (P) by a Schur complement, shearing only the pivot row of
the very next layer; 3. cleared coordinates accumulate into exceptional divisors whose exponents are
`Mval(t)` for the branch's rank profile `t`; 4. at `S = L+1` the whole product is `diag(b)`, a normal
crossing, and the candidate learning coefficient is `½·min` of the terminal divisor exponents.

---

## 0. Index conventions (declared before use)

!!! warning "Conventions — all of §1–§6 uses these"
    - **1-indexed throughout** (matching the paper). Layers `s = 1, …, L`. Widths `M^(1), …, M^(L+1)`.
      A matrix `C^(s)` has size `M^(s) × M^(s+1)`: **rows** indexed by the first index `i ∈ [1, M^(s)]`,
      **columns** by the second index `j ∈ [1, M^(s+1)]`. Entry `(i, j)` is row `i`, column `j`.
    - **We work on the reduced core** `‖∏_{s=1}^{L} C^(s)‖²`, at the origin (all `c^(s)_{ij} = 0`),
      after Theorem 3 (peel the regular part) and Theorem 4 (deepest point). At the zero-product fibre
      `r = 0`, so `M^(s) = H^(s)` and the core is the whole loss; for `r > 0` these are the reduced
      widths. The fold recursion is exactly about this core.
    - **Running minimum** `M(S) := min{ M^(s) : 1 ≤ s ≤ S }` for `S ≥ 1`. This caps the **row** axis of
      the residual (equivalently the size of `diag(b)`); the **column** axis is capped by `M^(S+1)`, the
      current next-layer input width. `M(S+1) := min{M(S), M^(S+1)}` is the number of pivots clearable in
      the current layer phase (Question Q1 pins the two readings of the symbol `M(S+1)`; see below).
    - **State** `(S, J)`: `0 ≤ S ≤ L` counts layers fully absorbed into `diag(b)`; `0 ≤ J ≤ M(S+1)` counts
      pivots cleared in the layer currently being absorbed. `S` advances the row/diagonal axis; `J` is the
      **within-layer descent** (each clear removes one row and one column of the residual).
    - **Exceptional coordinates** `u_{s,k}`: introduced when clearing the `k`-th pivot during the phase
      that absorbs into layer `s`. Each carries a **profile** `T_{s,k} = (t^(1)_{s,k}, …, t^(L)_{s,k})`
      and an accumulated **exponent** `M_{s,k}` (its Jacobian power is `M_{s,k} − 1`). Write
      `t̃_{s,k} := min_S t^(S)_{s,k}` (the paper's `~t`).

!!! danger "Symbol collision (name it, do not conflate)"
    The symbol `M(S)` (running-min, a *number*) and the widths `M^(s)` (a *sequence*) look alike; keep
    them distinct. The symbol `M(S+1)` overloads: `M(S+1) = min{M(S), M^(S+1)}` (the per-phase pivot cap)
    is **not** `M^(S+1)` (the raw width). And "`M_{s,k}`" (a divisor exponent) is a third, unrelated `M`.
    The paper reuses `M` for all three; this template keeps `M(S)` (running-min), `M^(s)` (width),
    `M_{s,k}` (exponent) visually distinct. This collision is pre-mortem item **PM-1**.

---

## 1. The state and the transition law for every edge kind

### 1.1 What a node carries

A node of the recursion at state `(S, J)` carries:

- `S, J` — the state indices above.
- **The diagonal** `diag(b_1, …, b_{M(S)})`, size `M(S) × M(S)`. Each `b_i` is a **monomial in the
  exceptional coordinates only** (no `c`-variables), defined by

$$
b_0 = 1, \qquad b_i = \Big(\textstyle\prod_{\tilde t_{s,k} = i-1} u_{s,k}\Big)\, b_{i-1}, \quad i = 1, \dots, M(S).
$$

  Unrolled, `b_i = ∏_{t̃_{s,k} < i} u_{s,k}`. Consequence: `b_1 | b_2 | ⋯ | b_{M(S)}` — the
  **divisibility chain**, by construction. (Verified structurally; it is the hypothesis under which the
  monomial-RLCT boxed rule is a theorem — worked.tex Object C.)
- **The residual block** `D_J = (d_{ij})`, `J+1 ≤ i ≤ M(S)`, `J+1 ≤ j ≤ M^(S+1)`, of size
  `(M(S) − J) × (M^(S+1) − J)`. Its entries are the fresh residual coordinates (see §3 for what they
  encode). The full "collapsed head" matrix is

$$
\begin{pmatrix} E_J & O \\ O & D_J \end{pmatrix}, \qquad \text{size } M(S) \times M^{(S+1)},
$$

  and the standing **invariant** is

$$
\Big\langle \textstyle\prod_{s=1}^{L} C^{(s)} \Big\rangle
= \Big\langle \operatorname{diag}(b_1,\dots,b_{M(S)}) \begin{pmatrix} E_J & O \\ O & D_J \end{pmatrix}
  \textstyle\prod_{s=S+1}^{L} C^{(s)} \Big\rangle .
$$

- **The exceptional/`b`-monomial data**: the set of coordinates `u_{s,k}` introduced so far, each with
  its profile `T_{s,k}` and exponent `M_{s,k}`. The `b`-chain is a *derived* view of this set (via `t̃`).

### 1.2 The start (the `S = 0` base — two objects both called `D_0`)

At `(S, J) = (0, 0)` the invariant is the tautology `⟨∏ C⟩ = ⟨∏ C⟩`. Concretely
(Codex-confirmed, high confidence):

- `M(0) := M^(1)`; `diag(b_1, …, b_{M^(1)}) = I_{M^(1)}` (all `b_i = 1`, no `u`'s yet); `E_0` is the
  `0 × 0` identity; the **`S = 0` auxiliary residual** is `D_0 = I_{M^(1)}` (size `M^(1) × M^(1)`). RHS
  `= I · I · ∏_{s=1}^{L} C^(s) = ∏ C`. ✓

The **first genuine blow-up acts at `(S, J) = (1, 0)`**, where the residual — confusingly *also*
written `D_0` in the paper — is

$$
D_0 = C^{(1)}, \qquad \text{size } M(1) \times M^{(2)} = M^{(1)} \times M^{(2)},
$$

with `diag(b) = I_{M^(1)}` still. RHS `= I · C^(1) · ∏_{s=2}^{L} C^(s) = ∏ C`. ✓

!!! danger "PM-2 — the two `D_0`s"
    The `S = 0` auxiliary `D_0 = I_{M^(1)}` (square) and the `S = 1` residual `D_0 = C^(1)`
    (`M^(1) × M^(2)`, generally non-square) are **different objects with the same name**. Taking
    `D_0 = C^(1)` already at `S = 0` is dimensionally wrong and duplicates `C^(1)`. Codex named this the
    single sharpest disagreement-risk. A formalisation should start the recursion at `(1, 0)` with
    `D_0 = C^(1)` and treat `S = 0` as the trivial base, or index so the collision cannot arise.

### 1.3 The equal-run classifier at `(S, J)`

Look at the tail `b_{J+1}, …, b_{M(S)}`. A **jump** sits at position `p` iff some `u_{s,k}` has
`t̃_{s,k} = p` (then `b_p ≠ b_{p+1}`). Let

$$
J_1 := \big(\min\{\, \tilde t_{s,k} : \tilde t_{s,k} \ge J+1 \,\}\big) - J,
$$

i.e. `b_{J+1} = ⋯ = b_{J+J_1}` and `b_{J+J_1} ≠ b_{J+J_1+1}` (the first jump at or after `J+1`).

- **Case 2** (full remaining block): no jump in `[J+1, M(S)−1]`, i.e. `b_{J+1} = ⋯ = b_{M(S)}` and
  `J_1 = M(S) − J`.
- **Case 1** (partial block): a jump at `J + J_1 < M(S)`; some `u_{s,k}` has `t̃_{s,k} = J + J_1`.

### 1.4 The transition law, edge by edge

There are **four** edge kinds. All four are verified end-to-end by the branching-tree simulator
(`verify/tree_final.py`): the emitted exponents and their minimum reproduce `minAdm` exactly for
`(3,3,4)`, `(3,3,2,2)`, `(2,2,2)`, `(2,2,2,2)`.

#### Edge A — Case 2 clear (a *fresh* divisor)

Precondition: Case 2 at `(S, J)`; `J + 1 ≤ M(S+1)`. Blow up the **whole** residual block
`{ d_{ij} = 0 : J+1 ≤ i ≤ M(S), J+1 ≤ j ≤ M^(S+1) }` (no `u` joins the centre — there is no jump to
pair with). In the pivot chart `d'_{J+1,J+1} = 1`:

- **emit** a new coordinate `u_{S,J+1}` with

$$
t^{(i)}_{S,J+1} = M^{(i+1)} \ (1 \le i \le S-1), \qquad t^{(S)}_{S,J+1} = \dots = t^{(L)}_{S,J+1} = J,
\qquad \tilde t_{S,J+1} = J,
$$

  and a **fresh** exponent

$$
M_{S,J+1} = (M(S) - J)\,(M^{(S+1)} - J) \quad (\text{the codimension of the blown-up block}).
$$

- **`b`-update**: `b'_i = u_{S,J+1}\, b_i` for **all** `i = J+1, …, M(S)` (the whole tail).
- **`(S, J)` update**: `J → J + 1` (one row and one column of the residual are removed; see §2).

#### Edge B — Case 1(1) boost (accumulate onto an *existing* divisor; no `J`-advance)

Precondition: Case 1 at `(S, J)`, run length `J_1`. Fix the coordinate `u_{s,k}` with
`t̃_{s,k} = J + J_1` that is **minimal in `T`-order** among those at that jump (the paper's tie-break;
pre-mortem PM-6). Blow up `{ d_{ij} = 0 : J+1 ≤ i ≤ J+J_1, j = J+1, …, M^(S+1); u_{s,k} = 0 }`. In the
chart where the `d`-block `= u_{s,k}·d'` (i.e. `u_{s,k}` stays the exceptional coordinate):

- **reset** the profile of `u_{s,k}`: `t^(S)_{s,k} = ⋯ = t^(L)_{s,k} = J`, hence `t̃_{s,k} → J`;
- **boost** its exponent: `M_{s,k} → M_{s,k} + J_1·(M^{(S+1)} − J)`;
- **`b`-update**: `b'_i = u_{s,k}·b_i` only for the **partial** block `i = J+1, …, J+J_1`;
- **no `J`-advance** — re-evaluate at the same `(S, J)`. The count of `u`'s with `t̃ = J+J_1` has
  dropped by one (an inner recursion on the multiplicity at that jump).

#### Edge C — Case 1(2) clear (a *new inherited* divisor; `J`-advance)

Same precondition. In the chart where one block entry is the pivot (`d_{J+1,J+1} = u_{S,J+1}·1`) and
`u_{s,k} = u_{S,J+1}·u'_{s,k}`:

- **emit** a new coordinate `u_{S,J+1}` **inheriting** the shallow coordinates from `u_{s,k}`:

$$
t^{(i)}_{S,J+1} = t^{(i)}_{s,k} \ (1 \le i \le S-1), \qquad t^{(S)}_{S,J+1} = \dots = t^{(L)}_{S,J+1} = J,
$$

  with exponent `M_{S,J+1} = M_{s,k} + J_1·(M^{(S+1)} − J)` (same value as the Edge-B boost);
- **`b`-update**: `b'_i = u_{S,J+1}·b_i` for the **whole** tail `i = J+1, …, M(S)` (see §3.3 for why
  the whole tail, not just the partial block);
- **`(S, J)` update**: `J → J + 1`.

!!! warning "PM-3 — Edge B (raw-width `t^{<S} = M^{(i+1)}`) vs Edge C (inherited `t^{<S} = t^{(i)}_{s,k}`)"
    Case 2 (Edge A) sets the shallow coordinates to the **raw width** `M^{(i+1)}`; Case 1(2) (Edge C)
    sets them to the **inherited** `t^{(i)}_{s,k}`. This asymmetry is real (ledger item **T-E**, image-
    confirmed p.20 vs p.17) and at non-monotone widths the raw-width label contradicts the paper's own
    p.22 candidate formula. **The exponents are unaffected** (they are computed from `J_1`, `M^(S+1)`,
    `J` — never from the `T`-label); this is why the Lean record carries `bexp`/`jac` but **no `T`
    field** at all. A formalisation must not key exponents off the `T`-label. See §3.4 and PM-9.

#### Edge D — rollover (layer done: `S → S+1`)

Precondition: `J + 1 > M(S+1) = min{M(S), M^{(S+1)}}` — all pivots of the current phase are cleared.
Then `D'''_J = (1, 0, …, 0)` (row) or `(1, 0, …, 0)^t` (column) and the head is fully diagonal. The
invariant becomes

$$
\Big\langle \textstyle\prod C^{(s)} \Big\rangle
= \Big\langle \operatorname{diag}(b_1,\dots,b_{M(S+1)})\, C'^{(S+1)} \textstyle\prod_{s=S+2}^{L} C^{(s)} \Big\rangle ,
$$

which is the invariant at `(S+1, 0)` with the new residual `D_0^{(S+1)} = C'^{(S+1)}` (the accumulated
`Q^{-1}`-recoordinatised next-layer matrix, size `M(S+1) × M^{(S+2)}`), running-min updated to
`M(S+1) = min{M(S), M^{(S+1)}}`, and no new `u`.

!!! warning "PM-4 — the running-min may shrink at rollover"
    When `M^{(S+1)} < M(S)` (e.g. `(3,3,2,2)` at `S=2→3`: `M(2)=3` drops to `M(3)=2`), the diagonal
    shrinks from `M(S)` to `M(S+1)` rows. Coordinates whose `t̃ ≥ M(S+1)` no longer index any `b_i`
    (there is no `b_i` with `i > M(S+1)`); they cease to affect the terminal `b`-chain. A formalisation
    must handle the diagonal truncation at rollover and not assume `diag(b)` only grows.

At `S = L+1` the recursion terminates: `⟨∏ C⟩ = ⟨diag(b_1, …, b_{M(L+1)})⟩`. See §4.

---

## 2. Each clearing step in full block-display form

Every clear (Edge A / Edge C) has the same three-move shape once the blow-up chart has normalised the
pivot to `1`. This is the single most load-bearing computation; it is verified symbolically on generic
blocks in `verify/step_verify.py` (all four checks PASS).

### 2.1 The normalised block, and `β, γ, δ` as explicit index sets

After the pivot chart, the active block (rows `J+1, …, M(S)`, columns `J+1, …, M^{(S+1)}`, with the
common `u`-factor already pulled out front into `diag(b')`) is

$$
D' = \begin{pmatrix} 1 & \beta \\ \gamma & \delta \end{pmatrix},
$$

with the explicit index sets (relative to the current block, pivot at local `(1,1) = (J+1, J+1)`):

- `β = (d'_{J+1,\,J+2}, …, d'_{J+1,\,M^{(S+1)}})` — the **pivot row tail**, a `1 × (M^{(S+1)} − J − 1)`
  row (columns `J+2 … M^{(S+1)}` of row `J+1`);
- `γ = (d'_{J+2,\,J+1}, …, d'_{M(S),\,J+1})^t` — the **pivot column tail**, an `(M(S) − J − 1) × 1`
  column (rows `J+2 … M(S)` of column `J+1`);
- `δ = (d'_{ij})_{J+2 ≤ i ≤ M(S),\; J+2 ≤ j ≤ M^{(S+1)}}` — the **deep block**, size
  `(M(S) − J − 1) × (M^{(S+1)} − J − 1)`.

### 2.2 The Q step (clears the pivot **row**; recoordinatises the next layer)

$$
Q = \begin{pmatrix} 1 & -\beta \\ 0 & I \end{pmatrix} \quad \text{(size } (M^{(S+1)}-J) \times (M^{(S+1)}-J), \ \det Q = 1),
$$

applied on the **right**. Then

$$
D'' = D'\,Q = \begin{pmatrix} 1 & 0 \\ \gamma & \delta - \gamma\beta \end{pmatrix}.
$$

- **READS**: the pivot row tail `β` only.
- **WRITES**: the pivot row → `(1, 0, …, 0)`; the deep block → the **Schur complement `δ − γβ`**
  (with respect to the `1 × 1` pivot `d'_{J+1,J+1} = 1`). The pivot column `γ` is untouched by Q.
- **Cross-layer coupling — where `Q^{-1}` on `C^{(S+1)}` enters**: simultaneously the next-layer matrix
  is recoordinatised `C'^{(S+1)}_J = Q^{-1} C^{(S+1)}_J`, so the product `D_J · C^{(S+1)}_J` is
  **unchanged** (`D'' · Q^{-1}C = D' C`). Since `Q^{-1} = I + e_1·(0, β)`, this modifies **only the
  pivot row of `C^{(S+1)}`** — rows `2, …` of `C^{(S+1)}` and the deeper layers `C^{(S+2)}, …, C^{(L)}`
  are untouched (verified; Codex-confirmed). This is the "shear of the residual into the next layer" —
  the one place a residual entry writes into a *deeper* factor, and it writes exactly one row.

### 2.3 The P step (clears the pivot **column**; `b'`-conjugated so `diag(b')` stays out front)

The paper's `P` is the `diag(b')`-conjugate of the plain column-clearing shear
`P̂ = [[1, 0], [−γ, I]]`:

$$
P = \operatorname{diag}(b') \, \hat P \, \operatorname{diag}(b')^{-1}, \qquad
P_{i,\,J+1} = -\frac{b'_i}{b'_{J+1}}\, d''_{i,\,J+1} \ \ (i = J+2, \dots, M(S)),
$$

with `diag(b') = diag(b'_{J+1}, …, b'_{M(S)})`. Then

$$
P \, \operatorname{diag}(b')\, D''\, C'^{(S+1)}_J = \operatorname{diag}(b')\, D'''\, C'^{(S+1)}_J,
\qquad D''' = \begin{pmatrix} 1 & 0 \\ 0 & \delta - \gamma\beta \end{pmatrix} = \begin{pmatrix} 1 & O \\ O & D_{J+1} \end{pmatrix}.
$$

- **READS**: the pivot-column tail `γ = (d''_{i,J+1})` and the monomial ratios `b'_i / b'_{J+1}`.
- **WRITES**: the pivot column → `0`. The Schur block `δ − γβ` (already produced by Q) is left
  unchanged. Net residual `D_{J+1} = δ − γβ`, size `(M(S) − J − 1) × (M^{(S+1)} − J − 1)`.
- **Regularity (why `P` is a unit)**: `P` has polynomial (indeed monomial) entries **iff**
  `b'_{J+1} | b'_i` for all `i` in the tail. This holds because the `b`-sequence is a **divisibility
  chain** (§1.1): `b'_{J+1} | b'_i`, so `b'_i / b'_{J+1}` is a genuine monomial. Conjugating by
  `diag(b')` is what keeps `diag(b')` factored out front while the shear acts — the recursion never
  divides by a `b`.

!!! note "The Schur displacement, in one line"
    `δ ↦ δ − γβ`, pivot `= 1`. The Q step **produces** it in the SE corner; the P step **confirms** it
    by clearing the column Q left as `γ`. Because Q already zeroed the pivot row, the P step introduces
    **no further displacement** in the deep block (the second Schur term vanishes) — a formalisation
    subtlety worth stating (PM-7).

### 2.4 What is a pivot, precisely

The pivot `d'_{J+1,J+1} = 1` is created by the **blow-up normalisation**, not by the loss: in the
chosen chart, one centre coordinate is inverted and the block is divided by it, so the top-left entry
becomes the unit `1`. The Schur complement is therefore always with respect to a `1 × 1` unit pivot —
there is never a division by a non-unit. This is why every step is ideal-preserving and unit-Jacobian
(exact, no lossy factorisation).

---

## 3. The residual through the recursion (support and coefficient windows)

### 3.1 The "cross-layer product residual (one factor per layer)"

A **binding branch's** terminal generator is a product with **one factor per layer**: the exceptional
divisor of that branch divides across the layers. For `(3,3,4)` the binding branch's loss factors as
`E² · unit` where `E = u_{1,2}` divides the entire `b`-chain (verified `g-coupled-334-diagb.py`:
`b = (E, Eαv, Eαvδw)`). The recursion's job is to expose this single principal factor; the support and
coefficient windows below track *where* the residual lives so the factorisation is exact.

### 3.2 Support window and coefficient window at every state

At `(S, J)`, decompose the invariant's right-hand matrix into three zones:

| zone | what | support window | coefficient window |
|---|---|---|---|
| `diag(b)` | `b_1, …, b_{M(S)}` | the diagonal, size `M(S)` | **exceptional `u`'s only** — no `c`-variables |
| head `[[E_J, O],[O, D_J]]` | `E_J` cleared pivots + residual `D_J` | `E_J`: diagonal rows `1…J`. `D_J`: rows `J+1…M(S)`, cols `J+1…M^{(S+1)}` | `D_J` entries are fresh residual coords (see §3.4) |
| tail `∏_{s>S} C^{(s)}` | untouched deeper layers | full `M^{(S+1)} × M^{(L+1)}` | free `c^(s)` for `s > S`, **except** the pivot rows of `C^{(S+1)}` already sheared by `Q^{-1}` (§2.2) |

!!! warning "PM-5 — the residual support is the width-capped block, not the full layer"
    The residual `D_J` at `(S, J)` occupies **rows `[J+1, M(S)]`** — capped by the running-min `M(S)`,
    **not** by `M^(S)` and **not** the full next layer. The columns are `[J+1, M^{(S+1)}]`. A leaf that
    reads the support as "the full layer `S+1`" or caps the row axis by `M^{(S+1)}` instead of `M(S)` is
    the exact class of defect (support-window extent, shear support) this expedition caught repeatedly.
    Assertion to check: `D_J : (M(S) − J) × (M^{(S+1)} − J)` at every state, row axis capped by `M(S)`.

### 3.3 First clear (strict transform) vs later clears (pullback)

The charge's `δ = 1` / `δ = 0` distinction maps onto the paper mechanism as follows. **This mapping to
the Lean `edgeδ` field is my interpretation** (I cannot read the Lean); it is registered as Question Q3
for the controller to diff against the definitions.

- **First clear of a layer (`J = 0`, right after rollover) — "strict transform", `δ = 1`.**
  The residual `D_0 = C^{(S+1)}` is the **fresh next-layer matrix**: its entries are degree-1 in the
  layer-`(S+1)` `c`-variables. The blow-up introduces `u_{S+1,1}`, and the residual generator is
  **exactly divisible** by that pivot coordinate — the strict transform. In the cross-layer product,
  the factor that *gains the pivot* is the newly-absorbed layer `S+1`; the degree-1 support sits in
  layer `S+1`'s columns **before** the clear and, **after**, is carried by the exceptional `u` times the
  Schur complement.

- **Later clears within a layer (`J ≥ 1`) — "pullback", `δ = 0`.**
  The residual `D_J` is already a Schur complement from the previous clear; the coordinate structure is
  inherited (pulled back), and the step is the pure Schur move of §2 with the `b`-chain carrying the
  accumulated `u`'s. No *new* layer gains a pivot; the descent is within the current layer.

!!! note "Why Case 1(2) multiplies the *whole* tail (Codex-confirmed, medium→high)"
    In Case 1(2) the fixed old coordinate `u_{s,k}` (with `t̃_{s,k} = J + J_1`) appears in **every**
    `b_i` with `i > J + J_1` (since `b_i = ∏_{t̃ < i} u`). The chart substitution `u_{s,k} = u_{S,J+1}·u'_{s,k}`
    therefore injects one factor `u_{S,J+1}` into every tail row `i > J + J_1` **through its existing
    `b_i`**; the partial block rows `J+1, …, J+J_1` acquire the same `u_{S,J+1}` **through**
    `d_{ij} = u_{S,J+1}·d'_{ij}`. The two sources combine to one common factor `u_{S,J+1}` across the
    whole tail `J+1, …, M(S)` — hence `b'_i = u_{S,J+1} b_i` for all `i` in the tail. In Case 1(1),
    `u_{s,k}` itself stays exceptional, so only the centred rows gain a *newly recorded* factor; the tail
    rows already contained `u_{s,k}`. This is why Edge A/C update the whole tail and Edge B only the
    partial block. The decisive index condition is `t̃_{s,k} = J + J_1` (in the paper: "Fix `u_{s,k}`
    such that `t̃_{s,k} = J + J_1`…").

### 3.4 The per-layer degree profile (where degree-2 legitimately appears)

The Schur complement `δ − γβ` has a **degree-2 residue** `γβ` (product of two degree-1 blocks). So:

- **The cleared layer legitimately carries degree 2**: after the first clear, `D_1 = δ − γβ` has
  entries of degree 2 in the pre-clear residual coordinates. The recursion then treats `d''_{ij}` as
  **fresh coordinates** via a unit-Jacobian change of variables (`d''_{ij} → d_{ij}`), so the *stated*
  residual entries are degree-1 fresh coords that **encode** the degree-2 polynomial. The
  coefficient window of the fresh `d_{ij}` is: the layer-`S` residual/deep `c`-variables and the `u`'s
  — **not** the cleared pivot rows `E_J` and **not** the deeper layers `C^{(S+1)}…`.
- **`diag(b)` never exceeds degree 0 in `c`** — it is pure `u`-monomial.

!!! warning "PM-8 — the coefficient window of a fresh residual coordinate"
    The change of variables `d''_{ij} → d_{ij}` is a **unit-Jacobian analytic isomorphism**; the fresh
    `d_{ij}` may read only the layer-`S` residual coordinates (and `u`'s), never the already-cleared
    pivots or the untouched deeper layers. A formalisation that lets a residual coordinate read a
    cleared-pivot variable, or a deeper layer's variable it should not, breaks ideal-preservation. This
    is the "coefficient window too loose" defect class.

---

## 4. The terminal (exhaustion, last-layer clears, Bézout collapse)

### 4.1 The exhaustion / rollover guard, and why `cleared ≥ 1`

The layer-`S` phase runs `J = 0, 1, …` while `J + 1 ≤ M(S+1) = min{M(S), M^{(S+1)}}`; it rolls over
(Edge D) at `J + 1 > M(S+1)`. Since `M(S+1) = min{M(S), M^{(S+1)}} ≥ 1` for positive widths, **at least
one clear happens before any rollover** (`J` reaches `≥ 1` at every terminal-reaching edge). This is the
guard that prevents a vacuous phase. Assertion: `M(S+1) ≥ 1` (positive widths) ⟹ every phase clears
`≥ 1` pivot.

### 4.2 The last-layer clears build the generator / unit data

At `S = L` (the deepest layer), the phase clears `M(L+1) = min` pivots; the residual collapses to a
single `1` (row or column `D'''_J = (1,0,…,0)`), and the invariant reaches `S = L+1`:

$$
\Big\langle \textstyle\prod_{s=1}^{L} C^{(s)} \Big\rangle = \big\langle \operatorname{diag}(b_1, \dots, b_{M(L+1)}) \big\rangle .
$$

The generators are exactly the diagonal monomials `b_1, …, b_{M(L+1)}`, a **normal-crossing** family
(each `b_i` a `u`-monomial, `b_1 | ⋯ | b_{M(L+1)}`).

### 4.3 The final collapse's exact input shape

The loss in the terminal chart is

$$
\Big\| \textstyle\prod_{s=1}^{L} C^{(s)} \Big\|^2 \ \leadsto \ b_1^2 + b_2^2 + \dots + b_{M(L+1)}^2,
$$

a **sum of squared monomials** (not literally equal — Frobenius is not preserved by the non-orthogonal
`Q, P`; equal *as ideals* via Lemma 1, worked.tex §1). Because `b_1 | b_i` for all `i`, the ideal is
**principal**: `⟨b_1, …, b_{M(L+1)}⟩ = ⟨b_1⟩`, and

$$
b_1^2 + \dots + b_{M(L+1)}^2 = b_1^2 \cdot \underbrace{\big(1 + (b_2/b_1)^2 + \dots + (b_{M(L+1)}/b_1)^2\big)}_{\text{unit, } = 1 \text{ at the origin}} .
$$

So the input shape to the collapse is: **one dominant monomial `b_1`** (the product of all `u_{s,k}`
with `t̃_{s,k} = 0`) times a unit. This is the "Bézout / principal collapse": the RLCT is read off `b_1`
alone via the monomial boxed rule, `2·rlct = min over binding axes (h + 1)`, `h_e = M_{s,k} − 1`. The
candidate learning coefficient is

$$
\boxed{\ \operatorname{rlct}_{\mathrm{core}} = \tfrac12 \min\{\, M_{s,k} : \tilde t_{s,k} = 0 \,\}\ }
\qquad
M_{s,k} = (M^{(1)} - t^{(1)}_{s,k})(M^{(2)} - t^{(1)}_{s,k}) + \sum_{j=2}^{L} (t^{(j-1)}_{s,k} - t^{(j)}_{s,k})(M^{(j+1)} - t^{(j)}_{s,k}).
$$

!!! note "The min is over terminal divisors (`t̃ = 0`) only"
    Only coordinates with `t̃_{s,k} = 0` (those dividing `b_1`) are candidates. Verified: for every
    realized terminal divisor, `M_{s,k} = Mval(T_{s,k})` exactly (`verify/tree_final.py`), and the set of
    emitted exponents equals `{Mval(t)}` over the admissible profile lattice, so the min equals the
    geometric `min_t Mval(t) = minAdm`.

---

## 5. Worked instantiations

Both traces are produced and checked by `verify/trace334.py`, `verify/tree_final.py`,
`verify/trace3322.py`. Every exponent below satisfies `M_{s,k} = Mval(T_{s,k})`; the overall minimum
matches the independent `minAdm` recursion.

### 5.1 `d = (3, 3, 4)` — `N = L = 2`, the small-depth coupled shadow

Widths `M^(1)=3, M^(2)=3, M^(3)=4`. `M(1)=3, M(2)=3, M(3)=3`. `C^(1)` is `3×3`, `C^(2)` is `3×4`.

**Terminal profile census** (all `t^(2) = 0`, computed + verified):

| profile `t` | `Mval` | realized? |
|---|---|---|
| `(0,0)` | 9 | yes |
| `(1,0)` | **8** | yes — **binding** |
| `(2,0)` | 9 | yes |
| `(3,0)` | 12 | yes |

`min = 8` at `t = (1,0)` ⟹ `rlct_core = 4` (matches `minAdm(3,3,4) = 8`, and `g-coupled-334-diagb.py`
`h_e = 7`, `rlct = 4`).

**State-by-state (binding path).** Layer 1 is **pure Case 2** (the tail stays all-equal because each
clear multiplies the whole tail by one `u`); layer 2 is where the jumps appear and Case 1 boosts fire.

| state `(S,J)` | classifier | edge | action | divisor / profile | exponent |
|---|---|---|---|---|---|
| `(1,0)` | Case 2 (`b=1,1,1`) | A | blow up `3×3`; `Q,P` Schur → `D_1` `2×2` | `u_{1,1}`, `T=(0,0)`, `t̃=0` | `M = 3·3 = 9` |
| `(1,1)` | Case 2 (`b=u,u,u`) | A | blow up `2×2` → `D_2` `1×1` | `u_{1,2}`, `T=(1,1)`, `t̃=1` | `M = 2·2 = 4` |
| `(1,2)` | Case 2 (single) | A | blow up `1×1`; then `J+1=3 = M(2)` | `u_{1,3}`, `T=(2,2)`, `t̃=2` | `M = 1·1 = 1` |
| `(1,3)` | — | D | rollover `S:1→2`; `D_0^{(2)} = C'^{(2)}` (`3×4`) | `b = (u_{1,1}, u_{1,1}u_{1,2}, u_{1,1}u_{1,2}u_{1,3})` | — |
| `(2,0)` | **Case 1** (`b_1 ≠ b_2`, `J_1=1`) | **B** | boost `u_{1,2}`: reset `t^(2):1→0`, `t̃:1→0` **terminal** | `u_{1,2}`, `T=(1,0)` | `M = 4 + 1·(4−0) = 8` |

The **binding divisor** is `u_{1,2}`: born in layer 1 (Case 2, `T=(1,1)`, `M=4`), then **boosted** in
layer 2 (Case 1(1), profile reset to `(1,0)`, exponent `4 → 8`). Its Jacobian power is `h = 8 − 1 = 7`
— exactly the `h_e = 7` of the independently-computed `diag(b)` certificate. This is the mechanism by
which a *non-balanced* profile (`t^(1) = 1 ≠ t^(2) = 0`) is realized: a divisor born balanced in an
early layer has its deeper coordinate reset by a Case-1 boost in a later layer.

**Concrete first step (matrices).** At `(1,0)`, `D_0 = C^(1)` (`3×3`). Case-2 pivot chart:
`C^(1) = u_{1,1}·C̄` with `C̄_{11} = 1`. With `β = (C̄_{12}, C̄_{13})`, `γ = (C̄_{21}, C̄_{31})^t`,
`δ = (C̄_{ij})_{i,j∈{2,3}}`:

$$
Q = \begin{pmatrix} 1 & -\beta \\ 0 & I_2 \end{pmatrix}, \quad
\bar C\, Q = \begin{pmatrix} 1 & 0 \\ \gamma & \delta - \gamma\beta \end{pmatrix}, \quad
D_1 = \delta - \gamma\beta \ (2\times2),
$$

and `C^(2)` is recoordinatised `C'^(2) = Q^{-1} C^(2)` (only its first row changes). `diag(b) = diag(u_{1,1},u_{1,1},u_{1,1})`.
(Verified exact, `verify/trace334.py`.)

### 5.2 `d = (3, 3, 2, 2)` — `N = L = 3`, exhibits the within-layer descent

Widths `M^(1)=3, M^(2)=3, M^(3)=2, M^(4)=2`. `M(1)=3, M(2)=3, M(3)=2, M(4)=2`. `C^(1)` `3×3`,
`C^(2)` `3×2`, `C^(3)` `2×2`.

**Terminal profile census** (`t^(3) = 0`, verified):

| profile `t` | `Mval` | note |
|---|---|---|
| `(2,1,0)` | **4** | **binding — coupled** (layer-1 corank `(1,1)` scalar `δ`) |
| `(3,1,0)` | **4** | **binding — clean** |
| `(3,2,0)` | **4** | **binding — clean** |
| `(2,0,0)` | 5 | |
| `(1,0,0)`, `(1,1,0)`, `(3,0,0)` | 6 | |
| `(0,0,0)` | 9 | |

`min = 4` ⟹ `rlct_core = 2` (matches `minAdm(3,3,2,2) = 4`). Three profiles bind — the coupled
`(2,1,0)` and two clean ones — matching worked.tex exactly.

**Coupled binding path `t = (2,1,0)` — two successive boosts (the within-layer descent).**

| state `(S,J)` | edge | action | profile after | exponent after |
|---|---|---|---|---|
| `(1,2)` | A (Case 2) | born fresh in layer 1, block `1×1` | `T = (2,2,2)`, `t̃=2` | `M = 1·1 = 1` |
| `(2,1)` | B (Case 1(1)) | boost, `J_1=1`: reset `t^(2..3)=1` | `T = (2,1,1)`, `t̃=1` | `M = 1 + 1·(M^{(3)}−1) = 1 + 1·1 = 2` |
| `(3,0)` | B (Case 1(1)) | boost, `J_1=1`: reset `t^(3)=0`, `t̃→0` **terminal** | `T = (2,1,0)` | `M = 2 + 1·(M^{(4)}−0) = 2 + 1·2 = 4` |

The coupled binder is born in layer 1 and boosted **once per subsequent layer** (`S=2` then `S=3`),
each boost resetting the next-deeper coordinate to the current `J` and adding `J_1·(M^{(next)} − J)` to
the exponent. This is the cross-layer coupling in its purest visible form. `h = 4 − 1 = 3`.

**Clean binding path `t = (3,2,0)` — for contrast, one Case-2 birth, no boost.**

| state `(S,J)` | edge | action | profile | exponent |
|---|---|---|---|---|
| `(3,0)` | A (Case 2) | born fresh in layer 3, block `2×2` | `T = (3,2,0)`, `t̃=0` **terminal** | `M = (M(3)−0)(M^{(4)}−0) = 2·2 = 4` |

A layer-3 Case-2 birth inherits the raw shallow widths `t^(1)=M^(2)=3, t^(2)=M^(3)=2` and sets
`t^(3)=J=0`. No boost needed — it is terminal at birth. (This is the `c_1 = 0` "clean" branch of the
partial-rank dichotomy in worked.tex §4.)

!!! note "The within-layer descent, named"
    In `(3,3,2,2)`, layer 1 has `M(1) = 3` so `J` descends `0 → 1 → 2 → 3` (three clears within one
    layer); layer 2 has `M(2) = 3`, `M(3) = min = 2`, so it clears `J: 0 → 1 → 2` (two clears) before
    rollover shrinks the diagonal to `2`. The "within-layer descent" is exactly this `J`-loop inside a
    fixed `S`, distinct from the `S`-rollover. Both binders exercise it differently: the coupled one via
    Case-1 boosts *across* the descent boundaries, the clean one by a single Case-2 birth deep in.

---

## 6. Pre-mortem list (concrete checkable assertions)

Each item is a place a formalisation could plausibly go wrong, stated as an assertion the controller can
diff against the build. Prefixed **PM-n**; cross-referenced above.

- **PM-1 (symbol collision).** `M(S)` (running-min number), `M^(s)` (width), `M_{s,k}` (divisor
  exponent), and `M(S+1) = min{M(S), M^{(S+1)}}` (per-phase pivot cap) are four different objects. Assert:
  the pivot cap in the `J`-loop guard is `min{M(S), M^{(S+1)}}`, never the raw `M^{(S+1)}` and never `M(S)` alone.
- **PM-2 (two `D_0`s).** The `S=0` auxiliary `D_0 = I_{M^(1)}` (square) ≠ the `S=1` residual
  `D_0 = C^(1)` (`M^(1) × M^(2)`). Assert: the first genuine blow-up acts on `C^(1)` at `(1,0)`, not on
  an identity, and `C^(1)` is not duplicated.
- **PM-3 (Edge B vs Edge C shallow label).** Case 2 / Edge A shallow label `t^(i)=M^{(i+1)}` (raw
  width); Case 1(2) / Edge C shallow label `t^(i)=t^(i)_{s,k}` (inherited). Assert: the two are distinct
  (ledger T-E), and **no exponent is computed from the `T`-label** (exponents use `J_1, M^{(S+1)}, J` only).
- **PM-4 (diagonal truncation at rollover).** When `M^{(S+1)} < M(S)` the diagonal shrinks at Edge D.
  Assert: `diag(b)` size updates to `M(S+1) = min{M(S), M^{(S+1)}}`; coordinates with `t̃ ≥ M(S+1)` drop
  out of the terminal chain. Do not assume `diag(b)` is monotone-growing.
- **PM-5 (residual support extent).** `D_J` is rows `[J+1, M(S)]` × cols `[J+1, M^{(S+1)}]`, size
  `(M(S) − J) × (M^{(S+1)} − J)`. Assert: **row axis capped by the running-min `M(S)`**, not `M^{(S)}`,
  not `M^{(S+1)}`, not "the full next layer". (The recurring support-window / shear-support defect.)
- **PM-6 (Case-1 tie-break).** The boosted/inherited coordinate is the `u_{s,k}` with `t̃_{s,k}=J+J_1`
  that is **minimal in `T`-order** among those at the jump. Assert: the choice is `T`-minimal (paper:
  "`T_{s,k} ≤ T_{s',k'}` for `t̃_{s',k'} = J+J_1`"). Also PM-9: this uses a *comparability* the paper
  claims but which is **false in general** (T-F) — see below.
- **PM-7 (no second Schur term).** Because Q clears the pivot row before P clears the pivot column, the
  P step introduces **no further displacement** in the deep block; `D_{J+1} = δ − γβ` exactly, once.
  Assert: the deep block is updated once (by Q), not twice.
- **PM-8 (coefficient window of a fresh residual coord).** After the unit-Jacobian relabel
  `d''_{ij} → d_{ij}`, a fresh `d_{ij}` may read only the layer-`S` residual coords and the `u`'s —
  **never** cleared pivots (`E_J`) or untouched deeper layers `C^{(S+1)}, …`. Assert: the coefficient
  window is exactly (layer-`S` residual ∪ exceptional), and the relabel is unit-Jacobian.
- **PM-9 (profile totality is FALSE).** The inductive statement (p.15) claims
  `T_{s,k} ≤ T_{s',k'}` or `≥` for all pairs; this is **false** (ledger T-F; `(2,2,1,1)` has
  incomparable `(1,1,1), (2,1,0)`). Assert: no downstream step relies on totality; the `min` is over a
  **set** (needs no total order) and the `b`-chain is ordered by construction. The record carries **no
  `T` field**.
- **PM-10 (Case-2 exponent = codimension; Case-1 exponent = accumulation).** Case 2:
  `M = (M(S) − J)(M^{(S+1)} − J)` (fresh, the block codimension). Case 1: `M += J_1·(M^{(S+1)} − J)`
  (accumulate onto the fixed/inherited divisor). Assert both forms exactly; the Case-2 form has no
  `M_{s,k}` addend, the Case-1 form does. (Ledger T-C, image p.20 / pp.16-17.)
- **PM-11 (`Q^{-1}` shears only the pivot row of `C^{(S+1)}`).** The cross-layer recoordinatization
  writes exactly one row (the pivot row) of the immediately-next layer; deeper layers `C^{(S+2)}, …`
  are untouched. Assert: `Q^{-1} = I + e_1·(0, β)` modifies only row `J+1` of `C^{(S+1)}`.
- **PM-12 (`P` regular iff divisibility chain).** `P`'s entries `b'_i/b'_{J+1}` are monomials **iff**
  `b'_{J+1} | b'_i`, guaranteed by `b_1 | ⋯ | b_{M(S)}`. Assert: the divisibility chain is maintained as
  an invariant and is the discharge of `P`'s regularity (unit).
- **PM-13 (whole tail vs partial block in the `b`-update).** Edge A / Edge C: `b'_i = u·b_i` for the
  **whole** tail `i = J+1, …, M(S)`. Edge B: only the **partial** block `i = J+1, …, J+J_1`. Assert the
  two ranges are different, and the whole-tail case is driven by `u_{s,k}` (with `t̃=J+J_1`) already
  dividing every `b_i` for `i > J+J_1` (§3.3).
- **PM-14 (pivot is a blow-up unit, not a loss value).** The Schur pivot `= 1` comes from the chart
  normalisation (divide the block by the chosen centre coordinate), never from the loss. Assert: every
  Schur complement is w.r.t. a `1 × 1` **unit** pivot ⟹ every step is exact / ideal-preserving /
  unit-Jacobian, no lossy factorisation on any path.

---

## Open questions (registered, not silently resolved)

- **Q1.** The symbol `M(S+1)` is used both as the running-min value `min{M(S), M^{(S+1)}}` (the pivot
  cap in the `J`-guard, p.19/21) and, in the initialisation on p.14, as a range bound `1 ≤ k ≤ M(S+1)`.
  These are consistent only if `M(S+1)` there means the pivot cap. Reading adopted: pivot cap. Confidence
  high; flagged for the formaliser to confirm the initialisation range.
- **Q2.** The paper's `S = 0` base is left implicit ("obvious for `S=0, J=0`"). Reading adopted (§1.2,
  Codex high confidence): `M(0)=M^(1)`, `D_0 = I` at `S=0`; first blow-up at `(1,0)` on `D_0 = C^(1)`.
- **Q3.** The mapping of the charge's `δ ∈ {0,1}` (Lean `edgeδ`) to the paper mechanism (§3.3:
  `δ=1` = first/strict-transform clear, `δ=0` = later/pullback clear) is **my interpretation**; I cannot
  read the Lean. The controller should diff §3.3 against the `edgeδ` / `edgeShear` definitions. The
  *paper mechanism* itself (which coordinates each edge reads/writes) is stated unambiguously in §2 and
  is not contingent on this mapping.

## Cross-references

- Paper: `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`
  pp.14–22 (inductive statement p.15; Case 1 pp.16–18; Case 2 pp.19–21; candidates p.22).
- Worked reproduction: `theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex` §4 (structure + exponent
  bookkeeping level); ledger items T-C, T-E, T-F, N-1.
- Terminal `diag(b)` certificates (independent): `theory/aoyagi-2023-reproduction/g-coupled-334-diagb.py`,
  `g-coupled-3322-shareddepth.py`.
- This thread's verification scripts: `threads/elaboration/verify/{step_verify,trace334,tree_sim,tree_final,trace3322}.py`.
- Decorrelated consult: `threads/elaboration/codex/fold-semantics-{prompt,answer}.md`.
