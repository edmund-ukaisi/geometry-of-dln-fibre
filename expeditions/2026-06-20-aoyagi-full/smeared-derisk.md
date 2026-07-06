# General-L R1-LOWER SMEARED achiever chart — bounded-vs-wall DE-RISK

**Scout:** pen-and-paper (aoyagi-full), OBSTRUCTION-leaning (hunt the wall; report the honest verdict).
**Target:** the general-L `SmearedAchieverChart M` branch of the R1-LOWER achiever trichotomy
(`Interior ∪ Clean ∪ Smeared`, `RouteMLayerCoverGE`). The L=2 smeared atom
`routeMCore_smearedL2_square_uncond` is DONE (the `M0<M1 & r=M0` square-P₁ stratum, diag-dominance /
Varah). Question: does the L=2 argument LIFT to ∀L, or is there a genuine multi-boundary obstruction
(as with the interior, or the R1-UPPER ≥2-boundary staircase, Item 116)?
**Method:** verify-first source-read of the L=2 machinery + the trichotomy definitions; exact-algebra
(sympy) on the smallest nontrivial L≥3 smeared instances; a decorrelated Codex consult (frame-in,
hypothesis-out — Codex CLI is HEALTHY today, contra Item 111). NO heavy Lean build. Numerics guide
search only; the load-bearing claims are exact-symbolic.

---

## VERDICT: BOUNDED (no wall) — a new but elementary product-map lemma, not the R1-UPPER staircase

The general-L smeared achiever chart does **NOT** hit a research wall. The multi-boundary structure that
walls R1-UPPER (Item 116) does **not** appear in the smeared divergence: the chart is **single-pivot at
every L** (`|det Dφ| = |z|^{minAdm−1}`, rate `F = z²·U`, ONE binding axis `z`), so the divergence is a
single-axis monomial integral identical in shape to the L=2 case. There is **no additive-over-boundaries
exponent**, hence no simultaneous-rank-flag blow-up is needed.

The ONE genuinely new piece vs L=2 is a single, bounded, network-free real-matrix lemma: **the front
rank block `P₁` is a MATRIX PRODUCT at L≥3** (not a single free matrix as at L=2), and its
box-unconditional full column rank (`det(P₁ᵀP₁) ≠ 0`) must be established by a **per-factor Varah chain**
(`‖A⁽⁰⁾···A⁽ᵏ⁾ x‖ ≥ (∏ γ_j)·‖x‖`) rather than by a single Levy–Desplanques det. This composes from the
**already-banked** per-factor argmax/Varah brick (`StrictRowDominant.exists_argmax_bound`); it needs no
singular-value theory, no Cauchy–Binet, no Mathlib gap. Decorrelated Codex independently returned
**BOUNDED** with the same crux and the same wide-factor caveat (§5).

Contrast with the interior leg (Item 113, verdict BOUNDED) and R1-UPPER (Item 116, verdict WALL): the
smeared leg lands with the interior, not with R1-UPPER — for the same reason (single-axis monomial, no
staircase).

---

## 1. What "smeared" is in the trichotomy (source-verified)

The R1-LOWER achiever divergence atom (`RouteMLayerCoverGE.routeMCore_box_diverges_achiever`, the ONE
`sorry`) splits ∀M (`2 ≤ L`, `1 ≤ minAdm M`) as `Interior ∪ Clean ∪ Smeared`
(`RouteMBoundaryClass.lean`), with the achiever-path widths
`r := deepRank M = Text M (tach M) L` (rank into the deepest factor) and
`m1 := deepRows M = Wext M (L−1) = M (L−1)`:

- **`InteriorDrop M`** — some interior boundary `p ∈ [1,L−1]` drops both row & column rank (the residual
  `r_p×c_p` block nonempty). Verdict Item 113: BOUNDED (`genm-l3interior`, monomial generalization).
- **`BoundaryClean M := ¬InteriorDrop ∧ deepRank = deepRows`** (`r = m1`) — the deepest factor is exactly
  the rank block; whole-deepest radial chart. DONE general-L.
- **`BoundarySmeared M := ¬InteriorDrop ∧ deepRank < deepRows`** (`r < m1`) — the deepest factor has
  spectator rows. **This branch.** Chart: the rational single-pivot `φ_sm`, `F = z²·U`,
  `U = ‖P₁·H̄‖²`, det `|z|^{minAdm−1}` (`certificate-genM-smeared.md`, exact-validated 46/46).

Exhaustiveness `deepRank ≤ deepRows` (the `hle` hypothesis in `boundaryClean_or_boundarySmeared`)
re-verified: 0 violations over boundary M with L≤5, w≤4 (844 cases).

### The unifying structural fact (`certificate-genM-smeared.md` §1, re-reproduced)
For every smeared M: `min(M_0,…,M_{L−1}) = r = Text(L)` (the FRONT-PRODUCT bottleneck). The front product
`P := A⁽⁰⁾···A⁽ᴸ⁻²⁾` (`M_0×m1`) has generic rank `r`; `P₁ := P[:,:r]` (`M_0×r`) is its rank block, and
`P₂ := P[:, r:]` (`M_0×s`, `s = m1−r`) lies in `col(P₁)`. The rational routing
`Λ₀ := (P₁ᵀP₁)⁻¹P₁ᵀP₂` is well-defined off `{det(P₁ᵀP₁)=0}`, and `P₁·Λ₀ = P₂` exactly.

---

## 2. The L=2 atom, and WHY it does not lift verbatim (the crux)

`routeMCore_smearedL2_square_uncond` (`RouteMSmearedSquareL2.lean`) discharges two per-family analytic
facts of `routeMCore_smearedL2`, both reducing to **`det(P₁ᵀP₁) ≠ 0` box-unconditionally**:

- **Fact 1 `hcancel`** (`P₁·Λ₀ = P₂`): `col(P₂) ⊆ col(P₁)` + `P₁` invertible ⟹ the projection cancels.
- **Fact 2 `hUpos`** (`U = ‖P₁·H̄‖² > 0`): needs `P₁` full column rank.

At **L=2** the reduction `smeared_deepRank_eq_M0` (`RouteMSmearedSquareReduce.lean`) proves
`BoundarySmeared ∧ 1 ≤ minAdm ⟹ deepRank = M 0`, i.e. **`P₁` is SQUARE `M0×M0`**, AND `P₁ = A⁽⁰⁾[:,:r]`
is a **submatrix of the single FREE front factor** `A⁽⁰⁾`. So `det P₁ ≠ 0` follows from strict-row
**diagonal dominance of `A⁽⁰⁾`** (Levy–Desplanques, `Core.Matrix.DiagDominance`), pinned on a conditioned
box (`|diag| ≥ δ/2`, `|off| ≤ δ/(4(r−1))`, margin `γ = δ/4`), and the Varah `Λ₀`-entry bound (field A)
uses `A⁽⁰⁾⁻¹` on the same square free matrix. Both are box-**unconditional** (the strength needed for a
divergent boundary integral, not a.e.).

**At L≥3 this reduction fails structurally.** Exact enumeration (all smeared M) shows:

| M (example) | L | r | m0 | m1 | P₁ shape | front bottleneck layer |
|---|---|---|---|---|---|---|
| (2,3,1) | 2 | 2 | 2 | 3 | **2×2 square (free)** | 0 |
| (1,2,2,1) | 3 | 1 | 1 | 2 | 1×1 square but **product** | 0 |
| (2,3,3,1) | 3 | 2 | 2 | 3 | 2×2 square but **product** | 0 |
| **(2,1,2,1)** | 3 | 1 | 2 | 2 | **2×1 tall product** | 1 (interior) |
| (3,2,3,1) | 3 | 2 | 3 | 3 | **3×2 tall product** | 1 (interior) |
| (2,3,1,2,1) | 4 | 1 | 2 | 2 | product w/ **WIDE factor before bnl** | 2 (interior) |

Two things break the L=2 argument at L≥3, both because `P₁ = (A⁽⁰⁾···A⁽ᵏ⁾)[:,:r]` is now a **product**:
1. **Every** L≥3 smeared `P₁` is a matrix product, even the `r = m0` "square" cases — its det is a
   Cauchy–Binet sum, not a dominant-diagonal readout of one free matrix. Levy–Desplanques does not apply.
   (E.g. `(1,2,2,1)`: `det P₁ = a0_0_0·a1_0_0 + a0_0_1·a1_1_0` — a product minor sum.)
2. There exist smeared L≥3 cases with **`r < m0`** (P₁ genuinely TALL) and with the bottleneck at an
   **interior** layer — the "square reduction" `deepRank = M0` is simply false at L≥3.

So the distinction is NOT "square vs tall P₁"; it is **single free factor (L=2) vs product of factors
(L≥3)**. The L=2 diag-dominance-of-a-free-matrix mechanism cannot lift to any L≥3 smeared case.

---

## 3. Exact-algebra on the smallest nontrivial L≥3 instances

**Smallest tall-product instance: `M = (2,1,2,1)`** (L=3, r=1, minAdm=1, interior bottleneck at layer 1).
Front product `P = A⁽⁰⁾(2×1)·A⁽¹⁾(1×2)` is a rank-1 outer product; `P₁ = P[:,0]` (2×1 tall):

    P₁ = [a0_0·a1_0, a0_1·a1_0]ᵀ,   P₂ = [a0_0·a1_1, a0_1·a1_1]ᵀ,
    Λ₀ = a1_1/a1_0   (rational),    P₁·Λ₀ − P₂ = 0  (Fact 1 holds symbolically),
    U  = ‖P₁·H̄‖²  = a1_0²·(a0_0² + a0_1²)  (Fact 2; > 0 iff a1_0 ≠ 0 and (a0_0,a0_1) ≠ 0),
    det(P₁ᵀP₁) = a1_0²·(a0_0² + a0_1²).

Both facts reduce, exactly as at L=2, to **`det(P₁ᵀP₁) ≠ 0`** — but this det is now a **product-map
polynomial**, not a free-matrix det. The Gram det factors (exact, sympy) into per-"stage" pieces:

| M | `det(P₁ᵀP₁)` factored |
|---|---|
| (2,1,2,1) | `a1_0_0²` · `(a0_0_0² + a0_1_0²)` |
| (3,2,3,1) | `(a1_0_0·a1_1_1 − a1_0_1·a1_1_0)²` · `[Gram-det of the A⁽⁰⁾ 2-col block]` |
| (2,2,1,2,1) | `a2_0_0²` · `‖A⁽⁰⁾·A⁽¹⁾‖²` (couples A⁽⁰⁾,A⁽¹⁾) |
| (2,3,1,2,1) | `a2_0_0²` · `‖A⁽⁰⁾·A⁽¹⁾‖²` with A⁽⁰⁾ **WIDE** (2×3) |

The det is `(tail-from-bottleneck minor)² × (Gram-det of the head product up to the bottleneck)`. The head
is a genuine product `A⁽⁰⁾···A⁽ᵏ⁾` when the bottleneck sits at layer `k ≥ 1`, and it does NOT split into
a clean product of per-factor dets: e.g. `‖A·B‖² ≠ det(A)²·‖B‖²` (verified false). So the object to bound
is the **norm of a matrix product**, `‖P₁ x‖`, not a single determinant.

**Single-axis structure (the R1-UPPER-wall discriminator), exact for all tested L≤4 including interior
bottlenecks** — `F = z²·U` single-pivot (U is z-free and a genuine polynomial), `|det Dφ| = |z|^{minAdm−1}`
(one binding axis `z`):

    (2,1,2,1),(2,1,3,1),(3,1,2,1),(3,1,3,1),(3,1,3,2),(3,2,3,1)            [L=3 tall]
    (2,2,1,2,1),(3,2,1,3,1),(2,3,1,3,1),(2,1,2,2,1),(3,1,3,3,1)            [L=4, interior bnl]
      → all: F=z²·U single-pivot ✓, U polynomial ✓, det = z^{minAdm−1} ✓.

There is NO additive-over-boundaries exponent, NO ≥2-active-boundary staircase. This is the exact
structural feature that makes R1-UPPER a wall (Item 116) and that is ABSENT here.

---

## 4. The one new lemma, and why it is BOUNDED (not a wall)

Everything except `det(P₁ᵀP₁) ≠ 0` box-unconditionally lifts from the banked L=2/M-agnostic assembly
(`RouteMSmearedAchieverGeneral`: `SmearedAchieverChart`, `routeMCore_box_diverges_of_smearedChart`,
`hSmeared_of_smearedChart` — all sorry-free, `[propext, Classical.choice, Quot.sound]`, S2-free). The
remaining content is a single network-free real-matrix lemma:

**Rectangular Varah chain.** If each front factor `A⁽ʲ⁾` (`M_j × M_{j+1}`) has its leading
`M_{j+1}×M_{j+1}` block strictly row-diagonally-dominant with margin `γ_j > 0` on the box, then for every
`x ∈ ℝ^r`,  `‖A⁽⁰⁾···A⁽ᵏ⁾ x‖_∞ ≥ (∏_j γ_j)·‖x‖_∞`, hence `‖P₁ x‖ ≥ (∏γ_j)·‖x‖` and
`det(P₁ᵀP₁) ≥ (∏γ_j)^{2r} > 0`, box-**unconditionally**.

The single-factor step is **already banked**: `StrictRowDominant.exists_argmax_bound`
(`Core/Matrix/DiagDominance.lean`) gives `γ·|x_k| ≤ |(B x)_k|` at the argmax, i.e. `‖Bx‖_∞ ≥ γ‖x‖_∞`. The
chain is the elementary composition of this brick over the factors. No SVD, no Cauchy–Binet, no
rectangular full-rank API — all of which are Mathlib gaps — is needed.

**Numerical certificate (guide, not proof):** per-factor leading-block conditioning (margin ~1,
off-diagonal ~0.02) keeps `σ_min(P₁) ≥ 0.90` uniformly across **all 652 smeared M** (L≤5, w≤4), 0 drops
below 1e-3; the worst-case over 50 000 adversarial wide-then-tall draws stayed ≥ 0.85. Consistent with
the exact `∏γ_j` lower bound.

---

## 5. The one genuine subtlety (flagged, resolved) — WIDE factors before the bottleneck

Codex (decorrelated) and my own enumeration both flag: the naive chain "each factor square-or-tall,
restrict to top-r rows" needs the widths to be **non-increasing down to the bottleneck**. That is
**FALSE in general** — 115 smeared cases (L≤5, w≤4) have a WIDE front factor `M_j < M_{j+1}` **before**
the bottleneck (e.g. `(2,3,1,2,1)`: widths `2→3→1`, so `A⁽⁰⁾` is 2×3, expanding, before the layer-2
bottleneck of width 1).

**Resolution (verified exactly + numerically):** a wide `A⁽ʲ⁾` does NOT admit a uniform lower bound
`‖A⁽ʲ⁾ v‖ ≥ γ‖v‖` (it has a kernel), so the chain must NOT be phrased as a per-factor uniform bound.
Instead the vector entering `A⁽ʲ⁾` is **concentrated on its leading coordinates** (the previous tall/square
factor's diag-dominant leading block forces `A⁽ʲ⁺¹⁾…x` to be leading-coordinate-dominated), and `A⁽ʲ⁾`
restricted to that leading direction is bounded below by its leading-block margin; the surplus columns of
`A⁽ʲ⁾` are multiplied only by the small off-diagonals of the next factor, contributing a bounded
perturbation. For `(2,3,1,2,1)`: `det(P₁ᵀP₁) = a2_0_0²·‖A⁽⁰⁾·A⁽¹⁾‖²` with `A⁽⁰⁾` wide, and the composition
`σ_min` stayed ≥ 0.91 over 8000 draws (≥ 0.85 adversarial). **No break.** This is the one place the
formaliser must phrase the chain lemma as "the leading coordinate stays dominant through the chain" rather
than "each factor is bounded below" — a bookkeeping refinement of the lemma statement, not new
mathematics. It is the load-bearing lemma-statement subtlety to get right.

---

## 6. BOUNDED build plan (lemmas in dependency order; L=2 machinery that lifts; scale)

The M-agnostic assembly + spine wiring is DONE (`RouteMSmearedAchieverGeneral`, general `L`). The build
generalizes the opaque-width L=2 decode/chart (`RouteMSmearedDecodeL2`, `RouteMSmearedSquareL2`) from
`Fin 3` to `Fin (L+1)`. In dependency order:

1. **`Core.Matrix.RectVarahChain`** (network-free, the ONE new brick). Per-factor: extend
   `StrictRowDominant.exists_argmax_bound` to a TALL factor via its leading square block (benign — the
   extra rows only add to the norm). Then the CHAIN lemma with the leading-coordinate-dominance phrasing
   of §5 (the wide-factor-safe form): `‖A⁽⁰⁾···A⁽ᵏ⁾ x‖ ≥ (∏γ_j)‖x‖`, and its corollaries
   `det(headᵀhead) ≠ 0` and the tall-`P₁` Gram det `≠ 0`. *Est. ~150–250 lines; pure Mathlib matrix
   arithmetic; no Mathlib gap.* This is the load-bearing residual.
2. **`P₁` full-column-rank on the conditioned box** (`det(P₁ᵀP₁) ≠ 0`, general L) — from (1) applied to
   the head product; the box conditions each free factor's leading block (the general-L analogue of
   `gram_det_ne_of_diagDominant`, now for a product). *Reuses the box-shape / margin arithmetic of
   `RouteMSmearedSquareL2`.*
3. **Fact 1 `hcancel` general-L** (`P₁·Λ₀ = P₂`) — the banked `Lam0u_cancel_of_factoring` /
   `proj_cancel_of_factorsThrough` are already width-generic (they take an abstract `P₁ P₂ K`); feed them
   the general-L `P₁,P₂` + the factoring `P₂ = P₁·K` (from `col(P₂) ⊆ col(P₁)`, the front-bottleneck fact
   §1) + the Gram det from (2). *Mostly lifts; the factoring `P₂ = P₁·K` is the front-product rank fact,
   validated 46/46.*
4. **Fact 2 `hUpos` general-L** (`U = ‖P₁·H̄‖² > 0`) — from (2) full-rank; `U` polynomial + a.e.-positive
   rides the banked `MvPolynomial.ae_eval_ne_zero` route (the U-positivity is already box-unconditional
   given full rank).
5. **The opaque-width decode `packM(shearMBody(R u)) = chartL2Params…` generalized to `Fin (L+1)`** — the
   slot bijection `slotEquiv`, the front-product `P` decode, the radial `Rmap`, `ψ` MP + measurable
   embedding, the shear `−Λ₀·S_bot`. This is the heavy plumbing; it generalizes `RouteMSmearedDecodeL2`
   from one front factor to a front PRODUCT. *This is where the opaque-width cast depth lives; est. the
   bulk of the tide (several hundred lines), but it is mechanical reindex/cast, not new math.*
6. **The rate `F = z²·U` telescoping general-L** — `P·A⁽ᴸ⁻¹⁾ = z·P₁·H̄` after the `Λ₀/S_bot`
   cancellation (Fact 1); the deepest product collapses to the pure radial. Single-pivot det
   `|z|^{minAdm−1}` (block-triangular: identity front + unit-triangular rational shear + radial),
   L-independent by the block structure (§3). *Lifts from the L=2 telescoping + the det argument.*
7. **`smearedChart_of_general : BoundarySmeared M → SmearedAchieverChart M`** (`Fin (L+1)`) — assemble
   1–6 into the bundle, feeding `hSmeared_of_smearedChart` (DONE, general-L). Closes the smeared branch.

**Scale estimate.** Comparable to `genm-glinterior` (the interior general-L build, Item 114 — a
~several-hundred-to-1000-line cast-heavy multi-tide), and for the SAME reason: the opaque-width
front-PRODUCT decode + reindex plumbing dominates. The genuinely-new mathematics is the single
`RectVarahChain` brick (~150–250 lines, no Mathlib gap). No research wall.

**Sequencing (honest, for the operator).** Like the interior (Item 114), this banks a durable piece
BEHIND the walls: the general-L R1-LOWER leg = Interior (charging, Item 114) + Clean (done) + Smeared
(this, bounded) + the R1-UPPER wall (Item 116) — and the general-L headline further needs Item-109 (D1)
+ #120. So completing the smeared branch is necessary-not-sufficient for the general-L headline; it banks
the LAST un-mapped R1-LOWER piece and completes the general-L R1-LOWER labour map as bounded.

---

## 7. Most-likely-to-break-it + next step to settle the open part

- **Most likely to break it:** the wide-factor-before-bottleneck chain (§5). If the
  leading-coordinate-dominance phrasing of `RectVarahChain` cannot be made to survive a wide factor
  **exactly** (my evidence is exact on the small cases + numerics on 652), the box conditioning might
  need per-layer widths (`η_j` per factor) rather than a single `η`, and the margin arithmetic
  (`(r−1)·η + γ ≤ δ/2` at L=2) becomes an L-fold product constraint. This is still bounded arithmetic
  (the interior tide solved the analogous per-layer width bookkeeping), but it is the sharpest surface.
- **Kill-condition:** a smeared M where NO per-factor box conditioning keeps `det(P₁ᵀP₁)` bounded away
  from 0 (i.e. `σ_min(P₁) → 0` on every product box). Searched 652 cases (L≤5, w≤4) — 0 hits; the
  `∏γ_j` lower bound predicts none exist. Empty hunt ⟹ scoped evidence, not a proof; the proof is the
  exact `RectVarahChain`.
- **Next construction to settle it:** write `RectVarahChain` as an exact lemma (the tall-factor argmax
  extension + the wide-factor leading-dominance chain) and check it against the `(2,3,1,2,1)` Gram
  factorization symbolically — the one instance that exercises BOTH a wide factor and an interior
  bottleneck. That is the decisive test before committing the opaque-width decode tide.

---

## Appendix — reproduction

- `expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/scripts/pp_smear_GATE.py` — the banked
  design gate (`F=z²·U`, det `z^{minAdm−1}`, threshold `½·minAdm`), 46/46, reproduced this pass.
- Smeared enumeration + P₁-shape classification, the Gram-det factorizations, the single-pivot check on
  L=4 interior-bottleneck cases, and the `σ_min(P₁)` per-factor-conditioning numerics (652 cases + the
  wide-factor adversarial draws): the sympy/numpy snippets in this thread's transcript (all off
  `witness_tide_validated.achiever` — the same achiever-path model the cert gate uses).
- Decorrelated Codex (`gpt-5-codex`, medium; frame-in / hypothesis-out): VERDICT **BOUNDED**; independently
  named the "Rectangular Varah Chain" as the minimal lemma, flagged the tall-factor step as benign and the
  wide-factor-before-bottleneck as the one thing to flag (§5), and confirmed single-axis ⟹ no staircase
  wall.
