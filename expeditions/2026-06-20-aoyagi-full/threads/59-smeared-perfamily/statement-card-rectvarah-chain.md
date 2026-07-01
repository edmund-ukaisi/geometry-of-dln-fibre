# Statement card — RectVarahChain (the L≥3 smeared rank-block nondegeneracy brick)

**File:** `lean/DLNFibre/Core/Matrix/RectVarahChain.lean` (Core engine, Mathlib-only imports).
**Status:** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]` (NO sorryAx, NO
`monomial_rlct`) on all 7 delivered results. Built via `scripts/lb DLNFibre.Core.Matrix.RectVarahChain`.
**Seat:** lean-formaliser (genm-smearbuild). **Date:** 2026-07-01.

## What it proves (name = content)

The RECTANGULAR Varah chain: `det(P₁ᵀP₁) ≠ 0` for a front PRODUCT `P₁ = (A⁰·A¹···Aᵏ)[:, :r]`
(`M₀ × r`, rectangular at `L ≥ 3`), UNCONDITIONALLY on a conditioned box — the rank-block
nondegeneracy the boundary-SMEARED achiever chart's `hUpos`/`Uy > 0` field consumes at `L ≥ 3`. At
`L = 2` the front product is a SINGLE (square) factor and `StrictRowDominant.det_ne_zero` closes it
(`RouteMSmearedSquareL2`); the product case is the one genuinely-new brick genm-smeared flagged.

Route (Codex-recommended map-first, decorrelated consult fired + healthy):
1. `gram_det_ne_of_mulVec_injective` — the PosDef endgame: `Function.Injective A.mulVec ⟹ det(AᵀA) ≠ 0`
   via `Matrix.PosDef.conjTranspose_mul_self` (over ℝ, `Aᴴ = Aᵀ` by `conjTranspose_eq_transpose_of_trivial`)
   + `PosDef.isUnit` + `isUnit_iff_isUnit_det`. Reusable, ~6 lines. (Needs `Data.Real.StarOrdered` for
   `StarOrderedRing ℝ`.)
2. `FactorDominant hrn hrm A d η` (structure) + `factorDominant_of_box` — per-factor leading-block
   strict row diagonal dominance: leading diagonal `≥ d/2`, every off-block/trailing entry `≤ η`,
   margin `(2m−1)η ≤ d/2`, `d > 0`. `factorDominant_of_box` is the box-membership readoff (diagonal in
   `[δ/2,δ]`, rest in `[−η,η]`) — the `L=2` `P1u_diag_ge_of_mem`/`P1u_offdiag_le_of_mem` shape, per
   factor.
3. `factorStep` — the propagation: a `LeadCert hrm w V` (leading coord attains the global max value `V`)
   maps under a `FactorDominant` factor to `LeadCert hrn (A*ᵥw) W` with `γ·V ≤ W`, `γ = d/2−(m−1)η > 0`.
   The margin forces trailing rows `≤ mηV ≤ γV`, so the argmax STAYS in the leading block ("leading
   coordinate stays dominant through the chain").
4. `leadCert_embed` — the base: a zero-padded `x : Fin r → ℝ` embeds with `LeadCert`, value `> 0` iff
   `x ≠ 0`.
5. `mulVec_injective_of_leadCert` / `frontGram_det_ne_of_leadCert` — the terminal: a positive-value
   `LeadCert` on every nonzero input ⟹ `P.mulVec` injective ⟹ `det(P₁ᵀP₁) ≠ 0`.

## VERIFY-FIRST (the decisive pre-tide test — PASSED)

`frontGram_det_ne_231`: the chain closes end-to-end on **M=(2,3,1,2,1)** — the one case with BOTH a
wide front factor (A¹ has 3 rows) and an interior bottleneck (the width-1 passthrough `= r=1`). Shapes
`2×3`, `3×1`, `1×2`; `P₁ = (A⁰A¹A²)[:, :1]`. Threads `leadCert_embed` → `factorStep ×3` →
`frontGram_det_ne_of_leadCert`, axiom-clean. This mirrors exactly what the opaque-width plumbing does
per factor. Numerically pre-validated (Monte-Carlo, 0 failures) for r=1,2,3,4 with the derived margin
`(2m−1)η ≤ d/2`.

## Fidelity / scope (caveats next to the claim)

- The brick is NETWORK-FREE pure linear algebra. It does not mention `routeMCore`, `frontProd`, or the
  chart — it is the reusable nondegeneracy engine. The smeared chart's `hUpos` (= `Uy = ‖P₁H̄‖² > 0`)
  reduces to `det(P₁ᵀP₁) ≠ 0` (P₁ full column rank ⟹ `‖P₁ v‖² > 0`), which is this brick.
- `factorStep` returns SOME value `W ≥ γ·V` (the actual leading max), not literally `γ·V` — `LeadCert`'s
  "value = the realized max" contract requires this; positivity threads because each `γⱼ > 0`.
- `leadCert_embed` needs `[Nonempty (Fin r)]` (i.e. `r ≥ 1` — always true in `BoundarySmeared`,
  `deepRank ≥ 1`).

## Interface for the plumbing (what the opaque-width chart consumes)

Per front factor `A⁽ʲ⁾` (from box coords): `factorDominant_of_box (r ≤ n_j) (r ≤ n_{j+1}) A⁽ʲ⁾ δ η …`
→ `FactorDominant`. Then `hcert x hx` is built by `leadCert_embed` (base) threaded through one
`factorStep` per factor (each scaling the value by `γⱼ > 0`), and `frontGram_det_ne_of_leadCert
(frontProd M) (r ≤ M₀) hcert` gives `det(P₁ᵀP₁) ≠ 0`.

## BLOCKER for the full per-family chart (honest boundary)

The opaque-width `SmearedAchieverChart M` construction ALSO needs the general-L **`frontProd M`
decode** — the bridge expressing `routeMCore M (ψ(R(insertNth p z y))) = z²·‖P₁·H̄‖²` (the peeled rate
`hRate`) at opaque widths, i.e. the general-L deepest-product telescoping `A_{L-1}·(front product)`.
That bridge does NOT exist yet (`RouteMSmearedGenRate`'s docstring: "`P = frontProd M` via … a
SEPARATE, still-to-build bridge"); `P1u`/`P2u`/the smeared decode are `Fin 3`-pinned
(`RouteMSmearedDecodeL2`). The general-L chain substrate (`chainOfMt`/`GenBlk`/`Wext`/`Text`,
`RouteMGenChain`) is genm-glift's in-flight interior work. So the full chart is blocked on general-L
`frontProd M` + the smeared decode lift — NOT on the nondegeneracy math (this brick), which is banked.

## Wiring instruction (aggregator is single-writer — controller wires)

Add `import DLNFibre.Core.Matrix.RectVarahChain` to `lean/DLNFibre.lean` near the other `Core.Matrix.*`
bricks (it only imports Mathlib — no ordering constraint beyond Core-before-DLN). Optionally add
`frontGram_det_ne_of_leadCert` + `frontGram_det_ne_231` to `AxCheck.lean` (they carry `#print axioms`
in-file already).
