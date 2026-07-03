# genm-b3closer — b3 (exact joint-differential rank) LANDED + hrank₂ DISCHARGED

Charged to build **b3** (the exact middle-stratum `rank(jacFlatL2)`, the sole remaining core-geometry
content of the L=2 D1 `≥`-leg per the b1closer runway) and finish LEAF 2. This hand **landed b3 AND
discharged `hrank₂`** (b3 wired into a two-peel producer), then reduced LEAF 2 to exactly the two
remaining ANALYTIC gates `hRne` + `hInterface` (not core-geometry). All sorry-free, axiom-clean
`[propext, Classical.choice, Quot.sound]` (forced `#print axioms`, no `sorryAx`, no new axiom).

Branch `origin/genm-b3closer` @ `51e8ff76` (from `origin/genm-b1closer` @ `ebfa58af`). Four new
modules; all green in their import-closure; no name clashes with siblings.

## What LANDED (all sorry-free, axiom-clean)

### b3 — the EXACT joint-differential rank (`D1JointDiffRankExact.lean`)
**Cleaner than the b3 target as stated: UNCONDITIONAL in the two layer ranks** (no middle-stratum
hypothesis; the value only reads `rank(v⁰)`, `rank(v¹)`):

    finrank_range_jointDiffL2_eq :
      finrank ℝ (range (jointDiffL2 H v)) = H0·rank(v¹) + rank(v⁰)·H2 − rank(v⁰)·rank(v¹)
    jacFlatL2_rank_eq :
      (jacFlatL2 H v).rank = H0·rank(v¹) + rank(v⁰)·H2 − rank(v⁰)·rank(v¹)

Route: inclusion–exclusion `finrank(R ⊔ C) = finrank R + finrank C − finrank(R ⊓ C)` on the two
single-argument ranges, where each finrank is computed via an **injective map into a matrix space**
(uniform pattern): `R = range(δ⁰ ↦ δ⁰·v¹) = range(Y ↦ Y·W1)` (factor `v¹=U1·W1`, `Y↦Y·W1` injective
via `W1` right-inverse) → `finrank R = H0·rank(v¹)`; dually `finrank C = rank(v⁰)·H2`; the
intersection `R ⊓ C = range(T ↦ U0·T·W1)` (sandwich map, injective) → `finrank = rank(v⁰)·rank(v¹)`.
`range(jointDiffL2) = R ⊔ C` via `Submodule.mem_sup` + a `paramsOfLayers` reconstruction. Uses the
banked `exists_rank_factorization` (generalized to arbitrary rectangular matrices via
`exists_rank_factorization_gen`, instantiating at `H = ![p,q,q]`) + the banked one-sided inverses.
This reconciles with the b1closer numeric certificate: with `rank(v⁰)=r+a`, `rank(v¹)=r+b`,
`jacFlatL2.rank − nReg = extraCountRect(H0−r,H2−r,a,b)` (d1gates, 0 fails).

### Sylvester's rank inequality (`D1JointDiffRankExact.lean`)
    rank_add_rank_le_rank_mul_add_middle : A.rank + B.rank ≤ (A*B).rank + m   (m = middle dim)
via `finrank_range_add_le_finrank_range_comp_add` (linear-map form, rank–nullity on the restriction
of `toLin A` to `range (toLin B)`). Needed to discharge the gate constraint `a + b ≤ H1 − r`.

### The hrank₂ COUNT above b3 (`D1RectHrankClose.lean`)
    jacFlatL2_rank_sub_nReg_eq_extraCountRect :
      (jacFlatL2 H v).rank − nRegL2 H r = extraCountRect (H0−r) (H2−r) (frontRise) (backRise)
at an optimal `v`, with `frontRise = rank(v⁰)−r`, `backRise = rank(v¹)−r`. b3 + Sylvester +
layer-rank bounds (`r ≤ rank(v⁰)`, `r ≤ rank(v¹)` from `rank(v⁰·v¹)=r`, width bounds) make the honest
ℕ subtraction go through (substitute `Hᵢ = r + rise + slack`, all subtractions honest, then `ring`).

### hrank₂ DISCHARGED — the two-peel producer with b3 wired in (`D1RectTwoPeelClosed.lean`)
    d1ge_L2_rect_two_peel_hrank_closed :  … → rlctAt deepest ≤ rlctAt v
Re-threads the FIRST peel through `residJacobian_rank_eq` (the DERIVATIVE-exposing producer, which
carries the residual-Jacobian rank of ITS OWN `q`), so the `∀-q` `hrank₂` gate of the base producer
`d1ge_L2_rect_two_peel` is **no longer a hypothesis** — it is derived internally from
`residJacobian_rank_eq` (`rank(jacResid q(0,·) t0) = jacFlatL2.rank − nReg`) + the b3 count. The
`(a,b)` rises are FIXED to `(frontRise, backRise)`; the honest constraints `ha`/`hab`/`hb` derived
in-file. **This closes the key finding: the base `hrank₂` gate is `∀ q` and NOT dischargeable for an
arbitrary `q` — the rank is specific to the constructed `q`, so the producer MUST bind `q` from the
derivative-exposing peel. Solved by inlining.** Still consumes `hRne` + `hInterface`.

### The ∀-v LEAF-2 reduction (`D1RectHeadlineWire.lean`)
    hD1ge_L2_rect_of_gates :
      … → ∀ v ∈ optimalSet H B, rlctAt deepest ≤ rlctAt v
The headline LEAF-2 shape closes given the v-INDEPENDENT `hDeepest` (banked #44 at the
`deepestPoint`) + the two per-`v` analytic gates `hRne` / `hInterface`. `hrank₂` closed internally.
Makes the LEAF-2 residual precise.

## The PRECISE remaining runway to close LEAF 2 (`HeadlineL2Assembly.lean:107`)

`hrank₂` (the sole core-geometry gate) is CLOSED. The remaining debt is exactly the TWO ANALYTIC
gates + the mechanical final plug — NONE are core-geometry:

1. **`hRne`** (slice non-vanishing) — `∑ q(0,z)² ≠ 0` a.e. near `t0` for the constructed first-peel
   `q`. Analogous to the banked `dlnLoss_deepest_core_ae_ne_zero` (deepest MODEL core) but for the
   chart-transported residual at a GENERAL `v`; a genuine analytic build (the residual→model
   non-vanishing connection at general `v`), NOT b3.
2. **`hInterface`** (R1 degraded core) — identify the constructed RECTANGULAR second-peel residual
   `q₂` with the `M'`-core RLCT `ofReal(lambdaCore (MprimeRect (H−r) frontRise backRise))`. R1's VALUE
   is banked (`r1_resolution_general` / `r1_resolution_interface_L2_generic`); the OPEN part is that
   the built `q₂` IS the `M'`-core — a genuine analytic identification, NOT b3.
3. **The final plug** into `HeadlineL2Assembly.lean:107` — instantiate `hD1ge_L2_rect_of_gates` at
   the front-pivoted `B'` with `hDeepest` from `deepest_regular_core_normal_form_L2_front` (already
   used in Step C), and supply gates 1+2. Mechanical once 1+2 land.

## Build status
`D1JointDiffRankExact`, `D1RectHrankClose`, `D1RectTwoPeelClosed`, `D1RectHeadlineWire` all green in
import-closure; the topmost (`D1RectHeadlineWire`) pulls all four in and builds exit-0. NOT yet wired
into the aggregator (`DLNFibre.lean` single-writer) or `AxCheck` — controller wiring: add
`import DLNFibre.DLN.RLCT.Validate.D1RectHeadlineWire` at the end of `DLNFibre.lean`, and (optionally)
`#print axioms jacFlatL2_rank_eq` + `d1ge_L2_rect_two_peel_hrank_closed` to `AxCheck.lean`.

## Pointer for the next hand
Core-geometry is DONE (b3 + `hrank₂`). LEAF 2's remaining debt is purely the two analytic gates
`hRne` (slice non-vanishing at general `v`) + `hInterface` (R1 degraded-core identification of the
rectangular second-peel residual). Both are distinct analytic builds from b3; `hD1ge_L2_rect_of_gates`
+ `d1ge_L2_rect_two_peel_hrank_closed` make the exact shape they must produce explicit.
