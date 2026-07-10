# Vertical slice — `(3,3,3,4)` corank-2 composed `(S,J)` blow-up recursion, END-TO-END

**Seat:** pen-and-paper (witness). **Direction:** exhibit the composed machine on one realizable
instance, correct + Lean-friendly. **Date:** 2026-07-09/10. **NO Lean** (certificate for the formaliser).
**Decorrelated check:** one `local-codex-consult` (xhigh), my accounting withheld — it independently
reproduced the construction term-for-term and corrected one modelling error of mine (see §7).

**Artefacts (this dir):** `vslice_verify.py` (Schur split + depth reduction + corank-2→1 crux, sympy
exact), `vslice_accounting.py` (minAdm + terminal-exponent lattice), `vslice_corner.py` (the corner
blow-up: min-vs-sum, symbolic threshold `7/2` + numeric abscissa corroboration), `codex-{prompt,answer}.md`.

---

## VERDICT

The composed machine runs END-TO-END on `(3,3,3,4)` corank-2 with **no new obstruction beyond the one
already-named bounded brick** (the relative corank-step invariant / the shared-support closure, §8). Every
step is an exact identity or a measure-preserving change of variables I have verified symbolically; the
exponent accounting sums to `minAdm(3,3,3,4) = 7`, giving the finiteness certificate

> `routeMLayerBoxIntegral (3,3,3,4) c′ 1 < ⊤`  for every `c′ < 7/2 = ½·minAdm(3,3,3,4)`.

**Level discipline (precision.md).** This certifies **FINITENESS** = `rlct ≥ ½·minAdm` (the R1-UPPER
direction: the resolution exhibits convergence). It does **not** on its own assert `rlct = 7/2` — the
matching upper bound `rlct ≤ ½·codim` is the separately-cited Watanabe/Aoyagi interface. The geometric
input (`codim = minAdm = 7`) is banked (`minAdmRec_eq_minAdm`).

**The single load-bearing surprise the composed run shook out** (relative to the per-chart probes): the
correct local model at the binding corner is a **SUM** `u₀²·U₀ + u₁²·U₁` of two order-2 radial terms, NOT
a product `(u₀u₁)²`. The corner blow-up then accumulates the two Jacobian powers (`3+2+1 = 6`) onto ONE
terminal divisor while the loss stays order `2`, giving threshold `7/2`. My first accounting toy used the
product form and got the wrong `7/4`; the sum form is the truth (§4, Codex-confirmed). This is the exact
resolution of the min-vs-sum wall (`r1upper-derisk.md`) for this slice.

---

## 0. Objects and the target

Widths `M = (M₀,M₁,M₂,M₃) = (3,3,3,4)`, depth `L = 3`. Layers
`A₀ : 3×3`, `A₁ : 3×3`, `A₂ : 3×4`, box `= {all entries ∈ [−1,1]}`. Loss `F = frobSq(A₀·A₁·A₂)`
(squared Frobenius of the `3×4` product). Target: `∫_box F^{−c′} < ⊤` for `c′ < 7/2`.

`minAdm(3,3,3,4) = 7`, binding boundary-0 cut `t₁ = 1` (corank block `(3−1)×(3−1) = 2×2`), whose branch
`T = (1,0,0)` has per-boundary charges `[4, 3, 0]` (Σ = 7). *(Verified `vslice_verify.py`: the recursion
`minAdm(3,3,3,4)=min_t (3−t)²+minAdm(t,3,4)` gives `9,7,7,8` at `t=0,1,2,3`; min `7` at `t∈{1,2}`.)*
`t₁=1` is the corank-2 branch — the reason this slice is the smallest chain where the corank-2 coupling
bites through a **shared deep factor** `A₂` (`t₁=2` is corank-1; `(3,3,4)` at `L=2` has the corank-2 block
but no shared deep layer — `verify-r1-diagb-334.md`).

`T=(1,0,0)` is **a** minimiser, not unique: `T=(2,0,0)` and `T=(2,1,0)` also sum to 7 (Codex flagged this;
correct — they are the corank-1 companions). The slice targets the corank-2 branch deliberately.

---

## 1. STEP 1 — front-split (banked, CLOSED)

`routeMLayerBoxIntegral_front_split` (proved clean-three in `RouteMSJResolution.lean`):

    ∫_box frobSq(A₀A₁A₂)^{−c′}
      = ∫_{A′∈box(tailChain M)} ∫_{A₀∈matBox 3 3 1} frobSq( A₀ · prod(tailChain M) A′ )^{−c′}

with `tailChain M = (3,3,4)`, `prod(tailChain M) A′ = A₁·A₂ =: Q` (a `3×4` matrix). Peels the leftmost
layer; measure-preserving (`eFront = piFinSuccAbove 0`, `frobSq_prod_front`). **Coordinate map:**
`A ↦ (A₀, (A₁,A₂))`, Jacobian `det = 1`. **Ledger state:** `S=0, J=0`; `D₀ = A₀A₁A₂` (`3×4`); `b = (1,1,1)`.

---

## 2. STEP 2 — pivot-chart cover of the front factor `A₀` (banked, CLOSED)

`{A₀ = 0}` (rank 0) is `volume`-null, so `matBox` `=ᵐ {1 ≤ rank A₀}`, and
`pivotLocus_eq_iUnion 1 : {1 ≤ rank A₀} = ⋃_{ρ,κ} pivotChart ρ κ` (row/col pivot selections
`ρ,κ : Fin 1 ↪ Fin 3`). `pivotChartCover_matBox_le_sum` gives the sub-additive cover

    inner A₀-integral  ≤  Σ_{ρ,κ}  ∫_{A₀ ∈ matBox ∩ pivotChart ρ κ}  frobSq(A₀ Q)^{−c′}.

The `9` charts `(ρ,κ)` are symmetric (row/col permutations of the box), so it suffices to bound one, at the
top-left pivot. **This is `sjBoundaryPeel` — the CLOSED-in-principle cover plumbing** (constant `1`; the
sorry is the multi-hundred-line block-reindex, not new math). **Ledger:** on chart `(ρ,κ)` the `t=1` pivot
is cleared → `S=1, J=1`; `D₁` = the `2×3` residual block; `b` still `(1,1,1)` (no exceptional coord yet).

---

## 3. STEP 3 — the Schur block split (banked EXACT `frobSq_schur_block_split`)

On the top-left `t=1` chart write `A₀ = [[a, B],[C, D]]` — `a` the `1×1` pivot (a unit on this chart:
`a ≠ 0`), `B` `1×2`, `C` `2×1`, `D` `2×2` — and split `Q = [[Q_p],[Q_b]]`, `Q_p` `1×4`, `Q_b` `2×4`. Then
**exactly** (verified `vslice_verify.py`, `sp.simplify(LHS−RHS)==0`):

    frobSq(A₀ Q) = frobSq(a·Q̃_p) + frobSq(C·Q̃_p + Γ·Q_b),
      Q̃_p = Q_p + a⁻¹ B Q_b   (1×4),      Γ = D − C a⁻¹ B   (2×2 Schur complement).

### COMPASS #1 — the pivot inverse `a⁻¹`, natively re-expressed

`a⁻¹` appears in `Q̃_p` and `Γ`. **It never becomes a Jacobian determinant.** Two measure-preserving shears
absorb it (`vslice_verify.py`, both Jacobians `= 1`):

- **`D ↦ Γ = D − C a⁻¹ B`** — an affine translation of the four `D`-entries (`a,B,C` held as coordinates);
  Jacobian `det = 1` (banked `measurePreserving_shearSub`). Domain: `Γ` in the translated box `box − Ca⁻¹B`.
- **`A₁ ↦ A₁^♯ = U·A₁`, `U = [[1, a⁻¹B],[0, I₂]]`** (unipotent `3×3`, `det = 1`) — this realises the row
  shear `Q_p ↦ Q̃_p` on the tail: `U·Q = U·A₁·A₂ = (U A₁)·A₂`, so it is a left-mult of `A₁`'s three
  columns by a `det-1` matrix ⟹ Jacobian `(det U)³ = 1`. Domain: a sheared box `U(box)`.

The full change of variables `(a,B,C,D,A₁) ↦ (a,B,C,Γ,A₁^♯)` is **block-triangular**, so no hidden
determinant factor appears. **This is the route-uniqueness compass in action:** the map "grows a det-inverse"
at the Schur step, and the native re-expression (unit pivot-chart + `det-1` shears) has existed, exactly as
the charter predicts. A genuine det-inverse would appear only if one normalised by a *non-unit* pivot or used
an inverse frame as a coordinate — neither is done. **Ledger:** `b` still `(1,1,1)`; the residual block is now
`Γ` (`2×2`) coupled to `Q_b`.

---

## 4. STEP 4 — depth reduction + the corank-2 resolution (the coupled core)

### 4a. Depth reduction to a lower-depth core (verified EXACT)

Writing `A₁^♯ = [[v],[W]]` (`v = row 1`, `1×3`; `W = rows 2,3`, `2×3`), the split of §3 becomes
(`vslice_verify.py`, `sp.simplify(...)==0`):

    F  =  a²·frobSq(v A₂)  +  frobSq( (C v + Γ W)·A₂ )  =  frobSq( H · A₂ ),
      H = [[ a·v ],[ C·v + Γ·W ]]   (3×3).

So peeling `A₀` drops the depth `3 → 2`: `F = frobSq(H·A₂)`, a `(·,3,4)`-shaped core whose front factor `H`
carries the accumulated layer-1 data. **This is the "fresh depth-`(L−1)` core" of Aoyagi's streamlined
depth recursion** (`aoyagi-2023-worked.tex §ssec:candidates`), with the coupling made explicit: `H` is a
*constrained* `3×3` (parametrised by `a, v, C, Γ, W`), not free — that constraint is the diag(b) content.
The exact factorisation is `H = [[1,0],[C/a, I₂]] · [[a v],[Γ W]]` (verify: the product's bottom block is
`(C/a)(av) + ΓW = Cv + ΓW`). Dropping the left `det-1` unit `[[1,0],[C/a, I]]` (bounded-invertible generator
recombination, RLCT-safe; for the *measure* it is a `det-1` shear on the output rows — it removes the `Cv`
cross-term) gives the clean model

    G  ≃  a²·frobSq(v A₂)  +  frobSq( Γ·W·A₂ ).                    (★)

The `a²` prefactor on the first summand is the **pivot / α-divisor** — kept explicit here (it is *non-binding*,
§6: threshold `≥ ½·Mval(0,0,0) = 9/2`, and near `a→0` it is dominated by the second summand on the generic
chart, so it never lowers the value). The two summands **share the deep factor `A₂`** — this is the L≥3
novelty absent from `(3,3,4)`.

### 4b. Corank-2 block → radial + corank-1 (verified EXACT)

Blow up the `2×2` corank block radially, `Γ = u₀·Γ̂`, `Γ̂ = [[1,β],[γ, γβ+δ]]` (top-left normalised to a
unit). **Jacobian** `dΓ = |u₀|^{4−1} du₀ dβ dγ dδ = |u₀|³ (…)` (block dim `4`, radial power `3`). Then
`frobSq(Γ W A₂) = u₀²·frobSq(Γ̂ W A₂)` (single radial factors cleanly — verified). Unit-triangular clear
(`det L = det R = 1`, functions of `Γ̂` only, `Z`-independent):

    [[1,0],[−γ,1]] · Γ̂ · [[1,−β],[0,1]] = [[1,0],[0,δ]],   δ = (γβ+δ) − γβ  (the Schur scalar).

Absorb `R = [[1,−β],[0,1]]` into `W` (`det 1`, deeper `A₂` untouched — the "renaming into the next factor").
With `W = [[w₁],[w₂]]` this yields (verified, `vslice_verify.py` morse split):

    G  ≃  frobSq(v A₂)  +  u₀²·( frobSq(w₁ A₂) + δ²·frobSq(w₂ A₂) ).

**COMPASS #2:** the unit-clear divides by `Γ̂`'s top-left entry — but on the radial chart that entry is
normalised to `1`, so the division is by a unit, no det-inverse. **Ledger** (`S=1→2`): `b` accumulates `u₀`
on the two corank rows; residual is the corank-1 scalar `δ` coupled to `w₂ A₂`, plus a fresh pivot row
`w₁ A₂` and the passed-through row `v A₂`.

The corank-2 step has **reduced to corank-1** coupling (`δ²·frobSq(w₂ A₂)`) — the already-closed shape of
the `(·)`-recursion. corank-2 and L≥3 coupling are independent novelties that compose (`chart-lemma-probe.md`
verdict, here instantiated end-to-end).

### 4c. Boundary-1 peel (charge 3) + the shared factor as passive prefactor

The passed-through row `v A₂` is the boundary-1 residual (a `(1,3,4)` sub-core, `minAdm(1,3,4)=3`). Blow up
`v = u₁·v̄` (`v ∈ ℝ³`): Jacobian `dv = |u₁|^{3−1} du₁ dv̄ = |u₁|²(…)`, and `frobSq(v A₂) = u₁²·frobSq(v̄ A₂)`.
The layer-1 exceptional `u₀` is a **passive monomial prefactor** on the layer-2 term: a later chart map `φ`
on the downstream acts as `φ*(u₀²·G_down) = u₀²·φ*(G_down)` (`chart-lemma-probe.md`, verified `sjj_sequential`).
**Boundary 2** has `t=0`, charge `(0−0)(4−0) = 0`: on the generic-`A₂` chart `A₂` supplies bounded-below
row coefficients (units), no new divisor; the rank-deficient-`A₂` locus is a *different* rank-profile
stratum (other branch, §6). **Ledger** (`S=2→3, done`): terminal monomials `b_corank = u₀`, `b_pivot = u₁`,
loss `≃ u₁²·U + u₀²·(U′ + δ²·U″)` with `U,U′,U″ > 0` units on the generic-downstream chart.

---

## 5. THE CRUX — min-vs-sum, resolved (§4 corner; verified `vslice_corner.py`)

After 4b–4c the binding local model is (Codex-confirmed, my product-form toy corrected). Radial `u₀` from
the `Γ` block (§4b) and radial `u₁` from the boundary-1 row `v = u₁v̄` (§4c) give
`G ≃ a²u₁²·‖v̄A₂‖² + u₀²·(‖w₁A₂‖² + δ²‖w₂A₂‖²)`, which is of the shape

    G  ≃  u₀²·U₀ + u₁²·U₁,     U₀,U₁ > 0 units,     measure  |u₀|³|u₁|² du₀ du₁ ,

with `U₀ = ‖w₁A₂‖² + δ²‖w₂A₂‖²`, `U₁ = a²‖v̄A₂‖²`. (The `a²` rides inside `U₁`; near `a→0` the corner-chart
unit `U₀ + τ²U₁` stays bounded below by `U₀ = ‖w₁A₂‖² > 0` on the generic-`A₂` chart, so the α-direction
does not bind — consistent with §4a.)

- **Naive (independent divisors):** `{u₀=0}` gives `3−2c′ > −1 ⇔ c′ < 4/2 = 2`; `{u₁=0}` gives
  `2−2c′ > −1 ⇔ c′ < 3/2`. `min(2, 3/2) = 3/2` — **the undershoot** (`r1upper-derisk.md`; the two-matrix
  engine caps at the min boundary). This is WRONG: it is not the resolved chart.
- **The binding zero is the CORNER `u₀=u₁=0`.** Blow it up (`u₁ = u₀·τ`, `du₁ = u₀ dτ`):

      measure  |u₀|³|u₁|²du₀du₁ = |u₀|³·|u₀τ|²·|u₀| du₀dτ = |u₀|⁶·|τ|² du₀dτ ,
      G = u₀²·(U₀ + τ²U₁)   (loss order **2** in u₀, unit `U₀+τ²U₁ > 0`).

  Terminal divisor `u₀`: **Jacobian power `6 = Mval−1`, loss order `2`, threshold `(6+1)/2 = 7/2`**. The
  `τ`-integral over `[0,1]` is a finite constant (`U₀ > 0`). The complementary chart `u₀ = u₁σ` is symmetric
  (`vslice_corner.py`: measure `|u₁|⁶|σ|³`, threshold `7/2`, `σ`-integral finite via `U₁ > 0`).

**The Jacobian powers ADD (`3 + 2 + 1 = 6`) while the loss order stays `2`** — because the model is a SUM
of two order-2 radial terms whose common zero is the corner, not a product. Symbolically
`∫ u₀^{6−2c′} du₀` is finite iff `c′ < 7/2`; numerically `I(c′) = ∫∫_{[0,1]²}(u₀²+u₁²)^{−c′}u₀³u₁² ` stays
small for `c′ < 3.5` and explodes (`c′=4.0 → 1.4·10¹⁸`) past it — abscissa exactly `7/2`.

**Role of the shared `A₂`:** it keeps the two summands `‖v A₂‖²` and `‖ΓW A₂‖²` in one product ideal, so
their zero loci meet at the SAME corner (codim `4+3 = 7`), and the codimensions ADD on the terminal divisor
— rather than producing two independent divisors (which would compete → min). *(Caveat, honest: the crude
scalar caricature `z²(x²+y²)` — sharing a 1-dim `z` — has RLCT `½` < the disjoint `1`, i.e. crude sharing
*collapses*. The DLN model does NOT collapse because the units `U₀,U₁` stay bounded below on the
generic-`A₂` chart; only `A₂`-rank-drop lowers them, and that is a separate, higher-`Mval` branch. The
"units stay bounded below across the shared-support charts" is precisely the named brick, §8.)*

---

## 6. Exponent accounting → `7`, and the closure over all branches

**Per-branch:** each rank-profile branch `t` yields a terminal divisor of threshold `½·Mval(t)`, where
`Mval(t) = (M₀−t₁)(M₁−t₁) + Σ_{j≥2}(t_{j−1}−t_j)(M_{j+1}−t_j)` = Σ of per-boundary charges (banked
`Mval_decompose` / `sjChargeUpdate_accum`; the additive decomposition
`Mval(M,T) = (M₀−T₀)(M₁−T₀) + Mval(redChain T₀ M, tail T)`). For the binding branch
`Mval((3,3,3,4),(1,0,0)) = 4 + 3 + 0 = 7`, threshold `7/2`.

**Closure (exhaustiveness — required, not optional).** Finiteness at `c′ < 7/2` needs EVERY terminal
divisor on EVERY chart `≥ 7/2`, i.e. `min_t Mval(t) = minAdm = 7`. Banked:
`sjChargeBudget_le : minAdm M ≤ (M₀−t)(M₁−t) + minAdm(redChain t M)` for all admissible `t`, and
`minAdmRec_eq_minAdm`. So no branch undershoots. *(Verified `vslice_accounting.py`: the admissible-profile
lattice min is `7`.)* The `α`/pivot direction and the recursive sub-cores are `≥ ½·minAdm` by the same
inequality (`aoyagi-2023-worked.tex §ssec:candidates` structural lower bound; `α ≥ ½Mval(0,0,0)=9/2`).

**Endpoint (banked).** On each chart the fully-resolved `G = (unit)·∏ b_i²` is normal-crossing;
`monomialIntegrand_integrable_of_lt` / `Case222Cover` close `∫ ∏|u|^{h−2c′}·unit^{−c′} < ⊤ ⇔ h−2c′ > −1`
coordinatewise, i.e. `c′ < min_divisor (h+1)/2 = 7/2`. Base `L=1`: `sjBase1_freeMatrix`.

---

## 7. The composed machine as a Lean-friendly pipeline (what feeds `sjJointResolution`)

    front-split (CLOSED)                          §1  routeMLayerBoxIntegral_front_split
      → pivot-chart cover (CLOSED)                §2  pivotChartCover_matBox_le_sum   [= sjBoundaryPeel plumbing]
        → Schur block split (BANKED EXACT)        §3  frobSq_schur_block_split
          → shear D↦Γ, A₁↦UA₁ (BANKED MP)         §3  measurePreserving_shearSub  [COMPASS #1]
            → radial u₀ of the 2×2 corank block   §4b radial_morse_residual_power_le   (Jac u₀³)
              → unit-clear Γ̂→diag(1,δ), absorb R  §4b (det-1, Z-independent)          [COMPASS #2]
                → radial u₁ of boundary-1 row     §4c (Jac u₁²), u₀ passive prefactor
                  → CORNER blow-up u₁=u₀τ         §5  (accumulate Jac 3+2+1=6, loss order 2)
                    → monomial endpoint (BANKED)  §6  monomialIntegrand_integrable_of_lt
    accounting: 4 + 3 + 0 = 7 = minAdm (BANKED)   §6  Mval_decompose / minAdmRec_eq_minAdm

Everything except the two carrier sorries (`sjBoundaryPeel`, `sjJointResolution`) is banked. This slice
tells the formaliser that `sjJointResolution` for a corank-2 branch factors as: **Schur split (have) → MP
shears (have) → two radial blow-ups (have `radial_…`) → the CORNER blow-up + the unit-boundedness of the
downstream cores (the new brick) → monomial endpoint (have).**

---

## 8. NAMED GAP (bounded, not a wall) — the relative corank-step invariant / shared-support closure

The one step not reducible to banked machinery + the exact identities above:

> **On the generic-downstream chart of a corank-`q` branch, after the radial + unit-clear, the residual
> cores `U₀, U₁, U″` (`= frobSq(row · A₂)` for the various resolved rows) are simultaneously BOUNDED BELOW
> by a positive constant, uniformly across the finite pivot/rank cover, with the earlier exceptional
> coordinates preserved as monomial prefactors (never divided by).**

This is the "relative corank-step invariant" (`chart-lemma-probe.md`) / the joint-support closure
(`outer-construction-cert.md`, DATA-A/B/C, `0/171`). It is **bounded chart algebra** (lift the `(2,2,2)`
`Case111`/`Case222` templates to opaque widths + track which exceptional `u` divides which generator), NOT
resolution-of-singularities and NOT a mathematical wall — the VALUE is certified general-`L` (Aoyagi + 3
methods + the `(3,3,4)` published-RRR anchor). But it is genuine-new (un-banked), and it is where a
formalisation stalls. **It does not re-open the R1-UPPER scope call** — it is labour on a proven template.

The composed `(3,3,3,4)` run confirms this is the ONLY new brick: the corank-2 coupling and the deep-factor
sharing compose through it, no further obstruction appears.

---

## 9. General pattern vs `(3,3,3,4)`-specific

**M-GENERIC (transfers to any nondegenerate `M`, corank `q`):**
- Front-split peels the leftmost layer; pivot-chart cover of the front factor; Schur block split with the
  pivot inverse `a⁻¹` living only in `det-1` shears (COMPASS #1) — never a Jacobian determinant.
- Each positive boundary charge `q_j` = a radial blow-up of a `q_j`-variable block, Jacobian power `q_j−1`,
  loss order `2`. Successive active radials are resolved by blowing up their **common corner**, giving one
  terminal divisor of Jacobian power `Σ_j q_j − 1` and loss order `2`, hence branch threshold `½·Σq_j =
  ½·Mval(branch)`. Min over branches `= ½·minAdm` (banked). Corank-`q` reduces to corank-`(q−1)` by the
  radial + unit-clear, composing down to the corank-1 recursion.

**`(3,3,3,4)`-SPECIFIC:** the literal `2×2` Schur residual at boundary 0 and the `1×3` row blow-up at
boundary 1; the concrete charge vector `[4,3,0]`; the fact that this is the smallest chain where corank-2
couples through a shared deep layer. The exponent mechanism (§5 corner accumulation) is generic.

---

## 10. CASE 2 for this slice — does not bind (coarse bound suffices)

Aoyagi's Case-2 divisor exponent prints `M'_{S,J+1} = (M(S)−J)(M^{(S+1)}−J)` (the residual-block codim;
`aoyagi-2023-worked.tex §ssec:blowup`, image p.20). The printed-paper **pitfall** (charter §CASE 2,
`reference-notes-sj-kernel.md`): the pivot vector is stated in ACTUAL widths where the faithful form is the
PREFIX-MIN increment, discrepancy `(n_S − μ_S)(n_{S+1} − J)`. For `(3,3,3,4)` the running minima are
`M(1)=M(2)=M(3)=3` (all widths equal until the last `M₃=4`), so the prefix-min and actual-width forms of
the pivot **coincide on every boundary of this slice** — the typo does not bite here. Moreover the
trusted-spine slack (`2λ ≤ M^{(i)}M^{(j)}`, Case-2 never attains the min — `aoyagi-2023-worked.tex` (T-C),
non-binding) holds: every branch threshold `½·Mval ≥ 7/2` and the Case-2 exponents are `≥` these, so a
**coarse bound suffices** for this slice and no sharp Case-2 handling is needed. **Fidelity note for the
carrier:** build the prefix-min form regardless (the width-general grind hits `M(S) < M^{(s)}` chains where
the forms diverge); land the named-deviation fidelity card there, not silently. For `(3,3,3,4)` itself:
Case 2 non-binding, coarse bound OK. *(This is a scoped observation on the equal-prefix-width slice, not a
general Case-2 clearance.)*

---

## 11. Codex (decorrelated, xhigh; my accounting withheld) — CONCUR, with one correction I adopted

Codex independently produced: the identical Schur peel (§3), the identical "no det-inverse in the Jacobian"
argument via the two `det-1` shears (§3, block-triangular), the identical clean model `‖vA₂‖²+‖ΓWA₂‖²` (★),
the identical radial `Γ=u₀[[1,β],[γ,γβ+δ]]` with Jacobian `|u₀|³` and unit-clear to `diag(1,δ)` (§4b), and
the identical boundary-1 row blow-up (§4c).

**The correction I adopted (FACT, my earlier toy was wrong):** the binding local model is the **SUM**
`u₀²U₀ + u₁²U₁`, NOT the product `(u₀u₁)²`; the corner blow-up `u₁=u₀τ` then gives Jacobian power `6`, loss
order `2`, threshold `7/2` (§5). My first `vslice_accounting.py` toy modelled the loss as `(u₀u₁)²` and got
`7/4` — the sum form is correct and is what `vslice_corner.py` verifies. Codex's phrasing (verbatim):
"Looking at `u0=0` or `u1=0` separately gives the misleading `4/2` and `3/2`. The binding zero lies at the
corner… the codimensions add on the terminal exceptional divisor."

**Codex INFERENCE (preserved as such, not fact):** that this matches the general DLN `rlct = ½·codim`
result (it cited an external arXiv preprint for the pattern). I treat that as a consistency cross-check, not
part of the from-scratch certificate — the exact algebra (Schur, Jacobians, corner blow-up) is the FACT;
the value-match to the literature is the (already-cited) interface.

---

## 12. Closing

- **Firmest result.** The composed `(3,3,3,4)` corank-2 `(S,J)` machine runs end-to-end: front-split →
  pivot-chart → Schur split (`a⁻¹` in `det-1` shears only, COMPASS) → depth reduction `frobSq(H·A₂)` →
  radial + corank-2→1 + boundary-1 radial → **corner blow-up accumulating Jac `3+2+1=6`, loss order 2 →
  threshold `7/2`** → monomial endpoint; accounting `4+3+0 = 7 = minAdm`. All identities verified
  symbolically; Codex decorrelated-concurs and corrected my sum-vs-product toy.
- **Most likely thing to break it.** The named brick (§8): that the downstream cores `U₀,U₁,U″` stay
  bounded below uniformly across the shared-support / rank-profile cover (equivalently: the coupled corner
  has codim EXACTLY `7`, the sharing does not collapse it). Verified in prior certs + RRR-anchored, but
  un-banked in Lean; the crude scalar caricature `z²(x²+y²)` shows sharing *can* collapse, so this
  boundedness is genuinely load-bearing, not free.
- **Next construction to settle the open part.** Formalise the corner blow-up + unit-boundedness as the
  single new lemma feeding `sjJointResolution` (the rest is banked), on this `(3,3,3,4)` binding chart
  first, then lift to opaque widths (the relative corank-step invariant). `vslice_corner.py` is the exact
  target the Lean corner-blow-up lemma must reproduce (`∫ u₀^{Mval−1−2c′} du₀ < ⊤ ⇔ c′ < ½Mval`).
