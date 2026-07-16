# genm-tideD-edgecshift — R2 (the C-shift CoV) + the remaining edge mountain map

**Seat:** formaliser (tide). **Picks up:** edgeasm's edge-reduction continuation
(`genm-tideD-edgeasm`). **Base:** `origin/expedition/genm-tideD-edgeasm @389fdd661` (edgeasm's scalar engine
+ atoms + satred's R2 de-risk + W2 single-chain correction). **Branch:**
`expedition/genm-tideD-edgecshift @95fa63aa7`. **Consultants:** dbuild (density-bound shape + rightMulₚ
diamond fix), edgebrick ({v=0}-null + `|v_{j₀}|^{−a}` Jacobian + outer-integrability), satred (exact R2
statement + de-risk). All three converged on the R2 statement below.

## LANDED this tide — R2 (sorry-free, clean-three `[propext, Classical.choice, Quot.sound]`)

`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJEdgeCShift.lean` (network-free, on `RouteMSJEdgeScalar` + Mathlib).
See `statement-card.md` for the four exact signatures. The core:

    edge_C_shift_bound :  ∫_{C∈[−1,1]^{a×(u+1)}} (W + ‖(of C)·v + β‖²)^{−c'} dC
                            ≤ 2^{a·u}·|v_{j₀}|^{−a} · scaledRadialEuclid(W, c')

The **crux** the multi-course-correction converged to (R2 was the only "genuinely-hard" piece; satred
de-risked it to medium). Route: peel column `j₀` (volume-preserving `piFinSuccAbove ∘
arrowProdEquivProdArrow`) → the `a`-dim affine-substitution atom `affineScale_pi_le` (the genuinely-new
content: `map_addHaar_smul` Jacobian `|v₀|^{−a}` + translation-invariance β-absorption + box→ℝ^a
a-fortiori) → transverse volume `2^{a·u}` → `radial_pi_eq_euclid` bridge to the landed `scaledRadialEuclid`.

**Not the wall it was feared to be:** the two feared risks (matrix-CoV module diamond; MP/apply defeq)
both dissolved — dbuild's `rightMulₚ`-over-pi pattern generalises, and `MeasurePreserving e` (composite
column-peel) + its apply-readback both close by `.comp` / `rfl`. No `map_linearMap_addHaar` over
`Matrix.module`; the whole CoV is native over the raw pi type.

## The banked edge map (edgeasm's, updated) — what remains for the full `edge_coupledBox_lt_top`

R1 (FreeBilinear) banked · P1 (Γ polar) banked · **R2 (C-shift) LANDED this tide** · P3
(scaledRadialEuclid) banked · L1/L2 (σ-log, δ-fold) banked. Remaining, all **medium** with atoms in hand:

| Step | Content | Status |
|---|---|---|
| P2 | coupling → log: satred COLLAPSED this into P3 + δ-fold (the log is `scaledRadialEuclid` at the critical exponent `c'=a/2`, σ-independent / β-invariant — R2 absorbs σ). No separate `u=rs` CoV for the generic edge. | atoms in hand (P3 + `one_add_log_inv_le_rpow`) |
| L3 | 2D-leaf δ-bound: `scaledRadialEuclid_eq` gives `W^{a/2−c'}` for `c'>a/2`; at the `c'=a/2` tie it is `≍ log(1/W)`, δ-folded via banked `one_add_log_inv_le_rpow` → `W^{−δ}`. | medium |
| W1 | `W = frobSq(P·Q̃ₚ)+transverse` constant over the C/σ/γ integration | satred-verified (algebraic) |
| W2 | **SINGLE**-chain (satred, verified 0/377): reduce to `redChain u M` at exponent `c'−ab/2+δ`; finiteness via banked cut-soundness `sjChargeBudget_le` (`RouteMSJResolution` — `minAdm M ≤ (M₀−u)(M₁−u) + minAdm(redChain u M)`); one arity−1 IH call. **No u'-cut multi-chain at the edge.** | medium (1 IH call + 1 banked lemma) |
| R3 | `b≥2`: `(b−1)`-block minor chart, bounded Gram-det Jacobian (satred). `b=1` skips it. | bounded (b=1 first) |

**The assembly wiring** (`coupledBoxIntegrand` → `freedSchurLoss` → R1 corank-one peel → P1 polar →
the `‖C·v+β‖²` form R2 consumes) is the connective tissue between the banked atoms and R2, and is itself
a substantial (medium) step. R2 (this tide) is the clean interface between that wiring and the radial
engine — it takes the localized `(W+‖(of C)·v+β‖²)^{−c'}` box integral and returns `K·W^{a/2−c'}·B`.

## Two assembly-level obligations R2 does NOT carry (by design; consultant-confirmed)

1. **`{v=0}`-null disposal** (edgebrick's Q1). `v = Q̃ₚ·ω`; `{v=0}` is a positive-codim algebraic subset —
   NOT an R2 case. Dispose it at assembly level via the reduced chain (satred), model on
   `coupledBox_deficientCell_null`'s `Nz` argument.
2. **Outer integrability of `|v j₀|^{−a}`** (edgebrick's Q2). R2's constant `K(v)=2^{a·u}·|v j₀|^{−a}`
   blows up as `v→0` (fine pointwise, v fixed nonzero). Over the reduced `(z, A_cor)` params, integrability
   of the `|v j₀|^{−a}` factor needs the **adaptive pivot** `j₀ = argmax|vⱼ|` (`|v j₀| ≥ ‖v‖_∞`) and the
   power condition `a ≤ codim{v=0}` — the microscopic rank-sector balance satred's KILL-check guarantees.
   Off the tie (`a < codim`) the Jacobian is integrable outright; at the tie (`a = codim`) the δ-slack
   (L3) carries it. `edge_C_shift_bound` takes `j₀` + `v j₀ ≠ 0` as hypotheses precisely so the assembly
   picks `j₀ = argmax`.

## Do-NOT-commit scratch

`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJEdgeAssembly.lean` — the Card-2 `edge_coupledBox_lt_top`
signature skeleton (body `sorry`, exact-fits arch1build's `hcell(edge i)`). Left uncommitted (zero-sorry
gate), same as edgeasm. It validates the assembly interface; the next tide fills it from the map above.
