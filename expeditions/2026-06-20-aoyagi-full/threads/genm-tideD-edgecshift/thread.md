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

## The banked edge map — what remains for the full `edge_coupledBox_lt_top`

**STATUS (satred, VERIFIED after churn — definitive; a≥u being consolidated into the D-cert as single
source of truth).** The reliable core:

1. **The corner is FINITE, RLCT `= ½minAdm(M)`, NO wall** (`⊆ RMBTF(M)|_chart` + sublevel-volume).
2. **R2 (`edge_C_shift_bound`) + `edge_leaf_gamma_bound` (both LANDED) are CORRECT bricks** — β-invariant,
   σ-independent, δ-free, giving the FULL `ab/2` charge `W^{a/2−c'}` in the open window `c' > (M₀−u)(M₁−u)/2`.
3. **PRECISION (reviewer+Codex):** the FULL-SPACE `scaledRadialEuclid = W^{a/2−c'}·B` DIVERGES at `c'=a/2`
   (`B = ∫_{ℝ^a}(1+‖s‖²)^{−c'} = +∞` for `a=2c'`), it does NOT `≍ log(1/W)`. The tie-log is a
   BOUNDED/cutoff-radial property, not this full-space comparator; the open window excludes `c'=a/2`, so
   `edge_leaf_gamma_bound` gives a finite RHS throughout. (This corroborates: the log ≠ R2/scaledRadialEuclid.)

**The edge splits by `a` vs `u` (`a=M₀−u`, `u+1`=pivot columns):**
- **`a < u`: CLEAN network-free leaf, fully GO with what's LANDED.** Close = `edge_leaf_gamma_bound` →
  `|v_{j₀}|^{−a}`-disposal (finite iff `a<u`: `v=Q̃ₚ·ω`, `Q̃ₚ` has a kernel, `‖v‖~dist` to a codim-`u`
  locus ⟹ `∫_ω‖v‖^{−a}<⊤ ⟺ a<u` = `corner_block_lintegral_lt_top`, `g=‖·‖²`, `c'=a/2`, `N=u` — verified
  by satred, citation STANDS) → arity−1 IH on `redChain u M` (strict range, `sjChargeBudget_le`). δ-fold
  only at `c'=ab/2` (bounded-radial, W2).
- **`a ≥ u`: satred's design DONE (D-cert §3bis @38ae38662).** Keep the transverse; CoV `Y = C·Q̃ₚ` gives
  `∫_C(W+frobSq(C·Q̃ₚ+γ⊗Q_b))^{−c'}dC = det(Q̃ₚQ̃ₚᵀ)^{−a/2}·(W+‖M0⊥‖²)^{au/2−c'}·B` — charge `au/2`, NO
  `‖v‖^{−a}` (so a≥u is fine).
  **KEY (this thread): that C-integral IS the LANDED `RouteMSJGammaAtom.gammaAtom_aniso_shifted_eq`** with
  `R=Q̃ₚ` (`q=u`), `S=γ⊗Q_b`, `p=a` — `det(RRᵀ)^{−p/2}·Cresid(pq)·(w+‖S(I−P_R)‖²)^{−(c'−pq/2)}` matches
  term-for-term (needs `Q̃ₚQ̃ₚᵀ` PosDef = generic full-row-rank edge). So the hard a≥u C-integral is BANKED;
  the ONLY open piece is satred's reduced-chain ACCOUNTING (that `det(Q̃ₚQ̃ₚᵀ)^{−a/2}` + σ,γ integrate over
  the reduced chain to `½minAdm M` — plausibly the IH's leading-Gram, likely an assembly-level treatment).

R1 (FreeBilinear) banked · P1 (Γ polar) banked · P3 (scaledRadialEuclid) banked · L1/L2 (σ-log, δ-fold)
banked. Remaining:

| Step | Content | Status |
|---|---|---|
| a<u disposal wiring | `edge_leaf_gamma_bound` → `corner_block` (a<u) → IH on `redChain u M`. All atoms LANDED; the wiring instantiates them (assembly-level: `v=Q̃ₚ·ω`, `W=frobSq(P·Q̃ₚ)`). | atoms in hand — assembly wiring |
| a≥u fuller lemma | transverse-kept C-integral. | satred design pass (D-cert) |
| W1 | `W = frobSq(P·Q̃ₚ)` constant over the C/γ integration | satred-verified (algebraic) |
| W2 | **SINGLE**-chain (satred, verified 0/377): reduce to `redChain u M` at exponent `c'−ab/2+δ`; finiteness via banked cut-soundness `sjChargeBudget_le` (`RouteMSJResolution` — `minAdm M ≤ (M₀−u)(M₁−u) + minAdm(redChain u M)`); one arity−1 IH call. **No u'-cut multi-chain at the edge.** | medium (1 IH call + 1 banked lemma) |
| R3 | `b≥2`: `(b−1)`-block minor chart, bounded Gram-det Jacobian (satred). `b=1` skips it. | bounded (b=1 first) |

**The assembly wiring** (`coupledBoxIntegrand` → `freedSchurLoss` → R1 corank-one peel → P1 polar →
the `(W+‖η_C+σγ‖²)^{−c'}` form P2 consumes) is the connective tissue between the banked atoms and the
closers, and is itself a substantial (medium) def-heavy step.

**dbuild's KILL-guard (banked).** The tie-log is FOLDED (`c'→c'+δ` on the IH's open range via
`one_add_sigmaLog_le_rpow`), never COUNTED — the top-level deliverable stays a `< ⊤`/threshold/VALUE claim
(finiteness for `c' < ½·minAdm`), NEVER an order-of-pole or multiplicity `m` claim (D-cert guard iv).

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
