import DLNFibre.DLN.RLCT.Validate.RouteMSJArity4Assembly
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankGeneric
import DLNFibre.DLN.RLCT.Validate.RouteMSJCellRank

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# `RouteMSJCorankRec` — item 4: the Route-B interior deliverables (`hGae` + `hfront`) + the scope

**Thread `genm-corankrec` (aoyagi-full Stage 2).** Item 4 is the coupled per-deep-cell finiteness of the
LAST substantive analytic content of the arity≥4 `(□)` discharge. **Route B (coupledBox) is CANONICAL**
(coordinator, 2026-07-16): the cells (indexed by `CRIndex (dropHead (redChain u M))`, cell deep-rank
`ρ_i = cellRankIndex i`) dispatch by `ρ_i` vs `a+b` (`a = M₀−u`, `b = M₁−u`, `ρ = deepTailMin M`):
* `ρ_i < deepTailMin` (deficient) → NULL, `∫ = 0` (dbuild's `coupledBox_deficientCell_null`, via the atlas
  bridge `prod_rank_eq_cellRankIndex` in `RouteMSJCellRank` + `deepFactor_rank_ge_deepTailMin_ae`);
* generic `ρ_i = deepTailMin`, interior `a+b ≤ ρ_i` → **MINE** (the two lemmas below → `arch1build`'s
  `coupledCell_interior_lt_top`); generic edge/deep-corank `ρ_i < a+b` → dbuild's edge brick.

The Route-A frontCharge `∀ i` form (formerly `coupled_hfin_cell` / `coupled_hfin`) is REMOVED — superseded
(G2's frontCharge route is `+∞` at edge cuts; Route B is coupledBox-direct). NATIVE throughout (no
`cited_aoyagi_dln`).

## Load-bearing scope (couplerad §5, Codex-red-teamed)

`BindingShell M t j` (below): the in-scope binding shell `u = t★+j`, `1 ≤ j < r` (`r = min(M₀−t, M₁−t)`)
+ rankgen `a+b+1 ≤ deepTailMin M`. Off it the charge lowers the codim below the floor (Codex CE
`(6,8,5,5) u=5`, non-binding). `deepFactor_hZrank_of_le` needs `M₁−u ≤ deepTailMin` (from the binding cut,
`tailWidth_le_deepTailMin_of_binding`), which the shell supplies.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory DeepAtlas
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The binding-shell scope predicate (couplerad §5).** At a NONDEGENERATE binding cut `t` (argmin,
`hbind`) with `t + 1 ≤ min(M₀,M₁)`, a cut `u = t+j` is an in-scope binding shell when `1 ≤ j < r`
(`r = min(M₀−t, M₁−t)`, strict interior) and rankgen holds: `(M₀−u) + (M₁−u) + 1 ≤ deepTailMin M`
(`a+b ≤ ρ−1`). This is exactly the region where the coupled charge is dominated. -/
structure BindingShell (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ) : Prop where
  /-- `t` nondegenerate: strictly below the pivot min. -/
  htb : t + 1 ≤ min (M 0) (M 1)
  /-- `t` is the binding (argmin) cut. -/
  hbind : minAdm M = peelCharge M t + minAdm (redChain t M)
  /-- strict interior shell: `1 ≤ j`. -/
  hj1 : 1 ≤ j
  /-- strict interior shell: `j < r = min(M₀−t, M₁−t)`. -/
  hjr : j < min (M 0 - t) (M 1 - t)
  /-- rankgen `a+b ≤ ρ−1`: the corank widths fit strictly inside the deep-tail rank. -/
  hrankgen : (M 0 - (t + j)) + (M 1 - (t + j)) + 1 ≤ deepTailMin M

/-! ## Route-B interior deliverables — the cell-level genericity `hGae` + the `hfront` reduction

**Route B (coupledBox) is canonical** (coordinator, 2026-07-16). The superseded Route-A frontCharge `∀ i`
form (`coupled_hfin_cell` / `coupled_hfin` + its G2 witness) has been removed — it is not on the live path
(G2's frontCharge route is superseded; frontCharge is `+∞` at edge cuts). My live contribution is the two
interior lemmas below (feeding `arch1build`'s `coupledCell_interior_lt_top`), plus the atlas gate
`cellRank` / `prod_rank_eq_cellRankIndex` in `RouteMSJCellRank`. `BindingShell` (above) carries the
binding-shell scope both consume. -/

/-- **The corank-Gram genericity `hGae` ON an interior cell** (Route B; feeds arch1build's
`coupledCell_interior_lt_top`). On the cell region (box ∩ deep-cell), the corank Gram `Q_b·Q_bᵀ`
(`Q_b = A_cor·Z_deep`) is PosDef a.e. This is the BOX-level genericity `hGae_from_deepRank`
(built from `M₁−u ≤ deepTailMin M` at the binding cut, via `deepFactor_hZrank_of_le`), RESTRICTED to the
cell ⊆ box (`ae_mono` on `Measure.restrict_mono` — an a.e. statement descends to any subset: vacuous on
a null deficient cell, box-a.e. on the co-null generic cell). NATIVE, no new genericity content. -/
theorem hGae_cell_interior (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (hshell : BindingShell M t j)
    (i : CRIndex (dropHead (redChain (t + j) M))) :
    ∀ᵐ p ∂(volume.restrict ((paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1)
        ∩ projDeep M (t + j) ⁻¹'
          (deepCell (dropHead (redChain (t + j) M)) (dropHead (redChain (t + j) M) 0) L
            le_rfl (dropHead (redChain (t + j) M) (Fin.last L)) i
            (fun _ => (1 : Matrix (Fin (dropHead (redChain (t + j) M) (Fin.last L)))
              (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ))))),
      ((hsQ M (t + j) (deeperFlagZdeep M (t + j)) p.1 p.2).submatrix Sum.inr id
        * ((hsQ M (t + j) (deeperFlagZdeep M (t + j)) p.1 p.2).submatrix Sum.inr id)ᵀ).PosDef := by
  have hb : M 1 - (t + j) ≤ deepTailMin M :=
    le_trans (Nat.sub_le_sub_left (Nat.le_add_right t j) (M 1))
      (tailWidth_le_deepTailMin_of_binding M t hshell.htb hshell.hbind)
  have hbox := hGae_from_deepRank M (t + j) (deepFactor_hZrank_of_le M (t + j) hb)
  exact hbox.filter_mono (ae_mono (Measure.restrict_mono Set.inter_subset_left le_rfl))

/-- **The interior-cell front-charge finiteness (`hfront`), from schurB's FREE-BOX bound + cell⊆box
monotonicity** (Route B). The per-cell front-charge integral over the cell region (box ∩ deep-cell) is
bounded by the whole-box integral (`lintegral_mono_set`, cell ⊆ box), so schurB's free-box bound
`∫_box frontCharge < ⊤` (built for `a+b ≤ ρ`, consuming the `RouteMSchurWishartWeight` ladder) DIRECTLY
gives per-cell finiteness — no cell-specific analytic content on my side, just the monotone restriction.
This is the `hfront` slot of arch1build's `coupledCell_interior_lt_top`. -/
theorem frontCharge_cell_lt_top_of_freebox (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ) (c' : ℝ)
    (i : CRIndex (dropHead (redChain (t + j) M)))
    (hfreebox : ∫⁻ p in paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1,
        frontChargeIntegrand M (t + j) c' p < ⊤) :
    ∫⁻ p in (paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1)
        ∩ projDeep M (t + j) ⁻¹'
          (deepCell (dropHead (redChain (t + j) M)) (dropHead (redChain (t + j) M) 0) L
            le_rfl (dropHead (redChain (t + j) M) (Fin.last L)) i
            (fun _ => (1 : Matrix (Fin (dropHead (redChain (t + j) M) (Fin.last L)))
              (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ))),
        frontChargeIntegrand M (t + j) c' p < ⊤ :=
  lt_of_le_of_lt (lintegral_mono_set Set.inter_subset_left) hfreebox

/-- **`cellRankIndex i ≤ deepTailMin M`** (dbuild's trichotomy cap). The exact deep-product rank on any
atlas cell is below the deep-tail-width minimum: `cellRankIndex_le_inf'` (`≤ ⨅ (dropHead (redChain u M))`)
composed with `⨅ (dropHead (redChain u M)) = deepTailMin M` (both `inf'` over the shared function
`fun i => M i.succ.succ`, via `dropHead`/`redChain_succ`). Turns the null-disposal + rank-bridge into the
TRICHOTOMY: `cellRankIndex i < deepTailMin` (deficient → null) / `= deepTailMin` (the unique co-null generic
cell → interior|edge); `> deepTailMin` is impossible. -/
theorem cellRank_le_deepTailMin (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (i : CRIndex (dropHead (redChain u M))) :
    cellRankIndex (dropHead (redChain u M)) i ≤ deepTailMin M := by
  have hfun : dropHead (redChain u M) = fun i => M i.succ.succ := by
    funext i; rw [dropHead]; exact redChain_succ u M i
  refine le_trans (cellRankIndex_le_inf' (dropHead (redChain u M)) i) (le_of_eq ?_)
  rw [deepTailMin, hfun]

end DLNFibre.DLN.RLCT
