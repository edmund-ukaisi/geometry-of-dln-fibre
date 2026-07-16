import DLNFibre.DLN.RLCT.Validate.RouteMSJArity4Assembly
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankGeneric
import DLNFibre.DLN.RLCT.Validate.RouteMSJCellRank

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# `RouteMSJCorankRec` — item 4: the coupled per-cell finiteness `hfin` (Route A, corank recursion)

**Thread `genm-corankrec` (aoyagi-full Stage 2), the LAST substantive analytic content of the (□)
discharge.** Discharges the SOLE hypothesis of G2 (`frontChargeBox_lt_top_of_hfin`, on `genm-3abase`):
the coupled per-deep-cell finiteness of `frontChargeIntegrand M u c' p` at each binding cut `u = t+j`.

The design is `genm-couplerad/couplerad-cert.md` (§2/§4/§5/§8, decorrelated-confirmed): **Route A**, a
recursion on the CORANK of the reduced bilinear `frobSq(Front·Z_deep)` (NOT chain length — Route B is
DEAD, the charge compounds under length-induction). SVD-FREE via Cauchy–Binet
(`det(Q_bQ_bᵀ) = Σ_I det(Q_{b,I})²`), avoiding the D-C spectral friction. The charge
`det(Q_bQ_bᵀ)^{−a/2}` is ONE decoration, dominated per-corank on the BINDING-SHELL scope.

## Load-bearing scope (couplerad §5, Codex-red-teamed — CARRIED as hypotheses, NOT proved universal)

Charge-domination (chartwise `C ≥ floor = minAdm((u,)+deep) ≥ 2·T1q`) holds ONLY on **binding shells**
`u = t★+j` with `1 ≤ j < r` (`r = min(M₀−t, M₁−t)`) plus rankgen `a+b ≤ ρ−1`
(`ρ = deepTailMin M`). Off the binding shells the charge can lower the codim below the floor
(Codex CE `(6,8,5,5) u=5`, a non-binding cut). So these are **hypotheses** on `coupled_hfin`, supplied by
the upstream shell restriction; the boundary cuts `j=0` / `j=r` are OUTSIDE this scope and are
`arch1build`'s separate `hbdryFin`.

## Status

`coupled_hfin_cell` — the per-cell finiteness — is the item-4 mountain (couplerad ★5: the non-square
bilinear corank recursion, a substantive new build). It is stated here at the EXACT G2 cell shape with
the binding-shell scope; `coupled_hfin` assembles the `∀ i` form G2 consumes. NATIVE (the RRR-codim
lower bound is elementary `∫ r^{c−1−2q} dr < ∞` per chart — no `cited_aoyagi_dln`).
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

/-- **Item 4 (per-cell) — the coupled per-cell finiteness at a binding shell (Route A mountain).**
For a fixed deep-atlas cell `i : CRIndex (dropHead (redChain (t+j) M))`, the coupled front-charge
integral over the cell (intersected with the box) is finite, in the top-`c'` window
`(M₀−u)(M₁−u)/2 < c' < carrierThreshold M` (`u = t+j`). This is the SVD/RRR-floor mountain: the
per-cell coupled RLCT-codim `≥ minAdm((u,)+deep) ≥ 2·T1q`, realized by the covering monomial
resolution (couplerad §2 — Stage A raw pivot/Schur split, Move 1 y-Morse peel, Move 2 lost-block
bilinear corank recursion), the charge `det(Q_bQ_bᵀ)^{−a/2}` dominated on the binding-shell scope.

ISOLATED as a documented correct-statement `sorry` (the non-square corank recursion, couplerad ★5) —
being driven incrementally: square sub-family (`u=M₂=n`) via banked `routeMBoxThresholdFinite_rrp`
first, then the non-square per-corank `SchurRecStep`. -/
theorem coupled_hfin_cell (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ) (c' : ℝ)
    (hshell : BindingShell M t j)
    (hc'lo : ((M 0 - (t + j) : ℕ) : ℝ) * ((M 1 - (t + j) : ℕ) : ℝ) / 2 < c')
    (hc'hi : c' < carrierThreshold M)
    (i : CRIndex (dropHead (redChain (t + j) M))) :
    ∫⁻ p in (paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1)
        ∩ projDeep M (t + j) ⁻¹'
          (deepCell (dropHead (redChain (t + j) M)) (dropHead (redChain (t + j) M) 0) L
            le_rfl (dropHead (redChain (t + j) M) (Fin.last L)) i
            (fun _ => (1 : Matrix (Fin (dropHead (redChain (t + j) M) (Fin.last L)))
              (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ))),
      frontChargeIntegrand M (t + j) c' p < ⊤ := by
  sorry

/-- **Item 4 — the coupled per-cell finiteness `hfin` (the G2 hypothesis) at a binding shell.** The
`∀ i` form G2 (`frontChargeBox_lt_top_of_hfin`) consumes, at cut `u = t+j`: for every deep-atlas cell
the coupled front-charge box integral is finite. Composes trivially over the finite cell family from
`coupled_hfin_cell`. This is EXACTLY the `hfin` hypothesis of `frontChargeBox_lt_top_of_hfin M (t+j) c'`
(so a caller discharges G2 by `frontChargeBox_lt_top_of_hfin M (t+j) c' (coupled_hfin M t j c' …)`). -/
theorem coupled_hfin (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ) (c' : ℝ)
    (hshell : BindingShell M t j)
    (hc'lo : ((M 0 - (t + j) : ℕ) : ℝ) * ((M 1 - (t + j) : ℕ) : ℝ) / 2 < c')
    (hc'hi : c' < carrierThreshold M) :
    ∀ i : CRIndex (dropHead (redChain (t + j) M)),
        ∫⁻ p in (paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1)
            ∩ projDeep M (t + j) ⁻¹'
              (deepCell (dropHead (redChain (t + j) M)) (dropHead (redChain (t + j) M) 0) L
                le_rfl (dropHead (redChain (t + j) M) (Fin.last L)) i
                (fun _ => (1 : Matrix (Fin (dropHead (redChain (t + j) M) (Fin.last L)))
                  (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ))),
          frontChargeIntegrand M (t + j) c' p < ⊤ :=
  fun i => coupled_hfin_cell M t j c' hshell hc'lo hc'hi i

/-- **Interface-fidelity witness.** `coupled_hfin`'s output is EXACTLY the `hfin` slot of G2
(`frontChargeBox_lt_top_of_hfin`) at cut `u = t+j` — so a caller discharges the front-charge box
finiteness at a binding shell by feeding `coupled_hfin` straight in, no bridge. This pins the interface
`arch1build`'s assembly consumes (the composition `hG1 → LINK → G2`). -/
example (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ) (c' : ℝ)
    (hshell : BindingShell M t j)
    (hc'lo : ((M 0 - (t + j) : ℕ) : ℝ) * ((M 1 - (t + j) : ℕ) : ℝ) / 2 < c')
    (hc'hi : c' < carrierThreshold M) :
    ∫⁻ p in paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1,
        frontChargeIntegrand M (t + j) c' p < ⊤ :=
  frontChargeBox_lt_top_of_hfin M (t + j) c' (coupled_hfin M t j c' hshell hc'lo hc'hi)

/-! ## Route-B interior deliverables — the cell-level genericity `hGae` (feeds arch1build's conversion) -/

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

end DLNFibre.DLN.RLCT
