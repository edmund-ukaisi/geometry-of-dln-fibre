import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontChargeBox

set_option linter.style.longLine false

/-!
# `RouteMSJArity4Assembly` — the coupled-incidence assembly skeleton (arity ≥ 4, per-`c'`)

**Thread `genm-3abase` (aoyagi-full Stage 2), the coupled-incidence route CAPSTONE skeleton.** Wires the
three coupled-route bricks into the per-`c'` box-finiteness

    routeMLayerBoxIntegral M c' 1 < ⊤

for a `≥ 4`-width chain `M` at a NONDEGENERATE binding cut `t` (`t + 1 ≤ min(M₀,M₁)`), from the two
remaining builds as HYPOTHESES:

* `hG1` — **G1** (tpeel, `RouteMSJTPeel`): `box ≤ ∑_j ∑_ρ ∑_κ shellSpineIntegrand M (t+j) κ ε r j c'`
  (the front-split + outer singular-shell cover of the tail product + inner co-null pivot-chart cover +
  freed change-of-variables). `r = min(M₀−t, M₁−t)`.
* `hfin` — **item 4** (couplerad → formaliser): the coupled per-cell finiteness at each cut `u = t+j`
  (the SVD singular-value-ray / RRR-floor mountain), the sole hypothesis of `G2`.

The wiring is the composition `hG1 → LINK → G2 → finite sum`:
`shellSpine_le_frontCharge_binding` (LINK) bounds each shell integrand by the front-charge box integral,
`frontChargeBox_lt_top_of_hfin` (G2) makes each such box integral finite given `hfin`, and a finite sum
(triple `ENNReal.sum_lt_top`) of finite terms is finite. NATIVE (no `cited_aoyagi_dln`).

## Load-bearing scope (caveats next to the claim)

This isolates the two remaining builds as clean holes, but the conclusion is **per-`c'` and carries two
further restrictions baked as hypotheses — they are NOT free**:

* `hc'` — the LINK's block-charge lower bound `(M₀−(t+j))(M₁−(t+j))/2 < c'` at every shell `j`. The
  binding constraint is `j = 0`: `(M₀−t)(M₁−t)/2 < c'`. So this skeleton covers only the **top `c'`
  window** `(M₀−t)(M₁−t)/2 < c' < ½·minAdm M`. The complementary block-dominant regime
  `c' ≤ (M₀−t)(M₁−t)/2` (where the front block's own Morse integral converges) is a SEPARATE, easier
  argument still owed for the full `RouteMBoxThresholdFinite M` (all `c'`).
* `htb`/`hbind` — a NONDEGENERATE binding cut. Existence of a binding cut is banked
  (`frontPeel_binding_cut` / `exists_binding_cut`); its nondegeneracy (`t + 1 ≤ min(M₀,M₁)`, i.e. the
  binding argmin is not the full `min`) is a further fact the `(□)` closure must supply.

So `routeMBox_arity4_lt_top_of_coupled` is the coupled route's per-`c'`, top-window,
nondegenerate-binding core; closing the full arity-≥4 `(□)` = `RouteMBoxThresholdFinite M` from it needs
(a) the block-dominant `c'`-complement and (b) the binding-nondegeneracy, then the banked strong-induction
wrapper `routeMBoxThresholdFinite_of_step`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory DeepAtlas
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The coupled-incidence assembly skeleton (arity ≥ 4, per-`c'`, top window, binding cut).** Given
G1 (`hG1`: the box is dominated by the finite triple sum of shell integrands) and item 4 (`hfin`: the
coupled per-cell finiteness at each cut `t+j`), the box integral is finite. Wires
`shellSpine_le_frontCharge_binding` (LINK) and `frontChargeBox_lt_top_of_hfin` (G2). NATIVE.

See the module docstring for the scope: the conclusion is per-`c'`, restricted to the top window
`(M₀−t)(M₁−t)/2 < c'` (via `hc'`) at a nondegenerate binding cut (via `htb`/`hbind`). -/
theorem routeMBox_arity4_lt_top_of_coupled
    (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (ε c' : ℝ)
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i) (htb : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M))
    (hc' : ∀ j : Fin (min (M 0 - t) (M 1 - t) + 1),
        ((M 0 - (t + (j : ℕ)) : ℕ) : ℝ) * ((M 1 - (t + (j : ℕ)) : ℕ) : ℝ) / 2 < c')
    (hG1 : routeMLayerBoxIntegral M c' 1
        ≤ ∑ j : Fin (min (M 0 - t) (M 1 - t) + 1),
            ∑ _ρ : Fin (t + (j : ℕ)) ↪ Fin (M 0),
              ∑ κ : Fin (t + (j : ℕ)) ↪ Fin (M 1),
                shellSpineIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c')
    (hfin : ∀ (j : Fin (min (M 0 - t) (M 1 - t) + 1))
        (i : CRIndex (dropHead (redChain (t + (j : ℕ)) M))),
        ∫⁻ p in (paramsBoxM (redChain (t + (j : ℕ)) M) 1 ×ˢ matBox (M 1 - (t + (j : ℕ))) (M 2) 1)
            ∩ projDeep M (t + (j : ℕ)) ⁻¹'
              (deepCell (dropHead (redChain (t + (j : ℕ)) M)) (dropHead (redChain (t + (j : ℕ)) M) 0) L
                le_rfl (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L)) i
                (fun _ => (1 : Matrix (Fin (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L)))
                  (Fin (dropHead (redChain (t + (j : ℕ)) M) (Fin.last L))) ℝ))),
          frontChargeIntegrand M (t + (j : ℕ)) c' p < ⊤) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  refine lt_of_le_of_lt hG1 ?_
  refine ENNReal.sum_lt_top.mpr (fun j _ => ?_)
  refine ENNReal.sum_lt_top.mpr (fun _ρ _ => ?_)
  refine ENNReal.sum_lt_top.mpr (fun κ _ => ?_)
  have hj : (j : ℕ) ≤ min (M 0 - t) (M 1 - t) := Nat.lt_succ_iff.mp j.isLt
  exact lt_of_le_of_lt
    (shellSpine_le_frontCharge_binding M t (j : ℕ) κ ε c' hj (hc' j) ht1 hnd htb hbind)
    (frontChargeBox_lt_top_of_hfin M (t + (j : ℕ)) c' (hfin j))

end DLNFibre.DLN.RLCT
