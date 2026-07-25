import DLNFibre.DLN.Aoyagi.Corank2Chart334
import DLNFibre.DLN.Aoyagi.Corank2ChartJac

/-!
# R1 M1 — `unit ≡ 1` DERIVED on the built COUPLED (3,3,4) chart (the §5 fidelity harness)

The elder's R1 M1 / RED-FLIP piece: is the load-bearing `unit ≡ 1` **derived** at the built coupled
leaf, or only assumed? This module records — as named results stated on `chart334`'s ACTUAL fields —
that it is DERIVED, ending the search: the RED-FLIP does not fire.

**The chart is genuinely coupled.** `chart334.g = gWrap = sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘ bbA1`
(`Corank2Chart334`/`Corank2ChartJac`): `shearH` is the corank-2 block-elimination shear carrying the
coupled residual `Δ = D − C·B`; `(3,3,4)` is corank-2, the coupling is present.

**`unit ≡ 1` is DERIVED on the ACTUAL Jacobian, no hand telescope.** `jacDet g u =
LinearMap.det (fderiv ℝ g u)` — the genuine `|det Dg(u)|` (`ProductResolution.jacDet`). The collapse
`|jacDet gWrap u| = |u₀|⁷·|u₁|³·|u₂₀|⁸` (`abs_jacDet_gWrap`) is proved by the genuine chain rule
`jacDet_comp` (= `fderiv_comp` + `LinearMap.det_comp`) over the per-atom Jacobians: `shearH`
unipotent
(`jacDet_blockShear = 1`, `det ≡ 1`), `permP` a coordinate permutation (`|jacDet| = 1`), and
`bbA0`/`bbA1`/`sigmaPiv` exact-monomial block blow-ups (`jacDet_blockBlowupMap`). The non-monomial
factor is therefore **identically `1`** — the `unit ≡ 1` the deep build needs, from
`unipotent-elim det≡1 × exact-monomial blow-up`, NOT assumed. All clean-three.

**The terminal-shrink ⋈ cover gate is GREEN on the ACTUAL chart, not merely conditionally.**
`chart334.nbhd = Set.univ`: the certificate region is the FULL space, so `terminal_bezout`'s shrink
is vacuous *at the built leaf* (`chart334.hideal_fwd/bwd` are BOTH stated on `univ`). This
discharges the `unit ≡ 1` hypothesis that `admissible_leaf_region_222_of_collapse`
(`Corank2AdmissibleLeaf222`) took
as an assumption — here it is a theorem about the built chart.

**Scope (honest):** `(3,3,4)` = corank-2 only. A corank ≥ 3 chart is NOT built (`cert_334` is
corank-2); the WIDE reach at corank ≥ 3 is a genuine new construction (a larger composite `g` +
its telescope), detail-at-scale but unbuilt — owed, not banked.

## Main results
- `chart334_collapse_actual` — `|jacDet chart334.g u| = jacWeight chart334.jac u`: the pure-monomial
  Jacobian collapse (`unit ≡ 1`) on the built chart's ACTUAL `g` and exponent `jac`.
- `chart334_unit_eq_one` — `chart334.unit = fun _ ↦ 1` (the field is identically `1`).
- `chart334_nbhd_univ` — `chart334.nbhd = Set.univ` (no terminal-shrink at the built leaf).
-/

open DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi.Corank2UnitOneDerived

open DLNFibre.DLN.Aoyagi

/-- **The §5 fidelity harness — `unit ≡ 1` on the ACTUAL Jacobian of the built coupled chart.**
`|jacDet chart334.g u| = jacWeight chart334.jac u`: the built `(3,3,4)` chart's Jacobian collapses
to a pure monomial (no unit factor) — on `chart334`'s ACTUAL map `g` and exponent `jac`, derived
via `gWrap_hjac`'s `jacDet_comp` telescope over the coupled composite. The `unit` field being
identically `1` is exactly the vanishing of this non-monomial factor. -/
theorem chart334_collapse_actual (u : Fin 21 → ℝ) :
    |jacDet chart334.g u| = jacWeight chart334.jac u := by
  -- `chart334.g ≡ gWrap` and `chart334.jac ≡ jacWrap` by `rfl`, so `gWrap_hjac` types against the
  -- built chart's ACTUAL fields; the `|1|` non-monomial factor collapses (`unit ≡ 1`).
  have h : |jacDet chart334.g u| = jacWeight chart334.jac u * |(1 : ℝ)| :=
    Corank2ChartJac.gWrap_hjac u
  rw [h, abs_one, mul_one]

/-- The built chart's `unit` field is identically `1` — the non-monomial Jacobian factor, shown
to be
absent by `chart334_collapse_actual`. -/
theorem chart334_unit_eq_one : chart334.unit = fun _ ↦ (1 : ℝ) := rfl

/-- The built chart's certificate region is the FULL space — NO terminal-shrink at the built leaf,
so
the terminal-shrink ⋈ cover gate holds on the ACTUAL chart (its `hideal` inclusions are both on
`univ`), not merely under the `unit ≡ 1` hypothesis of `admissible_leaf_region_222_of_collapse`. -/
theorem chart334_nbhd_univ : chart334.nbhd = Set.univ := rfl

end DLNFibre.DLN.Aoyagi.Corank2UnitOneDerived
