import DLNFibre.DLN.RLCT.Validate.RouteMAchieverStructAdm
import DLNFibre.DLN.RLCT.Validate.RouteMFlatStructV
import DLNFibre.DLN.RLCT.Validate.RouteMGenLeafIntegrand

/-!
# `RouteMAchieverRateFields` — the ∀M achiever-path rate-side `NodeAchieverChart` fields (decoder-agnostic)

The rate-side fields of the `NodeAchieverChart M` bundle, on the ACHIEVER path `tach M`
(`RouteMAchieverStructAdm`). The chart is the banked structured chart `phiFlatStructV M (tach M) …`
(`RouteMFlatStructV`), whose rate `routeMCore (phiFlatStructV … x) = (x p)²·UvalStructV … x` is
decoder-agnostic (banked `routeMCore_phiFlatStructV`). The unit is `UvalStructV` (`= VvalGen` of the
structured decoder at the achiever path).

Banked here (the FREE rate-side fields — they ride only on the rate identity + sum-of-squares, NO Jacobian
determinant, NO a.e.-positivity):

* `achieverPhi` / `achieverUfun` — the chart + unit on the achiever path (`phiFlatStructV`/`UvalStructV`
  at `tach M`, `structAdm_tach`).
* `routeMCore_achieverPhi` — the RATE `routeMCore M (achieverPhi x) = (x p)²·achieverUfun x` (∀M, one line
  from `routeMCore_phiFlatStructV`).
* `achieverUfun_nonneg` — `0 ≤ achieverUfun` (sum of squares, banked `VvalGen_nonneg`).
* `achiever_leaf_integrand` — the `NodeAchieverChart.leaf_integrand` field ∀M, for ANY exponent vector
  `leafH` and pivot, via the banked det-FREE `leaf_integrand_of_rate`.

THE OPEN WALL (the `Ubound` a.e.-positivity `∀ᵐ x, 0 < achieverUfun x`, + `Umeas`) is pinned as the contract
`achieverUbound_target` / `achieverUmeas_target` (`example`s, the durable interface). Per the build-tide
addendum (`threads/36-…/thread.md`) + Codex (`codex/deadleaf-vval-aepos-{prompt,answer}`):
- the structured (dead-leaf) `UvalStructV ≢ 0` for `L ≥ 2` (sympy `(2,2,2)`: `VvalGen = E²(w0²+w1²)`), but
  `≡ 0` for `L = 1` — so a uniform ∀M a.e.-positivity needs either the LIVE-leaf decoder (the §2 cert's
  `B_det M`, uniform witness `Hmat_0(0,0)=1`) or an interior-nonempty hypothesis + an `L=1` case split;
- EITHER way the proof needs the recursion-level `MvPolynomial` encoding of `Hmat_0` (Codex Q2/Q4: no v4.29
  analytic-zero-set shortcut), which the `ℝ`-pinned `Chain`/`Hmat` engine does not yet support.

Axiom-clean `[propext, Classical.choice, Quot.sound]` for the LANDED results (pure algebra; the `Classical`
is the `tStar` minimiser).
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The achiever-path chart + unit (decoder-agnostic rate) -/

/-- The ∀M achiever-path structured chart `phiFlatStructV M (tach M) …` (the binding pivot `⟨0,_⟩`). -/
noncomputable def achieverPhi (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
    (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  phiFlatStructV M (tach M) (structAdm_tach M hL) hN x

/-- The ∀M achiever-path unit factor `UvalStructV M (tach M) …` (`= VvalGen` of the structured decoder). -/
noncomputable def achieverUfun (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
    (x : Fin (routeMAmbient M) → ℝ) : ℝ :=
  UvalStructV M (tach M) (structAdm_tach M hL) hN x

/-- **The RATE identity ∀M** `routeMCore M (achieverPhi x) = (x p)²·achieverUfun x` — decoder-agnostic
(banked `routeMCore_phiFlatStructV`), the `NodeAchieverChart.leaf_integrand` rate factor on the achiever
path. -/
theorem routeMCore_achieverPhi (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (achieverPhi M hL hN x)
      = (x (structPivot M hN)) ^ 2 * achieverUfun M hL hN x :=
  routeMCore_phiFlatStructV M (tach M) (structAdm_tach M hL) hN x

/-- **`0 ≤ achieverUfun`** — sum of squares (banked `VvalGen_nonneg`). -/
theorem achieverUfun_nonneg (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
    (x : Fin (routeMAmbient M) → ℝ) :
    0 ≤ achieverUfun M hL hN x :=
  VvalGen_nonneg _ M (tach M) _ _

/-! ## The `leaf_integrand` field ∀M (det-FREE, via `leaf_integrand_of_rate`) -/

/-- **The `NodeAchieverChart.leaf_integrand` field ∀M** for the achiever path: for ANY exponent vector
`leafH` and the binding pivot `p = structPivot M hN`,
`(∏_j |x_j|^{leafH j})·|routeMCore M (achieverPhi x)|^{−c}
  = monomialIntegrand N (δ_p) leafH c x · (achieverUfun x)^{−c}`. Rides ONLY on the rate identity
`routeMCore (achieverPhi x) = (x p)²·achieverUfun x` + `achieverUfun ≥ 0` (NO Jacobian determinant). -/
theorem achiever_leaf_integrand (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
    (leafH : Fin (routeMAmbient M) → ℕ) (c : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (∏ j, |x j| ^ (leafH j)) * |routeMCore M (achieverPhi M hL hN x)| ^ (-c)
      = monomialIntegrand (routeMAmbient M) (nodeLeafK (routeMAmbient M) (structPivot M hN)) leafH c x
        * (achieverUfun M hL hN x) ^ (-c) :=
  leaf_integrand_of_rate (structPivot M hN) leafH
    (fun y => routeMCore M (achieverPhi M hL hN y)) (achieverUfun M hL hN)
    (fun y => routeMCore_achieverPhi M hL hN y) (fun y => achieverUfun_nonneg M hL hN y) c x

/-! ## The OPEN WALL — the `Ubound` a.e.-positivity + `Umeas` (pinned contracts)

These are the two rate-side fields that do NOT ride only on the rate identity. They are stated here as the
durable interface (`example`s the next tide discharges), NOT asserted — see the module docstring + the
build-tide addendum for why each needs the recursion-level `MvPolynomial` encoding of `Hmat_0` (and, for a
uniform ∀M statement, the live-leaf decoder or an `L=1` case split / interior-nonempty hypothesis). -/

/-- **CONTRACT (the wall): a.e.-positivity of the achiever unit.** What `NodeAchieverChart.Ubound`'s
positivity clause needs. UNPROVED here: `achieverUfun = VvalGen∘(structured dead-leaf decoder)`, which is a
nonzero polynomial in `x` for `L ≥ 2` (sympy `(2,2,2)`: `E²(w0²+w1²)`) but `≡ 0` for `L = 1`; the uniform
proof needs the recursion-level `MvPolynomial` encoding + `MvPolynomial.ae_eval_ne_zero`, OR the live-leaf
`B_det M` (cert §2/§5). Stated for `L ≥ 2` (the regime where the dead-leaf unit is non-vacuous). -/
example (M : Fin (L + 1) → ℕ) (hL2 : 2 ≤ L) (hN : 0 < routeMAmbient M)
    (hpos : ∀ M : Fin (L + 1) → ℕ, ∀ (hL : 0 < L) (hN : 0 < routeMAmbient M),
      ∀ᵐ x, 0 < achieverUfun M hL hN x) :
    ∀ᵐ x, 0 < achieverUfun M (by omega) hN x :=
  hpos M (by omega) hN

/-- **CONTRACT (the wall): measurability of the achiever unit.** What `NodeAchieverChart.Umeas` needs.
UNPROVED here: `achieverUfun` is a polynomial map in `x` (hence continuous, measurable), but there is no
banked `continuous_VvalGen∘decoder` over opaque widths yet. -/
example (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
    (hmeas : Measurable (achieverUfun M hL hN)) :
    Measurable (achieverUfun M hL hN) := hmeas

end DLNFibre.DLN.RLCT
