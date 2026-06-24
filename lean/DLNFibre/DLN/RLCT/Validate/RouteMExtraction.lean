import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import DLNFibre.DLN.RLCT.Foundations.LossContinuity
import DLNFibre.DLN.RLCT.Foundations.S1Fubini

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMExtraction` — the flat-coordinate extraction layer (fm3, #86)

The flat-coordinate repackaging that lets the headline feed the genuine loss `dlnLoss M 0` into crux2's
abstract Route-M bridge `routeM_rlctAtOn_eq_iInf` (which consumes `F : (Fin N → ℝ) → ℝ`, `U`, `ι d k h`).
Three definitions + the keystone transport:

- `routeMAmbient M := flatDim M` — the flat dimension `N` (`Σ_s M⁽ˢ⁾·M⁽ˢ⁺¹⁾`, the matrix-tuple size).
- `routeMCore M := dlnLoss M 0 ∘ (paramsEquivFlat M).symm` — the loss in flat coordinates, an
  `(Fin (flatDim M) → ℝ) → ℝ` (the bridge's `F`).
- `routeMBaseNbhd M := flatOpenBox (flatDim M)` — the bounded open box `(−1,1)^N ∋ 0` (the bridge's `U`).

The KEYSTONE (`rlctAtOn_routeMCore_transport`): the bridge concludes about `rlctAtOn (routeMCore M) 0`;
this transports it to the genuine `rlctAtOn (dlnLoss M 0) (fun _ => 0)` at the deepest point, via the
measure-preserving homeomorphism `paramsEquivFlat M` (`rlctAtOn_comp_homeomorph`, S1Fubini) + the
zero-preserving `paramsEquivFlat M (fun _ => 0) = 0`. This is the general-M analog of
`rlctAtOn_dlnLoss222_transport` (ParamsFlat222, the (2,2,2) seam).

NOTE the scope: this layer is INDEPENDENT of `routeStep`/`routeMIota` (the realizability wall, #85). It
provides the `F`/`U`/`N` the bridge needs from the loss side; the bridge's `ι d k h` come from the chart
family (gated). So this banks the headline plumbing the route to `routeM_rlctAtOn_eq_iInf` rests on.
-/

open MeasureTheory
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The three extraction definitions -/

/-- **The flat ambient dimension** of the Route-M chart problem for `M`: `flatDim M = Σ_s M⁽ˢ⁾·M⁽ˢ⁺¹⁾`,
the number of real coordinates in a parameter tuple `Params M`. The bridge's `N`. -/
def routeMAmbient (M : Fin (L + 1) → ℕ) : ℕ := flatDim M

/-- **The loss in flat coordinates**: `dlnLoss M 0` precomposed with the inverse flattening
`(paramsEquivFlat M).symm : (Fin (flatDim M) → ℝ) → Params M`. The bridge's `F`. -/
noncomputable def routeMCore (M : Fin (L + 1) → ℕ) : (Fin (routeMAmbient M) → ℝ) → ℝ :=
  fun x => dlnLoss M 0 ((paramsEquivFlat M).symm x)

/-- **The base neighbourhood**: the bounded open box `(−1,1)^N ∋ 0` in the flat coordinates. The bridge's
`U`. (A bounded open set containing the deepest point — NOT `univ`; the `rlctAt`/`weightedThreshold`
`∃ U ∈ 𝓝 0` quantifier needs a genuine neighbourhood, and `cover_le`'s finiteness needs boundedness.) -/
def routeMBaseNbhd (M : Fin (L + 1) → ℕ) : Set (Fin (routeMAmbient M) → ℝ) :=
  flatOpenBox (routeMAmbient M)

/-! ## The base-neighbourhood facts (open / contains 0 / bounded) -/

/-- `routeMBaseNbhd M` is open. -/
theorem isOpen_routeMBaseNbhd (M : Fin (L + 1) → ℕ) : IsOpen (routeMBaseNbhd M) :=
  isOpen_flatOpenBox _

/-- `0 ∈ routeMBaseNbhd M` (the deepest flat point is in the box). -/
theorem mem_routeMBaseNbhd_zero (M : Fin (L + 1) → ℕ) :
    (0 : Fin (routeMAmbient M) → ℝ) ∈ routeMBaseNbhd M :=
  mem_flatOpenBox_zero _

/-- `routeMBaseNbhd M` is bounded (it sits in `[−1,1]^N`). -/
theorem isBounded_routeMBaseNbhd (M : Fin (L + 1) → ℕ) :
    Bornology.IsBounded (routeMBaseNbhd M) :=
  isBounded_flatOpenBox _

/-! ## The core facts (continuity / measurability) -/

/-- `routeMCore M` is continuous (`dlnLoss` continuous ∘ the continuous inverse flattening). -/
theorem continuous_routeMCore (M : Fin (L + 1) → ℕ) : Continuous (routeMCore M) :=
  (continuous_dlnLoss M 0).comp (continuous_paramsEquivFlat_symm M)

/-- `routeMCore M` is measurable (continuous ⟹ measurable). The bridge's `Fmeas`. -/
theorem measurable_routeMCore (M : Fin (L + 1) → ℕ) : Measurable (routeMCore M) :=
  (continuous_routeMCore M).measurable

/-! ## The keystone: the flat-core RLCT at `0` is the genuine loss RLCT at the deepest point -/

/-- `paramsEquivFlat M` as a homeomorphism (`MeasurableEquiv` + both continuities). -/
noncomputable def paramsEquivFlatHomeo (M : Fin (L + 1) → ℕ) :
    Params M ≃ₜ (Fin (flatDim M) → ℝ) :=
  { (paramsEquivFlat M).toEquiv with
    continuous_toFun := continuous_paramsEquivFlat M
    continuous_invFun := continuous_paramsEquivFlat_symm M }

/-- The flattening sends the deepest point (the layerwise-zero tuple) to flat zero:
`paramsEquivFlat M (fun _ => 0) = 0`. (`Params` has no canonical `Zero`; the deepest point is the
layerwise-zero tuple, and the flattening is the zero-preserving coordinate reindex.) -/
theorem paramsEquivFlat_deepest (M : Fin (L + 1) → ℕ) :
    paramsEquivFlat M (fun _ => 0 : Params M) = (0 : Fin (flatDim M) → ℝ) := by
  funext k; rfl

/-- `routeMCore M ∘ paramsEquivFlat M = dlnLoss M 0` (the loss-identity in flat coordinates): the flat
core, pulled back along the forward flattening, is the genuine loss. -/
theorem routeMCore_comp_paramsEquivFlat (M : Fin (L + 1) → ℕ) :
    (fun A => routeMCore M (paramsEquivFlat M A)) = dlnLoss M 0 := by
  funext A
  simp only [routeMCore, MeasurableEquiv.symm_apply_apply]

/-- **The keystone transport.** The flat-core RLCT at the flat origin equals the genuine loss RLCT at the
deepest point: `rlctAtOn (routeMCore M) 0 = rlctAtOn (dlnLoss M 0) (fun _ => 0)`. Via
`rlctAtOn_comp_homeomorph` (the measure-preserving homeomorphism `paramsEquivFlat M`) + the
zero-preserving `paramsEquivFlat_deepest`. The general-M analog of `rlctAtOn_dlnLoss222_transport`; this is
what carries crux2's bridge conclusion `rlctAtOn (routeMCore M) 0 = ⨅ …` back to the headline's
`rlctAtOn (dlnLoss M 0) (deepest)`. -/
theorem rlctAtOn_routeMCore_transport (M : Fin (L + 1) → ℕ) :
    rlctAtOn (routeMCore M) (0 : Fin (routeMAmbient M) → ℝ)
      = rlctAtOn (dlnLoss M 0) (fun _ => 0 : Params M) := by
  have hmp : MeasurePreserving (paramsEquivFlatHomeo M) volume volume :=
    measurePreserving_paramsEquivFlat M
  have hemb : MeasurableEmbedding (paramsEquivFlatHomeo M) :=
    (paramsEquivFlat M).measurableEmbedding
  have key := rlctAtOn_comp_homeomorph (paramsEquivFlatHomeo M) hmp hemb (routeMCore M)
    (fun _ => 0 : Params M)
  -- `key : rlctAtOn (routeMCore M ∘ e) deepest = rlctAtOn (routeMCore M) (e deepest)`
  have he0 : (paramsEquivFlatHomeo M) (fun _ => 0 : Params M) = (0 : Fin (flatDim M) → ℝ) :=
    paramsEquivFlat_deepest M
  rw [he0] at key
  -- `routeMCore M ∘ e = dlnLoss M 0`
  have hcomp : (fun A => routeMCore M (paramsEquivFlatHomeo M A)) = dlnLoss M 0 :=
    routeMCore_comp_paramsEquivFlat M
  rw [hcomp] at key
  exact key.symm

end DLNFibre.DLN.RLCT
