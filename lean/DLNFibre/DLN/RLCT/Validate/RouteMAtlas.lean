import DLNFibre.DLN.RLCT.Validate.RouteMBridge
import DLNFibre.DLN.RLCT.Validate.ResolutionAtlas

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMAtlas` — the UNIFIED Route-M atlas (crux2, #38)

The §5(5)▸§5(3) seam, unified. The headline `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` factors
through `⨅ᵢ monomialThreshold (d i)(k i)(h i)`:
- `routeM_rlctAtOn_eq_iInf` (§5(5), `IsRouteMCover`): `rlctAtOn F 0 = ⨅ᵢ monomialThreshold` — the
  cover-integral bridge (crux2, `RouteMBridge`).
- `resolution_value_of_atlas` (§5(3), `IsResolutionAtlas`): `⨅ᵢ monomialThreshold = ofReal(lambdaCore M)`
  — the value-rearrangement (cover, `ResolutionAtlas`).
Both consume the SAME chart family `(ι, d, k, h)`. `RouteMAtlas` BUNDLES the two predicate-groups over
that shared family, so fm3's geometry discharges ONE structure and the headline is a one-step
`Eq.trans`. This resolves the dual-interface coherence flag (the two structures shared `(ι,d,k,h)` but
carried disjoint facts — cover-integral vs value).
-/

open MeasureTheory
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-- **The unified Route-M atlas** (crux2 #38). A single chart family `(ι, d, k, h)` that BOTH covers the
core `F` (the `IsRouteMCover` cover-integral facts ⟹ `rlctAtOn F 0 = ⨅`) AND realises the value (the
`IsResolutionAtlas` (S-min) facts ⟹ `⨅ = ofReal(lambdaCore M)`). fm3's chart geometry produces this one
datum; the headline `rlctAtOn F 0 = ofReal(lambdaCore M)` follows. `F` is the flat core (`= dlnLoss M 0`
in the post-blow-up coordinates the cover lives on). -/
structure RouteMAtlas {L : ℕ} (M : Fin (L + 1) → ℕ) {N : ℕ} (F : (Fin N → ℝ) → ℝ)
    (U : Set (Fin N → ℝ)) (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ) :
    Prop where
  /-- The §5(5) cover-integral facts: `F` is covered by the chart family (⟹ `rlctAtOn F 0 = ⨅`). -/
  isCover : IsRouteMCover F U ι d k h
  /-- The §5(3) value facts: the family realises `lambdaCore M` (⟹ `⨅ = ofReal(lambdaCore M)`). -/
  isValue : IsResolutionAtlas M ι d k h

/-- **The Route-M headline (crux2 #38, the §5(5)▸§5(3) composition).** From a single `RouteMAtlas`, the
core's RLCT at the deepest point IS the closed-form `lambdaCore M`:
`rlctAtOn (core) 0 = ofReal(lambdaCore M)`. One-step `Eq.trans` of the bridge (`rlctAtOn = ⨅`) and the
value (`⨅ = ofReal lambdaCore`), both consuming the atlas's shared `(ι, d, k, h)`. This is `resolution_charts`
proper, assembled — modulo fm3 producing the `RouteMAtlas` for the actual `dlnLoss M 0` cover. Core-only
(no `nReg` regular shift; that is L2/Fubini downstream). -/
theorem routeM_rlctAtOn_eq_lambdaCore {L : ℕ} (M : Fin (L + 1) → ℕ) {N : ℕ} (F : (Fin N → ℝ) → ℝ)
    (U : Set (Fin N → ℝ)) (ι : Type) [Fintype ι] [Nonempty ι] (d : ι → ℕ)
    (k h : (i : ι) → Fin (d i) → ℕ) (atlas : RouteMAtlas M F U ι d k h) :
    rlctAtOn F (0 : Fin N → ℝ) = ENNReal.ofReal (lambdaCore M : ℝ) :=
  (routeM_rlctAtOn_eq_iInf F U ι d k h atlas.isCover).trans
    (resolution_value_of_atlas M ι d k h atlas.isValue)

end DLNFibre.DLN.RLCT
