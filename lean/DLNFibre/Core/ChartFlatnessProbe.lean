import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Ideal.GoingDown
import DLNFibre.Core.MultComorphism

/-!
# `DLNFibre.Core.ChartFlatnessProbe` — the G2a chart-flatness API-surface contract

**Status: API contract / thermometer artefact, NOT a theorem.** Thread 09 (2026-06-23) is the GATING
probe for route **M-goingdown** of the rank-chart fibre-codimension build: localize F1's `multComap`
at the pivot minor and ask whether the chart-localized total ring is **flat** (via free, through the
Schur section) over the chart-localized base ring — which would feed the LANDED going-down
additivity `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`.

This module records the **verified-present localization + flatness API** as `example`-blocks
(durable pins), and states — without `sorry` — the precise SHAPE of the gating object, so the
verdict rests on confirmed contracts rather than recalled signatures.

**The verdict (in the thread report):** the localization + flatness *API* is present at v4.29
and the localized comorphism `Localization.Away.mapₐ` is constructible. But the *object* route
M-goingdown needs flat is NOT the global `multComap` — that map is provably **not flat** (the fibre
dimension jumps 4 → 5 as the target degenerates rank 1 → rank 0 on the `(2,2,2)` anchor, recorded in
`Core.FibreCodim`). The flatness lives only on the **exact-rank determinantal chart**, whose
base/total rings are quotients by determinantal ideals carried in the engine ONLY as opaque
`vanishingIdeal`s — so the Schur section cannot be exhibited as an `AlgEquiv` without first building
an explicit presentation of those quotient rings (a determinantal-algebra build). See the report.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core.ChartFlatProbe

open scoped TensorProduct
open MvPolynomial

universe u

/-! ## The localized comorphism exists (the chart-localized `algebraMap`)

`Localization.Away.mapₐ f a : Localization.Away a →ₐ[R] Localization.Away (f a)` is the localized
algebra map. Specialised to F1's `multComap d` and a pivot element `Δ` of the base coordinate ring,
it IS the chart-localized comorphism the route wants — its mere existence is not the wall. -/

/-- **The chart-localized comorphism exists.** For a base-ring element `Δ` (the pivot minor in
target coords), `Localization.Away.map` builds the localized comorphism of `mult`:
`(R_base)[1/Δ] →ₐ[k] (R_tot)[1/multComap Δ]`. Construction, not flatness. -/
noncomputable example {k : Type u} [Field k] {N : ℕ} (d : Fin (N + 1) → ℕ)
    (Δ : MvPolynomial (Fin (d (Fin.last N)) × Fin (d 0)) k)
    (Rb : Type u) [CommRing Rb] [Algebra (MvPolynomial (Fin (d (Fin.last N)) × Fin (d 0)) k) Rb]
    [IsLocalization.Away Δ Rb]
    (Rt : Type u) [CommRing Rt] [Algebra (MvPolynomial (RepCoord d) k) Rt]
    [IsLocalization.Away (multComap d Δ) Rt] :
    Rb →+* Rt :=
  IsLocalization.Away.map Rb Rt (multComap d).toRingHom Δ

/-! ## Localization is always flat over the base (`IsLocalization.flat`)

The localization `R[1/Δ]` is flat over `R` — present and unconditional. This is the EASY flatness
(localizing a single ring); it is NOT the route's flatness (total-over-base via the comorphism). -/

/-- A localization is flat over the ring it localizes (`IsLocalization.flat`). -/
example {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] : Module.Flat R S :=
  IsLocalization.flat S M

/-! ## The route's flatness, stated honestly as a hypothesis (the gating object)

The fact route M-goingdown needs: total-localized FLAT over base-localized THROUGH the comorphism,
with the base/total being the EXACT-RANK quotient rings (not the full polynomial rings). The engine
has no explicit presentation of those quotient rings, so we can only *state* the target as a
hypothesis here — this `example` pins its TYPE (the going-down consumer), not a proof. -/

/-- **The going-down consumer.** Given the route's flatness as a `[Module.Flat]` instance on a tower
`Rb → Rt`, the LANDED height-additivity fires — confirming the gating fact, once proved, needs no
hypothesis beyond Noetherianity. This is the contract the chart-flatness proof must discharge. -/
example {Rb Rt : Type u} [CommRing Rb] [CommRing Rt] [Algebra Rb Rt] [IsNoetherianRing Rb]
    [IsNoetherianRing Rt] [Module.Flat Rb Rt]
    (p : Ideal Rb) [p.IsPrime] (P : Ideal Rt) [P.IsPrime] [P.LiesOver p] :
    P.height = p.height + (P.map (Ideal.Quotient.mk (p.map (algebraMap Rb Rt)))).height :=
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P

/-! ## The Schur-freeness model shape (free total over base on a TRIVIALIZED chart)

The correct trivialization (decorrelated-Codex, 2026-06-23) is NOT a polynomial algebra: the fibre
over `E` is **reducible** (`F_E = k[u,v,X,Z,ℓ,m]/(uX+vZ−1, ℓm)` for the anchor — note the `ℓm = 0`
relation), so the chart is the BASE CHANGE `Rt ≃ₐ[Rb] Rb ⊗[k] F_E`, not `MvPolynomial _ Rb`. Over a
field `k` the fibre `F_E` is free as a `k`-module (every vector space is free), so the base change
is free, hence flat, over `Rb`. This pins what the Schur section must DELIVER; the wall is building
the trivializing `AlgEquiv` from the engine's opaque `vanishingIdeal`-quotients, not the closer. -/

/-- The base change `Rb ⊗[k] F` of a `k`-module `F` is free over `Rb` (over a field, `F` is free) —
the `Algebra.TensorProduct.instFree` lever the corrected Schur trivialization closes on. -/
example {k : Type u} [Field k] (Rb F : Type u) [CommRing Rb] [Algebra k Rb]
    [AddCommGroup F] [Module k F] : Module.Free Rb (Rb ⊗[k] F) := inferInstance

/-- **The Schur closer (model, corrected).** A chart trivialization `Rt ≃ₐ[Rb] Rb ⊗[k] F_E` to the
base change of the (reducible, free-over-`k`) fibre algebra `F_E` makes `Rt` free, hence flat, over
`Rb` — the one-liner the route ends on, once the trivializing `AlgEquiv` exists. -/
example {k : Type u} [Field k] (Rb Rt F : Type u) [CommRing Rb] [CommRing Rt] [Algebra k Rb]
    [AddCommGroup F] [Module k F] [Algebra Rb Rt] (e : Rt ≃ₗ[Rb] Rb ⊗[k] F) :
    Module.Flat Rb Rt :=
  Module.Flat.of_linearEquiv e

end DLNFibre.Core.ChartFlatProbe
