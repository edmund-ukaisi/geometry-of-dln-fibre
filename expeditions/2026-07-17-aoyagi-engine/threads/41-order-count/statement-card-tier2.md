# Statement card — Object E / P6, Tier 2 (the θ-attachment; arithmetic binding)

Seat: seat-E. Branch `expedition/aoyagi-engine-E`. Module `lean/DLNFibre/DLN/Aoyagi/OrderBinding.lean`.
**Tier 2** of the E-lane split: the thin DLN binding attaching the landed `aoyagiTheta`
(`Foundations.Lambda`) to the Tier-1 `bandCount` (`Core.Aoyagi.OrderCount`), instantiated at the
certified Def-3 selector objects `ell`/`residueA` (`Aoyagi.ClosedForm`). All are **value identities
between two in-tree `a(ℓ−a)+1` objects** — stable under any P6.2 (task #39) outcome.

Imports: `Core.Aoyagi.OrderCount` + `DLN.RLCT.Foundations.Lambda` + `DLN.Aoyagi.ClosedForm` ONLY
(MonumentAtlas/FoldProduced off-limits, as scoped).

---

> **Claim (θ-attachment).** The banded count equals the landed closed-form value:
> `bandCount ℓ a = aoyagiTheta ℓ a`, unconditionally (both `a(ℓ−a)+1`).
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.bandCount_eq_aoyagiTheta` (`…/OrderBinding.lean` @ `04da7648a`)
> - **Gloss.** `bandCount ℓ a = aoyagiTheta ℓ a`. Proof `rw [bandCount_eq, aoyagiTheta]`.
> - **Proved.** Unconditional. This is where the θ-name enters the E-lane (K3: Tier 1 stays neutral).
> - **Cited.** none.
> - **Deferred.** the identification of this count with Aoyagi's RLCT/zeta-pole multiplicity `ρ`
>   (P6.2, pnp-gated — task #39; elder's max-crossing-number hypothesis). NOT claimed in any name/docstring.
> - **Status.** sorry-free (build-confirmed, axiom-clean).

> **Claim (certified instantiation, pin (a)).** At the certified Def-3 selector objects,
> `thetaCount d r = aoyagiTheta (ell d r) (residueA d r).toNat`, where
> `thetaCount d r := bandCount (ell d r) (residueA d r).toNat`.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.thetaCount` / `thetaCount_eq_aoyagiTheta` (`…/OrderBinding.lean` @ `04da7648a`)
> - **Gloss.** The banded count at the certified `(ell d r, residueA d r)` equals `aoyagiTheta` there.
> - **Proved.** Immediate from `bandCount_eq_aoyagiTheta` (unconditional — no `residueA ≤ ell` bound
>   needed; the value identity holds for all naturals). Pin (a) discharged: parameters are the certified
>   `ClosedForm` objects, never free naturals.
> - **Cited.** none.
> - **Deferred.** the ρ-identification (as above); the through-selector VALUE gates
>   (`thetaCount ![2,2,2] 0 = 1`) need `ell`/`residueA` instance lemmas (`ell`/`residueA` are
>   `noncomputable`) — flagged for a follow-on, not built here.
> - **Status.** sorry-free (build-confirmed, axiom-clean).

**K1 ground-truth gates** (build-enforced, computable `aoyagiTheta` at the certified `(ℓ,a)`; RRR
table): `aoyagiTheta 2 2 = 1` [(2,2,2) & (3,3,4) → (ℓ,a)=(2,2)], `aoyagiTheta 2 1 = 2` [(2,1,2)],
`aoyagiTheta 3 2 = 3` [(2,2,2,2)] — by `decide`; plus `bandCount (ℓ,a) = aoyagiTheta (ℓ,a)` at each.

**Controller integration notes:** propose registering `bandCount_eq_aoyagiTheta` /
`thetaCount_eq_aoyagiTheta` as AxCheck roots (controller-only file); wire `OrderBinding` into the
aggregator (single-writer). Freeze the FINAL interpretive headline (`thetaCount = ρ`) only after the
controller's P6.2 signal.
