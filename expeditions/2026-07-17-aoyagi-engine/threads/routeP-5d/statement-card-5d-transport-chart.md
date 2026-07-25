# Statement card — RUNG 5d crux (B): the generic `transportChart` core + `permOf` calculus

- **Status.** sorry-free, clean-three (force-elab verified). Route-agnostic reusable core. The (3,3,4)
  leaf-Chart FAMILY / wiring is HELD pending the sector-count θ adjudication (per controller).
- **Module.** `lean/DLNFibre/DLN/Aoyagi/ChartTransport.lean` (new, ~270 LoC).
- **Lane branch.** `expedition/aoyagi-engine-5d-transport` (base `594b009c8`).
- **Axioms.** `#print axioms` (force-elab, olean deleted) = `[propext, Classical.choice, Quot.sound]`
  on `transportChart`, `permOf`, `measurePreserving_permOf`, `jacWeight_permOf`,
  `bindingAxes_comp_symm` — clean-three, no `sorryAx`.

## What LANDED (buildable, banked)

**`transportChart σ τ hequiv chart : Chart F (permOf σ.symm x₀)`** — the generic crux-(B) core.
Given a certified `Chart F x₀`, a coordinate permutation `σ : Equiv.Perm (Fin D)`, an index
permutation `τ : Equiv.Perm (Fin M)`, and the **equivariance-up-to-index-perm**
`hequiv : ∀ i, F i ∘ permOf σ = F (τ i)`, produces a certified `Chart F` for the conjugated map
`g' = permOf σ.symm ∘ g ∘ permOf σ`, resolving the SAME family `F`. All 5 certificate groups transport:

| field group | how it transports |
|---|---|
| `hg0`/`hg_cont`/`hg_analytic` | `permOf` is a linear homeo fixing `0` (`permCLM`) |
| `hjac` | `jacDet_comp` + `abs_jacDet_permOf`=1 ⟹ `\|jacDet g'\| = \|jacDet g ∘ permOf σ\|`; `jac' = jac ∘ σ.symm` (values preserved, axes permuted) |
| `hg_inj`/`hexcep` | `permOf` measure-preserving bijection (`measurePreserving_permOf` via `piCongrLeft`); `excep' = (permOf σ)⁻¹' excep` |
| `hideal_fwd`/`hideal_bwd` | cofactors conjugate along `σ`, consuming `hequiv`; `bexp' = bexp ∘ σ.symm` |
| `hchain`/`hbind`/`hunit_mult` | binding axes map by `σ` (`bindingAxes_comp_symm`), values preserved |

**Supporting `permOf` calculus** (reusable engine material): `permOf`, `permOf_zero`,
`permOf_symm_permOf`/`permOf_permOf_symm` (inverse), `continuous`/`analytic`/`differentiable`/
`measurable`/`injective_permOf`, `abs_jacDet_permOf` (reuses banked `abs_jacDet_permCoord`),
`measurePreserving_permOf`, `permOf_preimage_eq_image`, `jacWeight_permOf`, `monomialFam_permOf`,
`bindingAxes_comp_symm`.

## The load-bearing hypothesis (the gate — RESOLVED)

`hequiv : ∀ i, F i ∘ permOf σ = F (τ i)` is crux (B)'s analogue of crux (A). For the DLN application it
is `coreGen dvec eWrap`'s **K-equivariance**: VERIFIED (numeric, all 864 elements) that `coreGen` is
equivariant-up-to-index-perm under `K = S₄(rows i) × S₃(cols j) × S₃(middle m)`, |K| = 864, with
`π_σ : (i,j) ↦ (α i, β j)` (middle-m acts as gauge, π = id). The rigorous Lean `coreGen` K-equivariance
is a HELD follow-up (route-agnostic, reusable) — build gated on controller direction.

## The strategic finding (why transport alone does NOT close 5d)

**Transport charts move the blow-up CENTERS; decomp-5b's fan keeps them FIXED.**
`g' = permOf σ.symm ∘ gWrap ∘ permOf σ` conjugates the WHOLE composite, so each `blockBlowupMap S p`
becomes `blockBlowupMap (σ.symm '' S) (σ.symm p)`. The 3 nested centers `{0..7,20}`, `{0..7}`,
`{1,5,6,7}` are NOT K-invariant (verified: center2, center3 move under both the gauge and col-swaps).
So for EVERY non-identity `σ ∈ K`, the transport chart's `g'` differs from decomp-5b's fixed-center
leaf composite `blockBlowupMap {0..7,20} p1 ∘ (shearH∘permP) ∘ blockBlowupMap {0..7} p2 ∘
blockBlowupMap {1,5,6,7} p3` for the SAME pivot-triple. Consequence:

- Transport charts feed a **G-orbit cover** (moved centers) — which needs `orbit_covers` (the (ii)
  kill-condition), NOT decomp-5b's banked fixed-center cover.
- Closing 5d against decomp-5b's cover needs **chartAtPivot-generic** (fixed-center, hideal re-proven
  per pivot-triple). Transport does NOT shortcut it.

## Structural-hideal assessment (bounded, per controller)

Is a STRUCTURAL pivot-generic hideal (not brute-force `fin_cases;ring`) in reach? **NO, not obviously.**
The obstruction is the **tuned shear**: `gFaithful = shearH∘permP∘bbA0∘bbA1` with `shearH`'s bilinear
cross-terms hand-tuned to clear the CANONICAL pivots. Transport works WITHIN a K-orbit precisely
because conjugation adapts the shear too; the fixed-shear fan across pivots has an UN-adapted shear, so
each K-orbit needs its own shear-adapted (brute-force) monomialisation → 25 orbits = the general-`d`
MONUMENT if done for all. Confirms routeP-p1's mechanism read + the controller's "it's the monument".
**Path:** θ-prune (sector-count) the orbits, then a few fixed-center per-orbit hideals; transport-core
stays as the reusable within-orbit tool + the rigorous gate.

## Fidelity questions for review

(a) Is `transportChart` a faithful transport — every `Chart` field the honest conjugate, `hideal`
cofactors correctly conjugated via `hequiv`, no field weakened? (b) Is `measurePreserving_permOf`
sound (the `piCongrLeft` bridge)? (c) Is the "moved centers" finding correct (transport ≠ fixed-center
fan)?
