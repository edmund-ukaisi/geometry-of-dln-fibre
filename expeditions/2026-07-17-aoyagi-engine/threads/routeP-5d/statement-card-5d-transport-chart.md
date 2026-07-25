# Statement card — RUNG 5d crux (B): `transportChart` core + `permOf` calculus + `coreGen` K-equivariance

- **Status.** sorry-free, clean-three (force-elab verified). Two route-AGNOSTIC reusable modules,
  BANKED. The flat-(3,3,4)-fan transport APPLICATION is DEAD (sector-count exact: monomialization ⊥
  coverage — see below); both modules are banked for a **recursive-resolution route (#112)**, moot for
  the θ=1 bypass (#111) or the dead flat fan.
- **Modules.**
  - `lean/DLNFibre/DLN/Aoyagi/ChartTransport.lean` (~275 LoC, commit `2d8330538`) — generic transport.
  - `lean/DLNFibre/DLN/Aoyagi/Corank2CoreGenEquivar.lean` (commit `68385c86d`) — `coreGen` K-equivariance.
- **Lane branch.** `expedition/aoyagi-engine-5d-transport` (base `594b009c8`).
- **Axioms.** `#print axioms` (force-elab, olean deleted) = `[propext, Classical.choice, Quot.sound]`
  on `transportChart`, `permOf`, `measurePreserving_permOf`, `jacWeight_permOf`, `bindingAxes_comp_symm`,
  and `coreGen_permOf_kSigma`, `coreGen_comp_permOf_kSigma`, `kSigma`, `kTau`, `coreGen_eq_A1A0` —
  clean-three, no `sorryAx`.

## The `coreGen` K-equivariance (the rigorous gate)

`coreGen_permOf_kSigma` / `coreGen_comp_permOf_kSigma` — `coreGen dvec eWrap` is
equivariant-up-to-index-perm under `K = S₄(rows i) × S₃(cols j) × S₃(middle m)`, |K| = 864:
`coreGen k (permOf (kSigma α β ρ) u) = coreGen (kTau α β k) u`, with `kTau α β : (i,j) ↦ (α i, β j)`
(middle `ρ` = pure gauge, `π = id`). The `hequiv` that `transportChart` consumes. Built via the
transposed-product entry form `coreGen_eq_A1A0` + the layout equiv `kLayout` (`Equiv.ofBijective`,
`by decide`) + the product reindexing (shared `ρ` cancels in the contraction). Confirms sector-count's
tripwire: `kSigma` genuinely mixes the A0/A1 blocks via the shared `ρ`.

## The flat-fan death (V1 Gröbner check — decorrelated confirmation of sector-count)

Independent sympy check of `⟨coreGen ∘ (blockBlowupMap{0..7,20} p1 ∘ gFaithful)⟩` (local
monomialization = monomial-GCD in the ideal via a unit cofactor at `0`):
`p1=20` (chart334) MONOMIALIZES to `⟨u0·u20⟩` (unit cofactor entry 0 = 1, reproduces the banked
`⟨c11·E⟩` → harness validated); `p1=2` (distinct pivots) and `p1=0` (coinciding) do NOT monomialize
(monomial-GCD not locally in the ideal, no unit cofactor, min total degree 4). ⟹ the flat-fan COVERING
charts (`p1≠20`) do NOT admit chart334's principal-monomial hideal — confirms "monomialization ⊥
coverage": the resolution is intrinsically RECURSIVE (`buildTree`), chart334 = its column-0 terminal
branch. So the flat transport/atlas route is dead; `transportChart` + K-equivariance stay banked for the
recursive route.

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
