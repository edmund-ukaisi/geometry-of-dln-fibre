import DLNFibre.Core.Aoyagi.Corank2CompositeProto
import DLNFibre.Core.Aoyagi.Corank2TerminalProto
import DLNFibre.Core.Aoyagi.BlockBlowup

/-!
# `Core.Aoyagi.Corank2FaithfulComposite` — #112 PHASE-1 SCAFFOLD (the faithful (3,3,4) composite chart)

**SCAFFOLD — laid by `gate2-hideal`; the RADIAL CRUX is a tracked `sorry` for the grind builder.**
This is the skeleton of the END-TO-END gate (route P, #112 Phase-1): the SELF-CONTAINED faithful (3,3,4)
`t=(1,0)` composite chart `g` + its two-sided `hideal`, composing the three PROVEN recursion mechanisms:
- **L-A** block-elim (`Corank2HidealProto.blockElim_step_fwd`/`_bwd`, over the genuinely coupled `Δ`),
- **L-B** maintenance (`Corank2MaintenanceProto.maintenance_step_two_sided`, the b-chain reverse),
- **L-C** terminal (`Corank2TerminalProto` via `terminal_bezout`, reverse `1/unit`),
composed via the precompose primitive `Corank2CompositeProto.regionRepresents_comp` + the banked
`RegionRepresents.trans`.

## What is PINNED here (scaffold) vs the CRUX (builder)

- **PINNED:** the composition STRUCTURE — `gFaithful = shear ∘ radial ∘ join` (the faithful multi-term
  shape); the chain skeleton `⟨(∏C)∘g⟩ =[L-A ∘ g]= ⟨peeled∘g⟩ =[CRUX]= ⟨monomialFam bexpE⟩`, both
  directions, wired below; and the reverse riding `terminal_bezout` (`1/unit`, coupling-independent).
- **THE CRUX (tracked `sorry`, `crux_radial_monomialise`):** the concrete radial factorisation of the
  12-entry COUPLED `peeled∘g` to `⟨E⟩` — `L-C was proven on an ABSTRACT residual block
  (`Corank2TerminalProto`); the concrete faithful application to the specific `peeled` (built by the
  explicit faithful `g` exposing `peeled`'s entries as the monomialisable block) is Phase-1's real work.
  **Math-GREEN** (the `#124` pivot-survival tripwire passes — see
  `expeditions/2026-07-17-aoyagi-engine/gate3-codex/faithful_composite_tripwire.py`, run it), NOT a wall,
  NOT free wiring.

## Builder handoff (grind the crux)

1. **Finalise `gFaithful`'s components** (`shFaithful`/`radialFaithful`/`joinFaithful` below are the typed
   STRUCTURE with placeholder concrete values — pin them to the sympy blueprint's faithful multi-term
   shear (Schur cross-term + `C₂'=Q₂⁻¹C₂` recoord) + the radial `T=q·(1,t2,t3,t4)` / `Δ=u·Dbar` blow-ups +
   the join `q=E, u=E·α`). GUARD: faithful multi-term, NO single-term `outerShear` proxy (false-GREEN,
   rev-render #7).
2. **Prove `crux_radial_monomialise`** for the finalised `gFaithful` (+ the chart region `nbhd`): the
   forward `E ∣ every peeled∘g entry` (polynomial quotients) + one pivot entry `= E·unit` (`unit 0 ≠ 0`);
   the reverse is then `terminal_bezout`. Watch the `#124` tripwire. STOP + report on a genuine 21-var
   Mathlib wall.
3. **Connect `coreGen (3,3,4) e ∘ g`** to `flat(C1·C2)∘g` (the part-C flatten: `mult`-unfold `rfl`-cheap,
   the flatten HMul tax has CLAUDE.md mitigations) — the scaffold states the chain at the `flat(Pmat)`
   product-entry level (= `coreGen` content up to flatten/transpose); wrap it to `coreGen`.
-/

open Matrix Set
open DLNFibre.Core.Aoyagi DLNFibre.Core.Aoyagi.Corank2Proto DLNFibre.Core.Aoyagi.Corank2HidealProto
open DLNFibre.Core.Aoyagi.Corank2CompositeProto

namespace DLNFibre.Core.Aoyagi.Corank2FaithfulComposite

/-! ## The faithful composite chart map `gFaithful` (multi-term shear ∘ radial ∘ join)

STRUCTURE pinned; the component maps carry placeholder concrete values (banked `blockBlowupMap` for the
blow-ups) for the builder to finalise to the sympy blueprint. The composition order (shear outermost,
then radial, then join) is the faithful order. -/

/-- The faithful multi-term shear component (Schur cross-term + the `C₂'=Q₂⁻¹C₂` recoord). SCAFFOLD:
typed as a continuous origin-fixing self-map; the builder pins the exact linear entries (banked
`blockShear` idiom). Placeholder `id` keeps the scaffold buildable; it is NOT the faithful shear — the
builder replaces it (a `blockShear φ` with the (3,3,4) displacement). -/
def shFaithful : (Fin 21 → ℝ) → (Fin 21 → ℝ) := id

/-- The radial `T`/`ΔS` blow-up component. SCAFFOLD placeholder (`blockBlowupMap univ 0` monomialises a
block via the pivot); the builder pins the centers/pivot to the `T=q·(1,…)` / `Δ=u·Dbar` blow-ups. -/
def radialFaithful : (Fin 21 → ℝ) → (Fin 21 → ℝ) := blockBlowupMap Finset.univ 0

/-- The join component (`q=E, u=E·α`, blow up `{q=u=0}`). SCAFFOLD placeholder; builder pins it. -/
def joinFaithful : (Fin 21 → ℝ) → (Fin 21 → ℝ) := blockBlowupMap Finset.univ 0

/-- **The faithful composite chart map** `g = shear ∘ radial ∘ join`, `ℝ²¹ → ℝ²¹`. STRUCTURE pinned;
components to finalise (builder). -/
def gFaithful : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  shFaithful ∘ radialFaithful ∘ joinFaithful

/-- `gFaithful` is continuous (composite of continuous components). -/
theorem continuous_gFaithful : Continuous gFaithful := by
  refine Continuous.comp ?_ (Continuous.comp ?_ ?_)
  · exact continuous_id
  · exact continuous_blockBlowupMap _ _
  · exact continuous_blockBlowupMap _ _

/-- The dominant terminal exceptional monomial `b₁ = E` (here coord `0`), in `monomialFam` (`Fin 1`) form.
Builder pins the exponent vector to the join's `E`-coordinate. -/
def bexpE : Fin 1 → Fin 21 → ℕ := fun _ d ↦ if d = 0 then 1 else 0

/-! ## THE RADIAL CRUX — tracked `sorry`, precise statement -/

/-- **THE CRUX (`-- map: #112-phase1-radial`).** The concrete radial factorisation of the 12-entry
COUPLED `peeled∘gFaithful` to the single dominant monomial `⟨E⟩`, BOTH directions, on the chart region
`nbhd`:
- **fwd** `⟨peeled∘g⟩ ⊆ ⟨monomialFam bexpE⟩` — every pulled-back `peeled` entry is `E·(polynomial)`;
- **bwd** `⟨monomialFam bexpE⟩ ⊆ ⟨peeled∘g⟩` — `E` recovered from the cleared-pivot entry (`E·unit`,
  `unit 0 ≠ 0`), cofactor `1/unit` (this half IS `terminal_bezout`, proven — the builder supplies its
  hypotheses for the finalised `g`).
Math-GREEN via the `#124` pivot-survival tripwire (`faithful_composite_tripwire.py`); the concrete
construction (the explicit faithful `g` making `peeled∘g = E·q`) is Phase-1's grind. -/
theorem crux_radial_monomialise (nbhd : Set (Fin 21 → ℝ)) :
    RegionRepresents
      (fun i ↦ flat (peeled (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc) i
        ∘ gFaithful) (monomialFam bexpE) nbhd ∧
    RegionRepresents (monomialFam bexpE)
      (fun i ↦ flat (peeled (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc) i
        ∘ gFaithful) nbhd := by
  sorry

/-! ## The chain skeleton — `hideal` (product-entry level) from L-A ∘ g `.trans` the crux

`⟨(∏C)∘g⟩ =[L-A block-elim ∘ g, via regionRepresents_comp]= ⟨peeled∘g⟩ =[CRUX]= ⟨monomialFam bexpE⟩`,
both directions. Stated at the `flat(Pmat)` product-entry level; builder wraps to `coreGen (3,3,4) e`. -/

/-- **`hideal_fwd` skeleton** — `⟨(∏C)∘g⟩ ⊆ ⟨monomialFam bexpE⟩` on `nbhd ⊆ univ`, via L-A block-elim
precomposed with `g` (`regionRepresents_comp`) `.trans` the crux (fwd). -/
theorem hideal_faithful_fwd (nbhd : Set (Fin 21 → ℝ)) (hsub : nbhd ⊆ gFaithful ⁻¹' Set.univ) :
    RegionRepresents
      (fun i ↦ flat (Pmat (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc) i
        ∘ gFaithful) (monomialFam bexpE) nbhd :=
  ((regionRepresents_comp (blockElim_step_fwd Set.univ) continuous_gFaithful).mono hsub).trans
    (crux_radial_monomialise nbhd).1

/-- **`hideal_bwd` skeleton** — `⟨monomialFam bexpE⟩ ⊆ ⟨(∏C)∘g⟩` on `nbhd`, via the crux (bwd) `.trans`
the L-A block-elim (bwd) precomposed with `g`. -/
theorem hideal_faithful_bwd (nbhd : Set (Fin 21 → ℝ)) (hsub : nbhd ⊆ gFaithful ⁻¹' Set.univ) :
    RegionRepresents (monomialFam bexpE)
      (fun i ↦ flat (Pmat (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc) i
        ∘ gFaithful) nbhd :=
  (crux_radial_monomialise nbhd).2.trans
    ((regionRepresents_comp (blockElim_step_bwd Set.univ) continuous_gFaithful).mono hsub)

end DLNFibre.Core.Aoyagi.Corank2FaithfulComposite
