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

The explicit `(3,3,4)` `t=(1,0)` resolution chart, realising the FAITHFUL composite of the sympy
blueprint (`faithful_composite_tripwire.py`): the multi-term shear (Schur cross-term + the Lemma-2
recoord `C₂'=Q₂⁻¹C₂`) ∘ the radial `T=E·(1,t₂,t₃,t₄)` / `Δ=E·α·D̄` blow-ups ∘ the join `q=E, u=E·α`,
folded into ONE explicit polynomial map `ℝ²¹ → ℝ²¹`. The chart coordinates `u` are read as:
`E=u₀` (the dominant exceptional divisor), `α=u₁`, `(t₂,t₃,t₄)=(u₂,u₃,u₄)` (the `T`-row projective
coordinates), `(d₀₁,d₁₀,d₁₁)=(u₅,u₆,u₇)` (the `D̄`-block), `(c₀,c₁,c₂,c₃)=(u₈,u₉,u₁₀,u₁₁)` (the shear
coordinates — the `C₁`-coupling `c₁₂ₐ,c₁₂ᵦ,c₂₁ₐ,c₂₁ᵦ`, kept LIVE), `S=(u₁₂..u₁₉)` (the residual block),
`u₂₀` a spectator.

The output coordinates are chosen so that `peeled ∘ gFaithful` is `E`-factored (below): the shear
coordinates `x₀,x₁,x₂,x₃` stay free (`= c₀,c₁,c₂,c₃`), the residual `x₁₂..x₁₉` stays free (`= S`), and
the block-elim output coordinates `x₄..x₁₁` are SOLVED so that `Q₂⁻¹`'s coupling and the Schur
complement `Δ` compose to `E·(1,t₂,t₃,t₄)` on the `T`-row and `E·α·D̄` on the `Δ`-block. Faithfulness
(the coupling is genuinely present, not the diagonal confound) is witnessed by `delta_comp_coupled`. -/

/-- **The faithful composite chart map** `g = shear ∘ radial ∘ join`, `ℝ²¹ → ℝ²¹`, folded into one
explicit polynomial map (see the section docstring for the coordinate reading). -/
def gFaithful : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun u k ↦
  if k = 0 then u 8
  else if k = 1 then u 9
  else if k = 2 then u 10
  else if k = 3 then u 11
  else if k = 4 then u 0 * u 1 + u 8 * u 10
  else if k = 5 then u 0 * u 1 * u 5 + u 9 * u 10
  else if k = 6 then u 0 * u 1 * u 6 + u 8 * u 11
  else if k = 7 then u 0 * u 1 * u 7 + u 9 * u 11
  else if k = 8 then u 0 - u 8 * u 12 - u 9 * u 16
  else if k = 9 then u 0 * u 2 - u 8 * u 13 - u 9 * u 17
  else if k = 10 then u 0 * u 3 - u 8 * u 14 - u 9 * u 18
  else if k = 11 then u 0 * u 4 - u 8 * u 15 - u 9 * u 19
  else u k

/-- `gFaithful` is continuous (each output coordinate is a polynomial in the chart coordinates). -/
theorem continuous_gFaithful : Continuous gFaithful := by
  refine continuous_pi (fun k ↦ ?_)
  fin_cases k <;>
    (simp only [gFaithful, Fin.reduceFinMk, Fin.reduceEq, if_true, if_false] <;> fun_prop)

/-! ## The `E`-factorisation of `peeled ∘ gFaithful` (the concrete radial monomialisation)

`peeled = [T; Δ·S]` (`Corank2Proto.peeled`); the faithful `gFaithful` exposes every entry as
`E·(polynomial)`, `E = u₀`. The pivot entry `peeled₀₀∘g = E` EXACTLY (cofactor `1`, the reverse). The
quotient matrix `quotMat` records the 12 polynomial quotients (pivot `= 1`). -/

/-- The 12 divisibility quotients `quotMat i j` with `peeled i j ∘ gFaithful = E · quotMat i j`
(`E = u₀`). Row 0 is the `T`-row `(1, t₂, t₃, t₄) = (1, u₂, u₃, u₄)` (pivot quotient `1`); rows 1,2 are
`α·(D̄·S)` — the coupled `Δ`-block quotients, carrying `α = u₁`. -/
def quotMat : Matrix (Fin 3) (Fin 4) ((Fin 21 → ℝ) → ℝ) :=
  !![ (fun _ ↦ 1), (fun u ↦ u 2), (fun u ↦ u 3), (fun u ↦ u 4);
      (fun u ↦ u 1 * (u 12 + u 5 * u 16)), (fun u ↦ u 1 * (u 13 + u 5 * u 17)),
        (fun u ↦ u 1 * (u 14 + u 5 * u 18)), (fun u ↦ u 1 * (u 15 + u 5 * u 19));
      (fun u ↦ u 1 * (u 6 * u 12 + u 7 * u 16)), (fun u ↦ u 1 * (u 6 * u 13 + u 7 * u 17)),
        (fun u ↦ u 1 * (u 6 * u 14 + u 7 * u 18)), (fun u ↦ u 1 * (u 6 * u 15 + u 7 * u 19)) ]

/-- Each quotient `quotMat i j` is continuous (a polynomial in the chart coordinates). -/
theorem continuous_quotMat (i : Fin 3) (j : Fin 4) : Continuous (quotMat i j) := by
  fin_cases i <;> fin_cases j <;>
    (simp only [quotMat, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
      fun_prop)

set_option maxHeartbeats 1000000 in
/-- **The concrete `E`-factorisation** (the radial crux, matrix level): every entry of the coupled
block-elim output `peeled`, pulled back through the faithful chart `gFaithful`, is `E · quotMat i j`
with `E = u₀`. The pivot `(0,0)` has quotient `1`, so `peeled₀₀∘g = E` exactly. Proved by the explicit
`(3,3,4)` matrix computation: unfold the `diag(1,Δ)·(Q₂⁻¹·C₂)` product, evaluate `gFaithful`, `ring`. -/
theorem peeled_comp_gFaithful (i : Fin 3) (j : Fin 4) (u : Fin 21 → ℝ) :
    peeled (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc i j (gFaithful u)
      = u 0 * quotMat i j u := by
  fin_cases i <;> fin_cases j <;>
    simp [peeled, diag1Delta, Q2inv, C2conc, cc, quotMat, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_three, gFaithful] <;>
    ring

/-- **Faithfulness witness (not the diagonal confound).** On the chart, the Schur complement
`Δ ∘ gFaithful` is genuinely coupled: its off-diagonal `Δ₀₁ = m₁₂ − c₁₂ᵦ·c₂₁ₐ` pulls back to
`u₀·u₁·u₅` (via the LIVE shear coordinates), nonzero at a point — so `gFaithful` realises the FAITHFUL
multi-term shear (`Q₂⁻¹` non-trivial, `Δ` coupled), NOT the single-term `outerShear` proxy. -/
theorem delta_comp_coupled :
    ∃ u : Fin 21 → ℝ,
      Delta (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) 0 1 (gFaithful u) ≠ 0 := by
  refine ⟨fun k ↦ 1, ?_⟩
  simp only [Delta, cc, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Pi.sub_apply, Pi.mul_apply, gFaithful]
  norm_num [gFaithful, Fin.ext_iff]

/-- The dominant terminal exceptional monomial `b₁ = E` (here coord `0`), in `monomialFam` (`Fin 1`) form.
Builder pins the exponent vector to the join's `E`-coordinate. -/
def bexpE : Fin 1 → Fin 21 → ℕ := fun _ d ↦ if d = 0 then 1 else 0

/-- `monomialFam bexpE` is the single dominant monomial `E = u₀`. -/
theorem monomialFam_bexpE (k : Fin 1) (u : Fin 21 → ℝ) : monomialFam bexpE k u = u 0 := by
  simp only [monomialFam, bexpE]
  rw [Finset.prod_eq_single (0 : Fin 21)]
  · simp
  · intro d _ hd; simp [hd]
  · intro h; exact absurd (Finset.mem_univ _) h

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
  refine ⟨?_, ?_⟩
  · -- fwd: `peeled∘g` divides into `E`, cofactor the polynomial quotient `quotMat`
    refine ⟨fun i _ ↦ quotMat (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2,
      fun i _ ↦ (continuous_quotMat _ _).continuousOn, ?_⟩
    intro u _ i
    rw [Fin.sum_univ_one, monomialFam_bexpE]
    simp only [Function.comp_apply, flat]
    rw [peeled_comp_gFaithful]
    ring
  · -- bwd: `E` is exactly the cleared-pivot entry `peeled₀₀∘g` (cofactor `1` at the pivot, `0` else)
    refine ⟨fun _ j ↦ (fun _ ↦ if j = finProdFinEquiv ((0 : Fin 3), (0 : Fin 4)) then (1 : ℝ) else 0),
      fun _ _ ↦ continuousOn_const, ?_⟩
    intro u _ i
    rw [monomialFam_bexpE,
      Finset.sum_eq_single (finProdFinEquiv ((0 : Fin 3), (0 : Fin 4)))
        (fun j _ hj ↦ by simp [hj]) (fun h ↦ absurd (Finset.mem_univ _) h)]
    simp only [Function.comp_apply, flat, Equiv.symm_apply_apply, if_pos, one_mul]
    rw [peeled_comp_gFaithful]
    simp [quotMat]

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
