import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import DLNFibre.DLN.RLCT.Foundations.S1NonMPTransport
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestRegAbsorbIFT` — PIN 1's `regAbsorb_rlct` reduction (#44c)

PIN 1 of the L2 gauge-chart assembly (`deepest_regAbsorb_exists`) bundles the regular-slot
absorption `regAbsorb` with the RLCT-peel conjunct

    rlctAtOn (fun q => ∑ (regAbsorb q).1² + deepestCoreF (coreAbsorb q).2.1) 0
      = rlctAtOn (fun q => ∑ q.1²         + deepestCoreF (coreAbsorb q).2.1) 0.

This file isolates the **structure-independent heart** of that conjunct: a reduction lemma that
peels the regular substitution `regAbsorb` PAST the coupled core term `deepestCoreF (coreAbsorb
q).2.1`, turning the COUPLED equality into the DECOUPLED #72 peel of `regAbsorb` against a core
term that no longer mentions `coreAbsorb`.

## The coupling and its resolution (the key observation)

The two sides share the core term `deepestCoreF (coreAbsorb q).2.1`, which (since `coreAbsorb` is
the shear `coreShearHomeo shift`, reading the regular slot) DEPENDS on `q.1`. So a direct #72 peel
with `π = regAbsorb` does NOT close it: `(RHS-integrand) ∘ regAbsorb` carries `coreAbsorb (regAbsorb
q)`, not `coreAbsorb q`. The fix is to first change variables by the MEASURE-PRESERVING
`coreAbsorb.symm` (RLCT-invariant, `rlctAtOn_comp_homeomorph`), which collapses the core term to
`deepestCoreF q.2.1` (no `coreAbsorb`) on BOTH sides — because `coreAbsorb.symm` fixes the regular
and spectator slots (so `regAbsorb`'s regular output, which reads only reg+spec, is unchanged), and
`coreAbsorb ∘ coreAbsorb.symm = id` clears the core composition. The decoupled core term is then
independent of the regular slot, so the #72 peel of `regAbsorb` (a reg-slice local diffeo fixing the
core slot) applies cleanly.

This reduction needs ONLY abstract properties of `coreAbsorb` (measure-preserving, fixes reg + spec
+ origin) and of `regAbsorb` (fixes the core slot; its regular output depends only on the reg + spec
input). It is independent of the concrete Schur `shift` and of the concrete `E`-straightening `Ψ`.
The remaining genuinely-analytic atom — the decoupled peel `rlctAtOn (G ∘ regAbsorb) 0 = rlctAtOn G
0` — is supplied as a hypothesis (discharged by the implicit-function-theorem `Ψ` + its
bounded-unit Jacobian via `rlctAtOn_boundedUnit_localHomeomorph`, which needs the concrete `E` map).
-/

open MeasureTheory
open scoped ENNReal BigOperators Topology

namespace DLNFibre.DLN.RLCT

/-! ## The structure-independent reduction

Abstract over the three slot types `R` (regular), `C` (core), `S` (spectator) of a split product
`R × (C × S)` (the `DeepestSplit` shape). The reduction transports the regular substitution past the
core term using the measure-preserving conjugation by `coreAbsorb.symm`. -/

section SlotFix
variable {R C S : Type*} [TopologicalSpace R] [TopologicalSpace C] [TopologicalSpace S]

/-- `coreAbsorb.symm` fixes the regular slot, inherited from `coreAbsorb` fixing it: applying
`coreAbsorb_regular` at `coreAbsorb.symm q` and using `coreAbsorb (coreAbsorb.symm q) = q`. -/
theorem symm_fixes_fst (coreAbsorb : (R × (C × S)) ≃ₜ (R × (C × S)))
    (hca_reg : ∀ q, (coreAbsorb q).1 = q.1) (q : R × (C × S)) :
    (coreAbsorb.symm q).1 = q.1 := by
  have h := hca_reg (coreAbsorb.symm q)
  rw [coreAbsorb.apply_symm_apply] at h
  exact h.symm

/-- `coreAbsorb.symm` fixes the spectator slot (same inheritance as `symm_fixes_fst`). -/
theorem symm_fixes_spec (coreAbsorb : (R × (C × S)) ≃ₜ (R × (C × S)))
    (hca_spec : ∀ q, (coreAbsorb q).2.2 = q.2.2) (q : R × (C × S)) :
    (coreAbsorb.symm q).2.2 = q.2.2 := by
  have h := hca_spec (coreAbsorb.symm q)
  rw [coreAbsorb.apply_symm_apply] at h
  exact h.symm

end SlotFix

variable {R C S : Type*}
  [NormedAddCommGroup R] [NormedSpace ℝ R] [MeasureSpace R] [BorelSpace R]
  [FiniteDimensional ℝ R] [(volume : Measure R).IsAddHaarMeasure]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasureSpace C] [BorelSpace C]
  [FiniteDimensional ℝ C] [(volume : Measure C).IsAddHaarMeasure]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [MeasureSpace S] [BorelSpace S]
  [FiniteDimensional ℝ S] [(volume : Measure S).IsAddHaarMeasure]

omit [NormedSpace ℝ R] [FiniteDimensional ℝ R] [(volume : Measure R).IsAddHaarMeasure]
  [(volume : Measure C).IsAddHaarMeasure] [(volume : Measure S).IsAddHaarMeasure] in
/-- **The reg-absorption RLCT reduction** (PIN 1's heart, structure-independent). Given a
measure-preserving `coreAbsorb` fixing the regular + spectator slots and the origin, and a regular
substitution `regAbsorb` fixing the core slot whose regular output reads only the reg + spectator
input, the coupled RLCT equality

    rlctAtOn (fun q => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
      = rlctAtOn (fun q => regF q.1 + coreF (coreAbsorb q).2.1) 0

REDUCES to the decoupled `regAbsorb`-peel

    rlctAtOn (fun q => regF (regAbsorb q).1 + coreF q.2.1) 0
      = rlctAtOn (fun q => regF q.1 + coreF q.2.1) 0

(the core term stripped of `coreAbsorb`). The decoupled peel is the #72 application (the IFT `Ψ` +
its bounded-unit Jacobian); this lemma supplies the conjugation that removes `coreAbsorb` from core
term on both sides. -/
theorem rlctAtOn_regAbsorb_reduce
    (coreAbsorb : (R × (C × S)) ≃ₜ (R × (C × S)))
    (regAbsorb : (R × (C × S)) → (R × (C × S)))
    (regF : R → ℝ) (coreF : C → ℝ)
    (hca_mp : MeasurePreserving coreAbsorb volume volume)
    (hca_base : coreAbsorb 0 = 0)
    (hca_reg : ∀ q, (coreAbsorb q).1 = q.1)
    (hca_spec : ∀ q, (coreAbsorb q).2.2 = q.2.2)
    (hra_regdep : ∀ q q' : R × (C × S), q.1 = q'.1 → q.2.2 = q'.2.2 →
      (regAbsorb q).1 = (regAbsorb q').1)
    (hpeel :
      rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF q.2.1) 0
        = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0) :
    rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0 := by
  -- The measure-preserving conjugation by `coreAbsorb.symm`.
  have hsymm_mp : MeasurePreserving (⇑coreAbsorb.symm) volume volume :=
    hca_mp.symm coreAbsorb.toMeasurableEquiv
  have hsymm_emb : MeasurableEmbedding (⇑coreAbsorb.symm) := coreAbsorb.symm.measurableEmbedding
  have hsymm_base : coreAbsorb.symm 0 = 0 := by
    conv_lhs => rw [← hca_base]
    rw [coreAbsorb.symm_apply_apply]
  -- LHS: change variables by `coreAbsorb.symm`; the core term collapses to `coreF q.2.1`.
  have hL : rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
      = rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF q.2.1) 0 := by
    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
      (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
    rw [hsymm_base] at hstep
    -- `(fun q => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) ∘ coreAbsorb.symm`
    --   = `fun q => regF (regAbsorb q).1 + coreF q.2.1`.
    have hfun : (fun q : R × (C × S) =>
          regF (regAbsorb (coreAbsorb.symm q)).1 + coreF (coreAbsorb (coreAbsorb.symm q)).2.1)
        = fun q : R × (C × S) => regF (regAbsorb q).1 + coreF q.2.1 := by
      funext q
      have hcore : (coreAbsorb (coreAbsorb.symm q)).2.1 = q.2.1 := by
        rw [coreAbsorb.apply_symm_apply]
      have hreg : (regAbsorb (coreAbsorb.symm q)).1 = (regAbsorb q).1 :=
        hra_regdep _ _ (symm_fixes_fst coreAbsorb hca_reg q)
          (symm_fixes_spec coreAbsorb hca_spec q)
      rw [hcore, hreg]
    rw [hfun] at hstep
    exact hstep.symm
  -- RHS: same conjugation; the core term collapses, the regular term is untouched.
  have hR : rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0
      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0 := by
    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
      (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0
    rw [hsymm_base] at hstep
    have hfun : (fun q : R × (C × S) =>
          regF (coreAbsorb.symm q).1 + coreF (coreAbsorb (coreAbsorb.symm q)).2.1)
        = fun q : R × (C × S) => regF q.1 + coreF q.2.1 := by
      funext q
      have hcore : (coreAbsorb (coreAbsorb.symm q)).2.1 = q.2.1 := by
        rw [coreAbsorb.apply_symm_apply]
      have hreg : (coreAbsorb.symm q).1 = q.1 := symm_fixes_fst coreAbsorb hca_reg q
      rw [hcore, hreg]
    rw [hfun] at hstep
    exact hstep.symm
  rw [hL, hR, hpeel]

end DLNFibre.DLN.RLCT
