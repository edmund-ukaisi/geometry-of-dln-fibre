import DLNFibre.Core.Aoyagi.PathAtoms
import DLNFibre.Core.Aoyagi.BlockBlowup
import DLNFibre.DLN.Aoyagi.Corank2ChartJac

/-!
# M2 — the pivot-generic step constructor + born-siblings (completes R1)

The reroute's main constructive rung: a single, pivot-generic step constructor that emits, PER
PIVOT,
a certified child — the geometry born inside the constructor (guardrail-0), never transported. All
work is in the FIXED full space `Fin N → ℝ` (`Params M`; no dimension drop — R3-derisk design
constraint).

The elder's two acceptance criteria, met as THEOREMS (not "built green"):

1. **GUARDRAIL-0 = a per-emitted-step theorem, discharged from block structure.** Every clearing the
   constructor emits is bundled as a `CleanClearing`: a `blockShear φ` whose displacement `φ`
VANISHES
   on the kept coords (touches only the residual/cleared block) and READS only the kept coords. From
   these two fields `CleanClearing.jacDet_shear` DISCHARGES `jacDet (blockShear φ) = 1` per step
   (via
   `jacDet_blockShear`) — the shearH_eq analogue reproduced generically. A step CANNOT be emitted
   without this cert (it is a *field* of `PivotStep`), so the "no geometry outside the constructor
with
   a proven-clean clearing" guarantee is structural, not a threaded prose hypothesis.

2. **BORN-SIBLINGS = per-sibling certificates.** `bornSiblings` produces ONE `PivotStep` per pivot
   `p ∈ Z`; EACH independently carries its own `CleanClearing` (guardrail-0) and its own per-step
   Jacobian cert `|jacDet stepMap| = |u_p|^(|Z|−1)` (`bornSiblings_certified`). The siblings share
the
   node's clearing and differ only in the blow-up pivot `p` (pivot-independence), each BORN from
that
   pivot — never one transported to the others.

The corank-2 REAL clearing is a genuine instance: `clearing334 : CleanClearing 21` from the banked
`shearPhiH` (`clearing334_shear_eq_shearH` : its shear IS the real `shearH`), and
`bornSiblings334_certified` exhibits the (3,3,4) sibling family (pivots `{0,1}`), each certified.

**Scope (honest).** This is the per-step constructor + born-siblings (LOCAL, completes R1). The
recursion that THREADS these per-step facts (geometry + both `RegionRepresents` + cover-inflation)
through `conRel_wf` is R3 — the next monument. The ideal-side `Hchain` (b-chain) is threaded there;
the geometry `hjac` cert here is coupling/chain-independent (`jacDet_blockShear` is content-blind).

## Main results
- `CleanClearing` + `CleanClearing.jacDet_shear` — guardrail-0: the emitted clearing is a unipotent
  reads-only-kept blockShear, discharged per step.
- `PivotStep` + `PivotStep.abs_jacDet_stepMap` — one pivot-born step; its Jacobian
  `|jacDet| = |u_p|^(|Z|−1)`.
- `bornSiblings` + `bornSiblings_certified` — the per-pivot sibling family, each certified.
- `clearing334` / `clearing334_shear_eq_shearH` / `bornSiblings334_certified` — the corank-2 real
  instance + its certified (3,3,4) sibling family.
-/

open DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi.StepConstructor

variable {N : ℕ}

/-- A blow-up map is differentiable (from its `HasFDerivAt`). -/
private theorem diff_blockBlowup (S : Finset (Fin N)) (p : Fin N) :
    Differentiable ℝ (blockBlowupMap S p) :=
  fun w ↦ (hasFDerivAt_blockBlowupMap S p w).differentiableAt

/-! ## 1. `CleanClearing` — guardrail-0 bundled: a reads-only-kept blockShear + its discharged cert
-/

/-- A **clean clearing** — the geometry the step constructor may emit: a `blockShear φ` whose
displacement `φ` is differentiable, VANISHES on the kept coords (touches only the residual/cleared
block), and READS only the kept coords. Bundling these fields makes guardrail-0 STRUCTURAL: a
clearing
cannot exist without them. -/
structure CleanClearing (N : ℕ) where
  φ : (Fin N → ℝ) → (Fin N → ℝ)
  keep : Fin N → Prop
  hdiff : Differentiable ℝ φ
  hkeep : ∀ u i, keep i → φ u i = 0
  hread : ∀ u v : Fin N → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v

/-- The clearing map: the unipotent block shear `id + φ`. -/
def CleanClearing.shear (c : CleanClearing N) : (Fin N → ℝ) → (Fin N → ℝ) := blockShear c.φ

/-- The clearing is differentiable. -/
theorem CleanClearing.diff_shear (c : CleanClearing N) : Differentiable ℝ c.shear := by
  unfold CleanClearing.shear blockShear; exact differentiable_id.add c.hdiff

/-- **GUARDRAIL-0 (per-emitted-step theorem, DISCHARGED from block structure).** The clearing the
constructor emits is unipotent: `jacDet (c.shear) u = 1` — proved from `c`'s reads-only-kept +
vanishes-on-kept fields via `jacDet_blockShear`, NOT assumed. -/
theorem CleanClearing.jacDet_shear (c : CleanClearing N) (u : Fin N → ℝ) :
    jacDet c.shear u = 1 :=
  jacDet_blockShear c.φ c.keep c.hdiff c.hkeep c.hread u

/-- A kept coord is fixed by the clearing (the shear touches only the cleared block). -/
theorem CleanClearing.shear_keep (c : CleanClearing N) {p : Fin N} (hp : c.keep p)
    (u : Fin N → ℝ) : c.shear u p = u p := by
  simp only [CleanClearing.shear, blockShear, Pi.add_apply, c.hkeep u p hp, add_zero]

/-! ## 2. `PivotStep` — one pivot-born step (blow-up at the pivot ∘ the clean clearing) -/

/-- A **pivot step**: the geometry born at pivot `p` — the block blow-up `blockBlowupMap center p`
composed with the node's clean clearing. The clearing cert is a FIELD (guardrail-0 structural); the
pivot is a kept coord (`hpivot_keep`, so the blow-up sees the original pivot coordinate). -/
structure PivotStep (N : ℕ) where
  pivot : Fin N
  center : Finset (Fin N)
  hmem : pivot ∈ center
  clearing : CleanClearing N
  hpivot_keep : clearing.keep pivot

/-- The step map: blow-up at the pivot, outermost, over the clean clearing. -/
def PivotStep.stepMap (s : PivotStep N) : (Fin N → ℝ) → (Fin N → ℝ) :=
  blockBlowupMap s.center s.pivot ∘ s.clearing.shear

/-- **Per-step Jacobian cert.** `|jacDet stepMap u| = |u_pivot|^(|center|−1)` — a PURE monomial in
the
pivot coordinate: the clearing contributes `1` (guardrail-0, `jacDet_shear`) and the blow-up the
exact monomial (`jacDet_blockBlowupMap`). Discharged per emitted step. -/
theorem PivotStep.abs_jacDet_stepMap (s : PivotStep N) (u : Fin N → ℝ) :
    |jacDet s.stepMap u| = |u s.pivot| ^ (s.center.card - 1) := by
  rw [PivotStep.stepMap,
    jacDet_comp u (diff_blockBlowup s.center s.pivot).differentiableAt
      s.clearing.diff_shear.differentiableAt,
    jacDet_blockBlowupMap s.hmem, s.clearing.jacDet_shear, mul_one,
    s.clearing.shear_keep s.hpivot_keep, abs_pow]

/-! ## 3. `bornSiblings` — the per-pivot family, each independently certified (no transport) -/

/-- **Born-siblings.** For a center `Z` and a node clearing `c` (kept at every pivot of `Z`), the
constructor emits ONE `PivotStep` per pivot `p ∈ Z`, each BORN at `p` (its own blow-up), sharing the
node clearing — never transported. -/
def bornSiblings (Z : Finset (Fin N)) (c : CleanClearing N) (hkeep : ∀ p ∈ Z, c.keep p) :
    (p : Fin N) → p ∈ Z → PivotStep N :=
  fun p hp ↦ { pivot := p, center := Z, hmem := hp, clearing := c, hpivot_keep := hkeep p hp }

/-- **Each born sibling independently carries its certificates** — guardrail-0 (its clearing is a
unipotent reads-only-kept blockShear) AND its per-step Jacobian cert (`|jacDet| = |u_p|^(|Z|−1)`).
One per pivot, born from that pivot; NOT "produced N children green". -/
theorem bornSiblings_certified (Z : Finset (Fin N)) (c : CleanClearing N)
    (hkeep : ∀ p ∈ Z, c.keep p) (p : Fin N) (hp : p ∈ Z) (u : Fin N → ℝ) :
    jacDet (bornSiblings Z c hkeep p hp).clearing.shear u = 1 ∧
      |jacDet (bornSiblings Z c hkeep p hp).stepMap u| = |u p| ^ (Z.card - 1) :=
  ⟨(bornSiblings Z c hkeep p hp).clearing.jacDet_shear u,
    (bornSiblings Z c hkeep p hp).abs_jacDet_stepMap u⟩

/-! ## 4. The corank-2 REAL instance — the (3,3,4) clearing as a `CleanClearing` + its sibling
family -/

/-- The REAL (3,3,4) coupled clearing, packaged as a `CleanClearing` (guardrail-0 met by the actual
clearing): `φ = shearPhiH`, all fields the banked `Corank2ChartJac` facts. -/
def clearing334 : CleanClearing 21 where
  φ := Corank2ChartJac.shearPhiH
  keep := Corank2ChartJac.shearKeepH
  hdiff := Corank2ChartJac.differentiable_shearPhiH
  hkeep := Corank2ChartJac.shearPhiH_keep
  hread := Corank2ChartJac.shearPhiH_read

/-- The `clearing334` shear IS the real `shearH` — the constructor's geometry is the actual chart's
clearing, not a proxy. -/
theorem clearing334_shear_eq_shearH : clearing334.shear = Corank2GWrapDecomp.shearH :=
  Corank2ChartJac.shearH_eq.symm

/-- The (3,3,4) corank-2 pivots `{0,1}` are kept by the real clearing (both in `shearKeepH`). -/
theorem keep334_all01 : ∀ p ∈ ({0, 1} : Finset (Fin 21)), clearing334.keep p := by
  intro q hq; fin_cases hq <;> exact Or.inl (by decide)

/-- **The corank-2 real born-siblings.** At the (3,3,4) center `{0,1}` (the corank-2 pivots, both
kept
by `shearKeepH`), the constructor emits both siblings from the REAL clearing, EACH certified:
guardrail-0 (`jacDet shear = 1`) + the per-step Jacobian `|jacDet stepMap| = |u_p|^1`. Non-vacuous,
real clearing, born per pivot. -/
theorem bornSiblings334_certified (p : Fin 21) (hp : p ∈ ({0, 1} : Finset (Fin 21)))
    (u : Fin 21 → ℝ) :
    jacDet (bornSiblings ({0, 1} : Finset (Fin 21)) clearing334 keep334_all01 p hp).clearing.shear
        u = 1 ∧
      |jacDet (bornSiblings ({0, 1} : Finset (Fin 21)) clearing334 keep334_all01 p hp).stepMap u|
        = |u p| ^ 1 := by
  have h := bornSiblings_certified ({0, 1} : Finset (Fin 21)) clearing334 keep334_all01 p hp u
  simpa [show ({0, 1} : Finset (Fin 21)).card - 1 = 1 from by decide] using h

end DLNFibre.DLN.Aoyagi.StepConstructor
