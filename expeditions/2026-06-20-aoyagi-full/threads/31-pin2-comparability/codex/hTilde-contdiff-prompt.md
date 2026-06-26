<task>
Lean 4 + Mathlib v4.29 formalisation. I must discharge ONE `sorry` (`hTilde`) inside theorem
`deepest_gauge_construction` (file `DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean`).
I was briefed that the proof is routine, but I discovered the briefed approach is WRONG and I want
your independent strategy call BEFORE I spend compute, plus a sanity check on whether the goal is
even provable as stated. Be skeptical and concrete.

## The goal (`hTilde`)
Let `R := Fin nReg → ℝ`, `W := (Fin (flatDim M) → ℝ) × (Fin nGauge → ℝ)` (core × spec), and
`DeepestSplit := R × W`. Two given objects:
  • `Efull : DeepestSplit → R` is `ContDiff ℝ ⊤` GLOBALLY (lemma `deepestEFull_contdiff`, proved).
    Its strict derivative at 0 is the invertible total shear `regStraightenTotalCLM2 D_E` with
    invertible reg-block `F` (lemma `deepestEFull_deriv`, PROVED, axiom-clean modulo an inherited
    cert-body sorry).
  • `coreAbsorb : DeepestSplit ≃ₜ DeepestSplit` is a HOMEOMORPHISM (NOT a continuous-linear-equiv),
    namely `coreShearHomeo (schurCutoffShift)`:
        coreAbsorb (reg, core, spec) = (reg, core + shift(reg,spec), spec)
        coreAbsorb.symm (reg, core, spec) = (reg, core − shift(reg,spec), spec)
    where `shift = schurCutoffShift = χ • schurShiftRaw`,
        χ = a `ContDiffBump` at 0 (smooth, compact support, =1 near 0, tsupport χ ⊆ unitSet),
        schurShiftRaw(p) = flat-encode of per-layer `−Z_s(p)·(1+X_s(p))⁻¹·Y_s(p)`
            (X_s,Y_s,Z_s are LINEAR (CLE) reads of p; the only non-smoothness is the matrix inverse
             `(1+X_s)⁻¹`, which has poles where `det(1+X_s)=0`).
        unitSet = {p | ∀ s, det(1+X_s(p)) ≠ 0} is OPEN and contains 0; tsupport χ ⊆ unitSet.

The goal to prove:
  ∃ eTilde : DeepestSplit ≃L[ℝ] DeepestSplit,
    ContDiff ℝ ⊤ (regStraightenOf2 (fun q => Efull (coreAbsorb.symm q)))   -- (A) GLOBAL ContDiff
    ∧ HasStrictFDerivAt (regStraightenOf2 (fun q => Efull (coreAbsorb.symm q))) eTilde 0   -- (B)

where `regStraightenOf2 g := fun q => (g q, q.2)` and `regStraightenTotalCLM2 D := fun δ => (D δ, δ.2)`.

## The consumer (why GLOBAL ContDiff)
`hTilde` feeds `rlctAtOn_comp_localDiffeo (F) (wstar:=0) (f := regStraightenOf2 (Efull∘coreAbsorb.symm)) e`
whose signature DEMANDS `hcontdiff : ContDiff ℝ ⊤ f` GLOBALLY (it uses `hcontdiff.continuous` for
global measurability of the local diffeo's Jacobian, per `rlctAtOn_squeeze`). So (A) is genuinely
global ⊤-smoothness of `Efull ∘ coreAbsorb.symm`.

## The problem with the briefed approach
The brief said "ContDiff is routine (deepestEFull_contdiff ∘ a CLE)" — but `coreAbsorb.symm` is NOT a
CLE; it is a homeomorphism whose shift contains the matrix inverse `(1+X_s)⁻¹` (poles) tamed only by a
ContDiffBump cutoff χ. So to get GLOBAL ⊤-smoothness of `Efull ∘ coreAbsorb.symm` I would need to prove
GLOBAL ⊤-smoothness of `schurCutoffShift = χ • schurShiftRaw`, which is NOT yet proved anywhere (only
`continuous_schurCutoffShift` exists). The smoothness ladder would be:
  (1) ContDiffAt of `(1+X_s)⁻¹` on unitSet (matrix-inverse smoothness on the invertible locus);
  (2) ContDiffAt schurShiftRaw on unitSet; OFF tsupport χ it = 0 (smooth); glue to GLOBAL ContDiff of
      `χ • schurShiftRaw` via the bump killing the pole region;
  (3) ContDiff of coreShearHomeo.symm (smooth shift) ⟹ ContDiff of Efull∘coreAbsorb.symm.
Concern: the domain `(Fin n→ℝ)×(Fin m→ℝ)` carries the sup/Pi norm (NOT inner-product); yet `cutoffBump`
(a `ContDiffBump`) already typechecks in the file, so `HasContDiffBump` resolves somehow. I have NOT
verified the bump is ⊤-smooth as a function on this exact normed space.

## What I have available (all PROVED, axiom-clean unless noted)
  • `deepestEFull_contdiff`, `deepestEFull_base` (Efull 0 = 0), `deepestEFull_deriv`
    (∃ D_E e, HasStrictFDerivAt Efull D_E 0 ∧ ↑e = regStraightenTotalCLM2 D_E, e : ≃L invertible).
  • `hasStrictFDerivAt_regStraightenOf2_gen : HasStrictFDerivAt E D 0 → HasStrictFDerivAt
    (regStraightenOf2 E) (regStraightenTotalCLM2 D) 0`.
  • `regStraightenTotalCLM2_equiv_of_regBlock_isUnit : (F:≃L, ↑F = D.comp regInCLM) → ∃ e:≃L, ↑e =
    regStraightenTotalCLM2 D`.
  • `continuous_schurCutoffShift`, `schurCutoffShift_zero`, `schurCutoffShift_eq_raw_of_mem_closedBall`
    (= raw on inner ball, χ=1), `tsupport_cutoffBump_subset_unitSet`, `isOpen_unitSet`,
    `continuousAt_schurCorrection`/`continuousAt_inv_one_add_readX` (CONTINUITY only — no ContDiff).
  • `coreShearHomeo` (the ≃ₜ), `coreShearHomeo_regular/_spectator/_basepoint`.
  • Matrix inverse smoothness in Mathlib v4.29: I believe `contDiffAt_ring_inverse` /
    `Matrix.contDiffAt...` exist; the matrix-product / cast-to-`Ring.inverse` route is the usual one.

## Specific questions
1. Is GLOBAL ⊤-smoothness of `Efull ∘ coreAbsorb.symm` actually achievable here, or is there a
   structural obstruction I'm missing (e.g. the bump's ⊤-smoothness failing on the Pi sup-norm space,
   or `ContDiffBump` only giving finite smoothness)?
2. Is there a SHORTER route to (A)+(B) than the full ladder (1)-(3)? In particular: since (B) only
   needs the STRICT DERIVATIVE AT 0 and `schurCutoffShift = schurShiftRaw` near 0 with χ=1, and the
   reg/spec slots are fixed by coreAbsorb, can the *derivative at 0* of `Efull∘coreAbsorb.symm` be
   read off cheaply (D(Efull)(0) ∘ D(coreAbsorb.symm)(0))? And for (A), is there any way to AVOID
   global ⊤-smoothness — e.g. is the consumer's global-ContDiff hypothesis actually relaxable to
   "ContDiffOn an open nbhd of 0 + global continuity + global measurability of fderiv", which the
   continuity lemmas already give? (I can edit only files under DLNFibre/DLN/RLCT/.)
3. If the full ladder is required, give the MINIMAL set of new lemmas (names + exact Lean statements)
   and the load-bearing Mathlib lemma for each step (matrix-inverse ContDiff; bump ⊤-smoothness;
   the smooth-gluing `contDiff_of_…` for χ•raw vanishing off tsupport). Rank by risk.
4. The cleanest derivative-at-0 computation for `coreShearHomeo.symm`: its shift's derivative at 0.
   Note `shift = χ•raw`, χ(0)=1, raw is ContDiffAt 0 (on unitSet), so D(shift)(0) = D(raw)(0). And
   `raw(p) = encode(−Z(p)(1+X(p))⁻¹Y(p))` with X,Y,Z linear and Z(0)=Y(0)=0, so raw is degree-≥2 at 0
   ⟹ D(raw)(0) = 0. Hence D(coreAbsorb.symm)(0) = identity. Confirm this and whether it makes
   D(Efull∘coreAbsorb.symm)(0) = D(Efull)(0), so eTilde from `deepestEFull_deriv` works verbatim.
</task>

<output_contract>
  Four sections, one per question, in order. For Q1 a yes/no verdict + the single decisive reason.
  For Q2 rank candidate shortcuts cheapest-first with the blocking risk of each. For Q3 a numbered
  lemma list with exact Lean `theorem name (args) : statement` signatures and the Mathlib lemma each
  rests on. For Q4 confirm/refute the D(symm)(0)=id claim with the one-line reason. Be terse; flag
  every claim you are INFERRING vs one you can ground in Mathlib v4.29 API you are sure exists.
</output_contract>

<grounding_rules>
  Distinguish "Mathlib v4.29 lemma I am confident exists (give exact name)" from "lemma I expect but
  cannot name precisely". Do NOT invent lemma names; if unsure, describe the shape and say so. The
  diagnosis (route + risk ranking) is what I need; any Lean code is illustrative and I will verify it
  compiles before trusting it.
</grounding_rules>
