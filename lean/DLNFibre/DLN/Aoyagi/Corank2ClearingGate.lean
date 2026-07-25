import DLNFibre.DLN.Aoyagi.Corank2ChartJac

/-!
# M2 first-unit gate — the real coupled clearing is a CLEAN reads-only-kept blockShear

The elder's M2 acceptance gate (a THEOREM, not "built green"): the constructor's coupled clearing
step
IS `blockShear φ` with `φ` READING ONLY the kept coords and VANISHING on them (touching only the
residual/cleared block — the `shearH_eq` analogue, the block-structure separation). This is NOT the
retired divide-by-pivot risk (structurally precluded — see `Corank3HjacProbe`); it is whether the
ACTUAL clearing has the clean-blockShear STRUCTURE. **The surprise to catch: a clearing that reads a
CLEARED coord** (breaking `φ`'s reads-only-kept hypothesis). **Verdict: GREEN — no such surprise.**

**corank-2 (the REAL (3,3,4) chart — banked `shearH_eq`).** `clearing_334_clean_reads_only_kept`:
the actual coupled clearing `shearH` of the (3,3,4) resolution chart IS `blockShear shearPhiH`, and
`shearPhiH`
* VANISHES on the kept coords `{0,1,2,3} ∪ {12..20}` (`shearPhiH_keep`) — it touches ONLY the
residual
  block `{4..11}`;
* READS only the kept coords (`shearPhiH_read`) — every clearing term is a pivot×connection product
  (`w₀·w₂`, `w₁·w₂`, `-(w₀·w₁₂) - w₁·w₁₆`, …); ZERO residual (cleared) factors. The block separation
  is exact — no clearing reads a cleared coord.

**general-d step form.** The genuinely-coupled corank-3 model `Corank3HjacProbe.shearPhi3` (incl.
the
**trilinear** `w₀·w₁·w₂` accumulation) is likewise reads-only-kept + vanishing-on-kept
(`Corank3HjacProbe.shearPhi3_read`/`_keep`), clearing `{3,4,5}` reading only `{0,1,2}`. The general
step-form CONTRACT is `jacDet_blockShear`: it needs EXACTLY reads-only-kept + vanishing-on-kept and
delivers `jacDet = 1` — so any clearing meeting the contract is clean, regardless of coupling
content.

**Why the surprise cannot arise (the block separation is structural at any corank).** Block
elimination clears the residual entries using the PIVOT CONNECTIONS — a coordinate set DISJOINT from
the residual being cleared (the pivots/connections are shallower; the residual is the deepest
coupled
block). The Schur clear sets residual `↦ residual − (connection·connection)`; the displacement `φ`
reads the connections (kept), never the residual (cleared). Verified exactly at corank-2
(`shearPhiH`,
all pivot×connection products). The per-step reads-only-kept of the *built* constructor is M2's
guardrail-0 invariant (each emitted clearing reads only kept); this gate establishes it at the real
corank-2 leaf and the general step form, so a clearing that read a cleared coord would fail the
contract and be caught.

## Main result
- `clearing_334_clean_reads_only_kept` — the real (3,3,4) clearing `shearH` is a clean
reads-only-kept
  (+ vanishing-on-kept) blockShear: the `shearH_eq` analogue for M2's first unit.
-/

open DLNFibre.Core.Aoyagi DLNFibre.DLN.Aoyagi.Corank2GWrapDecomp DLNFibre.DLN.Aoyagi.Corank2ChartJac

namespace DLNFibre.DLN.Aoyagi.Corank2ClearingGate

/-- **M2 first-unit gate (corank-2, REAL (3,3,4)) — the `shearH_eq` analogue.** The actual coupled
clearing `shearH` of the (3,3,4) resolution chart IS a clean reads-only-kept blockShear:
`shearH = blockShear shearPhiH`, with `shearPhiH` VANISHING on the kept coords (touching only the
residual block `{4..11}`) and READING only the kept coords (`{0,1,2,3} ∪ {12..20}`) — never a
cleared
coord. All three conjuncts are the banked `Corank2ChartJac` facts; this packages them as the gate.
-/
theorem clearing_334_clean_reads_only_kept :
    shearH = blockShear shearPhiH ∧
      (∀ u i, shearKeepH i → shearPhiH u i = 0) ∧
      (∀ u v : Fin 21 → ℝ, (∀ i, shearKeepH i → u i = v i) → shearPhiH u = shearPhiH v) :=
  ⟨shearH_eq, shearPhiH_keep, shearPhiH_read⟩

end DLNFibre.DLN.Aoyagi.Corank2ClearingGate
