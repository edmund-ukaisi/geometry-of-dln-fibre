<task>
Lean 4 + Mathlib v4.29, DLNFibre harness. The (1,1)-smeared RATE leg is LANDED sorry-free. Now the MP
(measure-preserving) + measurable-embedding leg for the flat chart, feeding a LANDED generic-M
divergence lemma `routeMCore_box_diverges_of_MPChart` (it takes: a measure-preserving measurable
embedding `phi : (Fin N → ℝ) → (Fin N → ℝ)` [N = routeMAmbient M] + a source sub-box certificate).

LANDED I can reuse:
- `paramsEquivFlat M : Params M ≃ᵐ (Fin (flatDim M) → ℝ)` (measure-preserving measurable equiv).
- `paramsEquivFlat_symm_decode M x q : ((paramsEquivFlat M).symm x) q.1.1 q.1.2 q.2 = x (flatCoordOf M q)`
  (the per-coord decode, `flatCoordOf M q : Fin (routeMAmbient M)`, `routeMAmbient M = flatDim M`).
- `measurePreserving_shearAt {n} (i : Fin (n+1)) (g : (Fin n → ℝ) → ℝ) (hg : Measurable g) :
    MeasurePreserving (fun x => Function.update x i (x i + g (fun k => x (i.succAbove k)))) volume volume`
  (single-coordinate transvection, det 1; GENERIC, no per-M work).
- The RATE keystone (Params-level): `prod_smParams_eq_smul_pivotCol` where
  `smParams M hL u hrow hcol hm1 := Function.update (baseParams M u) (deepLayer M hL) (smearedDeepLayer …)`,
  `baseParams M u := (paramsEquivFlat M).symm u`, `smearedDeepLayer = updateRow (baseParams u (deepLayer))
  ⟨0,hrow⟩ (fun _ => deepCol ⟨0,hrow⟩ − smearShift)`. `smearShift` reads the FRONT coords (layers 0..L-2,
  via the front product / routing) + the residual deepest-rows (rows 1..m1-1 of the deepest column) — it
  does NOT read the deepest-pivot (0,0) entry.

GOAL: define a flat chart `phiSm : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ)`, a SINGLE
`Function.update` shear at the deepest-(0,0) flat coord `p* := flatCoordOf M ⟨⟨deepLayer, 0⟩, 0⟩`, such
that `(paramsEquivFlat M).symm (phiSm u) = smParams M hL u … u` (so routeMCore(phiSm u) = the rate), AND
`phiSm` is measure-preserving + a measurable embedding.

The shear: `phiSm u := Function.update u p* (u p* − smearShiftFlat u)` where `smearShiftFlat u` = the flat
expression for `smearShift` (reading the OTHER coords). Since `smearShift` doesn't read coord `p*`,
`smearShiftFlat` factors through `fun k => u (p*.succAbove k)` — exactly `measurePreserving_shearAt`'s `g`.

KEY OBSTACLES I foresee:
(a) `measurePreserving_shearAt` needs `routeMAmbient M = n+1` to expose `p*` as `Fin (n+1)`; routeMAmbient
    is opaque. And it ADDS `+ g`, I need `− smearShiftFlat` (sign: use `g = −smearShiftFlat`).
(b) The connection `(paramsEquivFlat).symm (phiSm u) = smParams … u`: LHS decodes coord-by-coord via
    `paramsEquivFlat_symm_decode`. At the deepest-(0,0) slot it must equal `deepCol ⟨0,hrow⟩ − smearShift`;
    at every other slot it must equal `baseParams u` (unchanged). The `Function.update` at `p*` only changes
    coord `p*` = the (0,0) slot; all others decode to `u`'s coord = `baseParams u`'s slot. But `smParams`
    changes the WHOLE deepest-layer row 0 — for the (1,1) family row 0 has only the (0,0) entry (`M_L=1`),
    so it IS just coord `p*`. Need this alignment.
(c) `smearShiftFlat` reading `fun k => u (p*.succAbove k)` — but `smearShift` reads `baseParams u` slots
    (front coords + residual rows). Need `smearShift` re-expressed as a function of `u`'s non-p* coords.
</task>

<output_contract>
1. The cleanest definition of `phiSm` + `smearShiftFlat` (does `smearShiftFlat` need to literally factor
   through `p*.succAbove`, or can I define it as `smearShift M hL u …` directly and prove coord-independence
   separately?). Recommend the design that minimizes the `measurePreserving_shearAt` plumbing.
2. The MP proof route: how to apply `measurePreserving_shearAt` at the opaque `routeMAmbient M` width
   (the `n+1` exposure) — destructure, or is there a width-free transvection-MP lemma? Name the exact steps.
3. The connection lemma `(paramsEquivFlat).symm (phiSm u) = smParams … u` route: Params funext + per-slot
   `paramsEquivFlat_symm_decode` + `Function.update` apply (the p* slot vs others). The deepest-(0,0)
   alignment (smParams's updateRow row-0 = the single coord p* for M_L=1).
4. The measurable embedding: is it automatic from MP-of-an-equiv, or do I package phiSm as a MeasurableEquiv
   (like the validate-small's phi121smME)? Cheapest route.
5. The SINGLE biggest risk / likely wall on this leg.
</output_contract>

<grounding_rules>
Mark Mathlib lemmas you're unsure exist at v4.29 as "verify". Prefer reusing the LANDED pieces over the
validate-small's per-M conjugation scaffolding (split121/coreShear/the ME packaging) — that was per-fixed-
width and should NOT be needed generically. The rate is off-pole only; MP is everywhere (the shear is a
polynomial-in-other-coords transvection, MP unconditionally).
</grounding_rules>
