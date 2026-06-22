# Fidelity cert — the SQUEEZE datum (`IsSchurStraightenSqueeze` + chain), independent review

Reviewer: fidelity/bedrock pass on `fm2/r1-squeeze-integ` @9c7964a (file
`lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean`). Decorrelated Codex xhigh
(`codex/g132-squeeze-datum-fidelity-{prompt,answer}.md`). Build GREEN (2673 jobs); all 5 new decls
axiom clean-three `[propext, Classical.choice, Quot.sound]` (verified `#print axioms`).

## Verdict: SURVIVED with two SCOPE flags (no wrong-statement in the committed code)

The squeeze datum is the faithful #129/#130 repair. The audited DATUM + CHAIN are sound and the
committed statements do not over-claim. Two flags are for the DOWNSTREAM recursion-closing step, not the
audited target.

### Per-point (faithful)
1. #129 squeeze (compare at same point, no c-o-v): FAITHFUL. `squeeze` is a same-domain, same-point
   comparison; no `χ`, no `MeasurePreserving`, no `χ 0 = 0`. The rlct is taken at the literal `(0,0)`.
2. #130 (i) anchor = deepest point: FAITHFUL-as-stated for an already-anchored `flatCore` (the rlct
   basepoint IS `(0,0)`, no stray free basepoint). SEE FLAG-A (the datum does not itself PROVE `(0,0)` is
   a zero of `flatCore`).
3. #130 (ii) genuine unit: FAITHFUL. The unit role is `c₁,c₂` positive CONSTANTS (`c₁pos`,`c₂pos`), not
   an abstract `Measurable u`. `0 < c₁` is load-bearing — the `F=0⟺Φ=0` vanishing (hence the RLCT
   equality) fails at `c₁=0` (`F=x⁴, Φ=x²` has `0·Φ≤F≤Φ` but different RLCTs). Confirmed against
   `rlctAtOn_unit_invariant_aux`'s `a>0`.
4. NAME=CONTENT: holds. `redCore_eq`, `Gne`, `measure_drops`, `squeeze` say what they prove.
5. SUPERSEDE: CLEAN. Old `IsSchurStraighten`/`schur_straighten_of_data` retained as a TRUE conditional
   (takes the clean `hfactor` as a hypothesis); the unsatisfiable-clean-factor is the hypothesis, not a
   live false assertion. Docstring + SUPERSEDED banner explicit. No false statement left live.
6. AXIOM HYGIENE: clean-three on all 5 new decls. NO `monomial_rlct`/S2.

### NON-VACUITY: CONFIRMED
Built a full term of `IsSchurStraightenSqueeze` (M=![2,1], drop=![1,0] red=![1,1] — a real dim drop;
nReg=3; Y=ℝ; G=const 1 nonvanishing; redEmbed = the 1×1 layer with entry 1, so `dlnLoss S.red 0 = 1 =
G²`; c₁=c₂=1). All seven fields close simultaneously. The chain `schur_straighten_squeeze_of_data` →
`schur_recursion_step_squeeze` → `rlctAtOn_squeeze` + `rlct_additive_smooth_block` genuinely proves the
split (the `Gne` guard blocks the `G≡0 ⟹ rlctAtOn=⊤` smooth-block degeneracy — the right guard).

## FLAG-A (scope, downstream — the serious one). `redCore_eq` is a POINTWISE pullback
`G y² = dlnLoss S.red 0 (redEmbed y)`. It does NOT imply `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`
on the reduced parameter space — that needs `redEmbed` anchored + measure/topology-compatible (a
measure-preserving coordinate identification), or a separate RLCT-transport theorem. NOT a defect in the
AUDITED code: `schur_straighten_squeeze_of_data`'s RHS is literally `rlctAtOn (G²) 0` (it does NOT claim
the reduced-chain identification), and `redCore_eq` is consumed by NO proof here (it is a carried datum
field). The gap bites only when the recursion is CLOSED (the producer must supply the transport). Flag
for the recursion-assembly step.

## FLAG-B (scope, mild). Anchor not internally pinned. `Gne` (G≠0 a.e. on a nbhd of 0) is CONSISTENT
with `G 0 = 0` (a point is null), so it neither forces nor prevents `(0,0)` being a zero of `flatCore`.
If `G 0 ≠ 0`, the split is still TRUE but trivial (`⊤ = ⊤`). The equation is never FALSE. To make the
conclusion non-trivial in the `⊤` regime, add `redEmbed_zero : redEmbed 0 = 0` (then `redCore_eq` +
`dlnLoss S.red 0 0 = 0` forces `G 0 = 0`). Optional hardening; not a wrong-statement.

## FLAG-C (cosmetic). The structure declares `[MeasureSpace Y][TopologicalSpace Y][Zero Y]`, but the
consumer `schur_straighten_squeeze_of_data` needs `[PseudoMetricSpace][ProperSpace][IsFiniteMeasure
OnCompacts][BorelSpace][OpensMeasurableSpace]`. Benign (the consumer re-declares what it needs); the
structure can be inhabited at a `Y` that can't be consumed, which is looseness, not unsoundness.

## Net
The datum's `squeeze` field is shaped so the geometric existence producer CAN fill it (Codex confirms:
cross-terms `F = |E|²+|G+A(E,y)|²` with `|A|≤C|E|` give a genuine two-sided constant bound — though the
producer must prove the actual inequality, NOT merely `flatCore−Φ ∈ ideal(E)`: `F=(G+E)²` has `F−Φ∈(E)`,
nonneg, but is NOT comparable to `E²+G²` since it vanishes along `G=−E`). The producer obligation (pp2
#11) is correctly OUTSIDE the datum.
