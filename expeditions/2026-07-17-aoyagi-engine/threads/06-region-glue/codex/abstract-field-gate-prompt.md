<task>
Adversarial soundness audit of a Lean 4 / Mathlib interface `ChartBridge` against a
downstream finiteness theorem `region_glue`. I want you to HUNT for a gap: find a leaf
(or tree) that SATISFIES every clause of `ChartBridge` and the ratio hypothesis `hrat`,
yet for which the box-integral in `region_glue` is INFINITE — i.e. `region_glue` is
false-as-stated. If you cannot construct such a witness after genuine effort, say so
and state which clause blocks each escape you tried. Do NOT assume the interface is
correct; that is the question.

## Setting
- `Params M` is a finite-dimensional real normed space; `flatDim M : ℕ` its dimension;
  `paramsEquivFlat M : Params M ≃ (Fin (flatDim M) → ℝ)` a linear iso (flat coordinates);
  `volume` the Haar/Lebesgue measure on it (NOT assumed complete).
- `frobSq (prod M A)` is a nonnegative polynomial "loss" `F : Params M → ℝ≥0`.
- The DLN target: `routeMLayerBoxIntegral M c' 1 = ∫⁻ over the unit box of F^{-c'}`; we
  want it `< ⊤` (finite) for `c' > 0` below a threshold; `c' ≤ 0` is a trivial bounded case.

## Carrier (finite inductive)
`ResolutionTree M` is a finite inductive: `leaf (LeafData M)` or
`branch (StepData M) (List (Edge M))`; `leaves t : List (LeafData M)` (a genuine finite List).
Each `LeafData` carries: `numDiv : ℕ`, `divExp : Fin numDiv → ℕ`, `resRank : ℕ`,
`divCoord : Fin numDiv → Fin (flatDim M)`, `resCoord : Fin resRank → Fin (flatDim M)`,
`chartMap : Params M → Params M`, `srcBox : Set (Params M)`.

## Supporting predicates
- `residualBaseForm l w := if resRank = 0 then 1 else ∑ i:Fin resRank, (paramsEquivFlat M w (resCoord i))^2`
- `LeafPullback l := ∃ residualCore (lo hi : ℝ), 0 < lo ∧ ∀ w ∈ srcBox,
    F(chartMap w) = (∏ k, (paramsEquivFlat M w (divCoord k))^2) * residualCore w
    ∧ lo * residualBaseForm l w ≤ residualCore w ≤ hi * residualBaseForm l w`
- `LeafJacobian l := ∃ β ψ ψsymm (Dβ Dψ) (lo hi), 0<lo ∧
    (∀ w∈srcBox, chartMap w = ψ(β w))
    ∧ (∀ w∈srcBox, HasFDerivAt β (Dβ w) w ∧ |(Dβ w).det| = ∏ k, |paramsEquivFlat M w (divCoord k)|^(divExp k - 1))
    ∧ (∀ v∈β''srcBox, ψsymm(ψ v)=v ∧ ψ(ψsymm v)=v ∧ HasFDerivAt ψ (Dψ v) v ∧ lo ≤ |(Dψ v).det| ≤ hi)`

## ChartBridge M t (the interface under audit)
1. Cover: `∃ U open, {A ∈ unit box | F A = 0} ⊆ U ⊆ ⋃ l ∈ leaves t, chartMap l '' srcBox l`.
2. Per leaf l ∈ leaves t:
   - `MeasurableSet srcBox`
   - `∃ R>0, srcBox ⊆ paramsEquivFlat⁻¹'(cubeBox (flatDim M) R)`   (bounded in a flat cube)
   - `Function.Injective divCoord`, `Function.Injective resCoord`, `Disjoint (range divCoord) (range resCoord)`
   - `∃ N, volume N = 0 ∧ Set.InjOn chartMap (srcBox \ N)`
   - `LeafPullback l ∧ LeafJacobian l`
3. Coherence: each leaf's chartMap = the fold of its root→leaf edge substitutions.

## terminalExponents and hrat
`terminalExponents t := (leaves t).flatMap (fun l => (map divExp over Fin numDiv) ++ (if 0 < resRank then [resRank] else []))`.
`region_glue` hypothesis `hrat : ∀ e ∈ terminalExponents t, c' < (e:ℝ)/2`.

## region_glue (the theorem whose soundness you audit)
`region_glue (hbridge : ChartBridge M t) (c' : ℝ) (hrat) : routeMLayerBoxIntegral M c' 1 < ⊤`.
Intended proof: c'≤0 trivial; for c'>0 — small box ⊆ U ⊆ ⋃images (finite union, finite leaves);
per leaf via Mathlib area formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul` on srcBox∖N̄
(chain rule Dφ = Dψ(β·)∘Dβ, |det Dφ| ≤ hi·∏|u|^(divExp−1)); enlarge bounded srcBox to a product
cube; Tonelli over divisor / Morse / spectator coordinates; banked 1-D monomial read (finite iff
c'<divExp/2) + Morse radial read (finite iff c'<resRank/2); homogeneity scaling small-box→unit-box.

## Specific escapes to probe (find a satisfying-but-divergent witness, or block it)
(a) COORDINATE ALIGNMENT: can the divisor monomial and the Morse core end up on OVERLAPPING or
    non-separated flat coordinates so Tonelli cannot factor, despite clauses 2 holding?
(b) FINITE COVER: is there any way the effective cover is INFINITE, or the small-box-around-0 step
    fails (e.g. 0 not in U), given clause 1?
(c) CONSTANTS: does anything require the per-leaf (lo,hi) to be UNIFORM across leaves?
(d) NULL SET / MEASURABILITY: does `volume N = 0` (N possibly non-measurable) break the area formula's
    `MeasurableSet` need, with no repair?
(e) UNBOUNDED-in-a-hidden-direction, degenerate divExp (=0), resRank interplay, spectator coordinates,
    residualCore measurability, or ANY other field-level gap you can realize.
</task>

<output_contract>
Two sections.
1) VERDICT: either "WITNESS FOUND" (give the explicit leaf/tree: flatDim, divCoord/resCoord,
   chartMap, srcBox, divExp, resRank, c', and show which region_glue step diverges while every
   ChartBridge clause + hrat holds) — or "NO WITNESS" (the interface forces enough).
2) PER-FIELD table (a)-(e) + any field you add: FORCES-ENOUGH or GAP; if GAP, the missing
   hypothesis, whether a real monomializing blow-up chart supplies it freely, and a witness sketch;
   if a needed step is a banked lemma (not a hypothesis), name it.
Be concrete with coordinates and exponents. Prefer a realized counterexample over a worry.
</output_contract>

<grounding_rules>
Distinguish (i) a REALIZED counterexample (explicit satisfying-but-divergent witness) from
(ii) an unproven worry. Mark each. If you claim a Mathlib lemma is missing or misstated, flag it
as inference unless you are certain of the v4.29 name. Do not assume region_glue is correct or
incorrect — derive it from the clauses.
</grounding_rules>
