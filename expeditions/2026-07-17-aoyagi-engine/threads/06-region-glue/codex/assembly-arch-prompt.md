<task>
Lean 4 + Mathlib v4.29 formalisation. I must prove ONE theorem (`region_glue`) — a global
lintegral finiteness bound. I have already proved the "scaling bridge" lemma; I need the cleanest
proof ARCHITECTURE for the remaining assembly, given a subtle obstruction (the chart source sets are
abstract, not product boxes). Diagnose the architecture; do not write full Lean.

## The goal (verbatim signature; I may NOT change it — another seat owns the file)

    theorem region_glue (M : Fin (L + 1) → ℕ)
        (hbridge : ChartBridge M (resolutionOf M)) (c' : ℝ)
        (hrat : ∀ e ∈ terminalExponents (resolutionOf M), c' < (e : ℝ) / 2) :
        routeMLayerBoxIntegral M c' 1 < ⊤

where

    routeMLayerBoxIntegral M c' 1 = ∫⁻ A in paramsBoxM M 1, ENNReal.ofReal ((frobSq (prod M A)) ^ (-c'))
    -- paramsBoxM M 1 = { A : Params M | ∀ s i j, A s i j ∈ Set.Icc (-1) 1 }   (a closed cube [-1,1]^N)
    -- Params M ≅ ℝ^N (N = flatDim M) as a finite-dim normed ℝ-space with Haar `volume`; paramsEquivFlat
    --   is a measure-preserving linear iso Params M ≃ (Fin N → ℝ).
    -- F(A) := frobSq (prod M A) = ‖A^(1)·…·A^(L)‖²_Frobenius. F ≥ 0, continuous (polynomial), and
    --   HOMOGENEOUS of degree 2L: F(c • A) = c^(2L) F(A). Zero locus Z = {F=0} is a cone (0 ∈ Z).
    -- `^ (-c')` is Real.rpow. c' : ℝ (no sign hypothesis in the statement; in real use 0 ≤ c' < minAdm/2,
    --   but the theorem must cover all c' : ℝ).

## The hypothesis data (ChartBridge), a finite list of "leaves" l (l ∈ leaves (resolutionOf M)):

    ChartBridge M t :=
      (∃ U, IsOpen U ∧ {A ∈ paramsBoxM M 1 | frobSq (prod M A) = 0} ⊆ U ∧
            U ⊆ ⋃ l ∈ leaves t, l.chartMap '' l.srcBox)              -- (COVER) upstairs-open image cover
      ∧ (∀ l ∈ leaves t,
          Function.Injective l.divCoord ∧ Function.Injective l.resCoord ∧
          Disjoint (range l.divCoord) (range l.resCoord) ∧
          (∃ N, volume N = 0 ∧ Set.InjOn l.chartMap (l.srcBox \ N)) ∧     -- a.e.-injective
          LeafPullback l ∧ LeafJacobian l)
      ∧ (coherence: each leaf's chartMap = fold of edge substitutions)

Each leaf l has: numDiv, resRank : ℕ; divExp : Fin numDiv → ℕ; divProfile; chartMap : Params M → Params M;
srcBox : Set (Params M); divCoord : Fin numDiv → Fin (flatDim M); resCoord : Fin resRank → Fin (flatDim M).
Coordinates are read off a point w via `paramsEquivFlat M w (divCoord k)` etc.

    LeafPullback l := ∃ (R : Params M → ℝ) (lo hi : ℝ), 0 < lo ∧ ∀ w ∈ l.srcBox,
        frobSq (prod M (l.chartMap w)) = (∏ k : Fin l.numDiv, (paramsEquivFlat M w (l.divCoord k))^2) * R w
        ∧ lo * baseForm l w ≤ R w ∧ R w ≤ hi * baseForm l w
      where baseForm l w = (if resRank=0 then 1 else ∑ i:Fin resRank, (paramsEquivFlat M w (resCoord i))^2)  -- ‖z‖²

    LeafJacobian l := ∃ (β ψ ψsymm : Params M → Params M) (Dβ Dψ : Params M → (Params M →L[ℝ] Params M))
        (lo hi : ℝ), 0 < lo ∧
        (∀ w ∈ srcBox, chartMap w = ψ (β w)) ∧
        (∀ w ∈ srcBox, HasFDerivAt β (Dβ w) w ∧
            |(Dβ w).det| = ∏ k, |paramsEquivFlat M w (divCoord k)|^(divExp k - 1)) ∧
        (∀ v ∈ β '' srcBox, ψsymm (ψ v) = v ∧ ψ (ψsymm v) = v ∧ HasFDerivAt ψ (Dψ v) v
            ∧ lo ≤ |(Dψ v).det| ∧ |(Dψ v).det| ≤ hi)

    terminalExponents t = (leaves t).flatMap (fun l => (finRange l.numDiv).map l.divExp
                                                        ++ (if 0 < l.resRank then [l.resRank] else []))
    -- so hrat gives: c' < divExp k / 2 for every leaf & divisor index, AND c' < resRank / 2 for every leaf.

## The banked lemmas I can consume (all proved, sorry-free)

  rlctAtOn F wstar := sSup { c : ℝ≥0∞ | ∃ c':NNReal, c = c' ∧ ∃ Ω open ⊇ {wstar},
                              IntegrableOn (fun w => |F w|^(-(c':ℝ)) * 1) Ω volume }   -- germ threshold at a point

  rlctAtOn_boundedUnit_localHomeomorph : for π a local diffeo on open V ∋ wstar with inverse πsymm,
     both C¹ on V, π wstar = wstar, bounded-unit |det Dπ|, |det Dπsymm| on V:
       rlctAtOn (fun w => F (π w)) wstar = rlctAtOn F wstar

  rlctAtOn_ray_scaling_invariant : F homog degree D, t>0 ⟹ rlctAtOn F (t • v) = rlctAtOn F v
  deepest_le_of_homogeneous_core : F homog degree D ⟹ rlctAtOn F 0 ≤ rlctAtOn F v   (origin is the min)

  -- MY new scaling bridge (just proved, on Fin N → ℝ, F' any measurable nonneg degree-D homogeneous):
  lintegral_rpow_neg_smul_bridge :
     ∫⁻ y in ε • K, ofReal (F' y ^ (-c')) = ofReal (ε ^ ((N:ℝ) - D*c')) * ∫⁻ x in K, ofReal (F' x ^ (-c'))
     (0 < ε, K measurable)

  -- radial/monomial 1-D reads exist: ∫ over a ball of ‖z‖^(-2c') < ⊤ iff c' < resRank/2;
  --   ∫_Ioc of |u|^(divExp-1-2c') < ⊤ iff c' < divExp/2.

## THE OBSTRUCTION

The chart source `srcBox` is an ABSTRACT `Set (Params M)` — NOT guaranteed to be a product box, nor
bounded. So I canNOT directly Fubini-factorize the per-leaf integral ∫_{srcBox} (∏|u|^{divExp-1-2c'})·‖z‖^{-2c'}
into 1-D integrals. This is why the "direct area-formula per leaf" route seems to fail. The intended
route ("route (b)") uses rlctAtOn (a germ/point notion) + the scaling bridge (homogeneity), but I need
to see the clean global assembly.

Specifically I am unsure how to compose:
 (i) the COVER is a union of chart IMAGES covering an OPEN nbhd U of the whole (compact, cone) zero locus
     Z∩box; no single chart image is guaranteed to be a neighborhood of any point.
 (ii) rlctAtOn is defined pointwise (germ at wstar); the goal is a GLOBAL box integral.
 (iii) F is homogeneous so the box integral is "controlled by rlctAtOn F 0" — but the origin 0 might sit
     under several charts.
</task>

<output_contract>
Answer in these sections, terse and concrete:

1. RECOMMENDED ARCHITECTURE. The top-level skeleton for `region_glue` as a short chain of named
   sub-lemmas (state each sub-lemma's rough Lean signature). Pick ONE architecture and justify why it
   dodges the abstract-srcBox obstruction. Especially: does the global box integral reduce to
   (a) a finite sum over charts of per-leaf integrals via cover+subadditivity, each per-leaf integral
       bounded WITHOUT needing srcBox to be a product box, or
   (b) rlctAtOn F 0 > c' (origin RLCT) via the scaling bridge + a compactness/cover argument, or
   (c) something else?
   If (a): how is each per-leaf ∫_{chartMap '' srcBox} F^{-c'} < ⊤ proved given only LeafPullback +
   LeafJacobian + a.e.-injectivity, WITHOUT product structure on srcBox? Be concrete about the change of
   variables lemma used and how the transport lemma / area formula handles the abstract set.

2. THE ROLE OF EACH BANKED TOOL. For rlctAtOn_boundedUnit_localHomeomorph, the scaling bridge, and the
   radial/monomial reads — say exactly where each enters (or if some are unnecessary / red herrings).

3. THE c'≤0 vs c'>0 SPLIT. Confirm the easy case and the exact hypotheses needed.

4. THE BIGGEST RISK / MOST LIKELY TO WALL. Which sub-lemma is the real analytic content and might not be
   dischardgeable from the given ChartBridge data, and what extra hypothesis (if any) I'd need to request
   from the construction seat (e.g. srcBox nonempty-interior, srcBox ⊆ a bounded box, srcBox measurable).

5. IS THE STATEMENT EVEN TRUE / PROVABLE from this exact ChartBridge? Flag any gap where the hypotheses
   are too weak to prove the conclusion (e.g. missing measurability of srcBox, missing boundedness).
</output_contract>

<grounding_rules>
Distinguish (i) what follows rigorously from the stated hypotheses vs (ii) your inference about the
intended design. If a needed fact is NOT in the hypotheses (e.g. srcBox measurability/boundedness),
say so explicitly rather than assuming it. Prefer Mathlib v4.29 lemma names you are confident exist;
flag guesses.
</grounding_rules>
