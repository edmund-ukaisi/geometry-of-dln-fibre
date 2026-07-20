# Decorrelated red-team: an edge-labelled resolution-tree carrier for Aoyagi's DLN RLCT resolution

You are an independent reviewer. I am auditing a Lean 4 skeleton (blueprint forecast, holes allowed)
that transcribes Aoyagi's 2023 resolution of the deep-linear-network multiplication-map singularity
(her §5, pp.14–22) into a datatype + obligations, whose sole output is: for every width chain `M`,
the parameter-box integral `∫ (loss)^{-c'}` is finite whenever `c' < ½·min_t Mval(t)`. RLCT-of-the-loss
= half the geometric codimension. Judge the MATHEMATICAL SHAPE of the statements below. I want
counterexamples / precise gaps, not reassurance. Distinguish clearly what you INFER vs what you can
assert as fact.

## The paper's step content (from her worked construction, verified against images)

A double induction over `(S, J)` (layer S, cleared pivots J). At a step the equal-block run
`b_{J+1}=…` above `J` determines the case. Three cases:

- **Case 1** (partial equal block `b_{J+1}=…=b_{J+J₁} ≠ b_{J+J₁+1}`, `J₁ < M(S)−J`): blow up a
  `J₁ × (M^{(S+1)}−J)` d-block. The affine chart cover splits into TWO chart types of ONE blow-up:
  - **Case 1(1)** (the d-block `= u·d'`, an EXISTING exceptional coordinate `u` divides): sets
    `t̃_{s,k}=J` and **ADDS to that divisor's exponent**: `M'_{s,k} = M_{s,k} + J₁·(M^{(S+1)}−J)`
    (the NEW exponent references the OLD exponent of the SAME divisor — a parent→child update).
  - **Case 1(2)** (first row normalised, `u = u_{S,J+1}·u'`, a NEW pivot `u_{S,J+1}` enters):
    advances `J`; the new pivot enters the monomial vector.
- **Case 2** (full remaining block `b_{J+1}=…=b_{M(S)}`): blow up the full `(M(S)−J)×(M^{(S+1)}−J)`
  block; one new divisor of exponent `M'_{S,J+1} = (M(S)−J)(M^{(S+1)}−J)` (the residual codimension),
  dividing EVERY residual generator (shared δ).

Terminal divisors (`t̃=0`) accumulate exponent `M_{s,k} = Mval(t_{s,k})`; the RLCT core is
`½·min over terminal divisors of M_{s,k}`.

## The Lean encoding under review (edge-labelled carrier)

Children hang off labelled edges; the per-chart CASE and per-chart SUBSTITUTION are per-edge data.

```lean
inductive StepCase | case11 | case12 | case2
structure ChartSubst (M) where
  localSub : Params M → Params M        -- the chart coordinate change (self-map)
  jacDivCount : ℕ
  jacPow : Fin jacDivCount → ℕ          -- monomial-Jacobian exponents at this step
structure StepData (M) where            -- a blow-up node; NO case field
  layer cleared resRows resCols numDiv numB : ℕ
  bExp : Fin numB → (Fin numDiv → ℕ)    -- monomial vectors
  bChain : Monotone bExp
  divExp : Fin numDiv → ℕ               -- per-divisor exponent M_{s,k}
  divTilde : Fin numDiv → ℕ             -- per-divisor clearing level t̃_{s,k}
  numGen : ℕ
  support : Fin numGen → Finset (Fin numDiv)   -- divisor-support (sharing) map
structure LeafData (M) where
  numDiv : ℕ ; divExp : Fin numDiv → ℕ ; divProfile : Fin numDiv → (Fin L → ℕ)
  numB : ℕ ; bExp : ... ; bChain : Monotone bExp
  chartMap : Params M → Params M        -- DERIVED = fold of root→leaf edge substitutions
  srcBox : Set (Params M)               -- UPSTAIRS source domain
  resRank : ℕ                           -- Morse-core rank (0 = bounded unit)
  divCoord : Fin numDiv → Fin (flatDim M) ; resCoord : Fin resRank → Fin (flatDim M)
mutual
  inductive ResolutionTree (M) | leaf (l : LeafData M) | branch (n : StepData M) (edges : List (Edge M))
  inductive Edge (M) | mk (case : StepCase) (subst : ChartSubst M) (child : ResolutionTree M)
end

-- The per-step edge-relational invariant (n = PARENT node, e = one outgoing edge):
def StepRel (n : StepData M) (e : Edge M) : Prop :=
  (e.case = case2 → ∃ k, n.divExp k = n.resRows * n.resCols ∧ ∀ g, k ∈ n.support g) ∧
  (e.case = case11 → ∃ k, n.divTilde k = n.cleared) ∧
  (e.case = case12 → ∃ k, n.divTilde k = n.cleared ∧ ∃ i, 0 < n.bExp i k)

-- terminalExponents t = flatMap over EMITTED leaves of (their divExp values)
-- attainment conjunct in the bundle: `minAdm M ∈ terminalExponents t`
--   (minAdm M = min_t Mval(t), banked; the ≤-half also in the bundle)
```

The coverage bundle `ChartBridge M t` :=
`(∃ U open, {A ∈ box : frobSq(prod A)=0} ⊆ U ⊆ ⋃_{l ∈ leaves t} chartMap_l '' srcBox_l)`
`∧ (∀ leaf, InjOn chartMap srcBox ∧ LeafPullback l ∧ LeafJacobian l)`
`∧ (∀ (l, comp) ∈ leafPaths id t, l.chartMap = comp)`  -- coherence: chartMap = edge-subst fold
where
```lean
LeafPullback l := ∃ residualCore lo hi, 0 < lo ∧ ∀ w ∈ srcBox,
  frobSq (prod M (chartMap w)) = (∏ k, (paramsEquivFlat w (divCoord k))^2) * residualCore w
  ∧ lo * baseForm w ≤ residualCore w ≤ hi * baseForm w      -- baseForm = ‖z‖² Morse, or 1
LeafJacobian l := ∃ (Dφ : Params M → (Params M →L[ℝ] Params M)) lo hi, 0 < lo ∧ ∀ w ∈ srcBox,
  HasFDerivAt chartMap (Dφ w) w
  ∧ ∃ jacUnit, lo ≤ jacUnit ≤ hi ∧ |(Dφ w).det| = (∏ k, (paramsEquivFlat w (divCoord k))^(divExp k − 1)) * jacUnit
```

The analytic hole `region_glue` consumes `ChartBridge` to conclude the box integral is finite when
`c' < ½·e` for every terminal exponent `e`. The intended tool is a banked lemma
`rlctAtOn_boundedUnit_localHomeomorph` whose hypotheses are (paraphrased): a forward map `π` AND an
inverse `πsymm`, both `C¹` on an open `V ∋ wstar`, with `π wstar = wstar`, left/right inverse
identities on `V`, and BOTH Jacobian determinants bounded away from 0 and ∞ on `V` (bounded-UNIT both
directions) — i.e. `π` is a local diffeomorphism with bounded-unit Jacobian. Plus a "scaling bridge"
`∫_{εK} F^{-c'} = ε^{N−2Lc'} ∫_K F^{-c'}` and banked monomial/radial integral reads.

## Questions (give a verdict on each; a concrete counterexample beats a hedge)

**Q1 (case-1(1) fidelity).** The paper's Case-1(1) content is `t̃_{s,k}=J` AND the exponent-merge
`M'_{s,k} = M_{s,k} + J₁·(M^{(S+1)}−J)`, where the CHILD's divisor exponent is the PARENT's plus a
computable increment. The Lean `StepRel` case11 clause is ONLY `∃ k, divTilde k = cleared` (i.e.
`t̃=J`), and never references the child edge's divisor exponents. Is this a faithful encoding of
Case-1(1), or does it drop the load-bearing parent→child exponent-merge? If it drops it, is the
merge encodable given the carrier (edges give access to `e.child`'s root `StepData`/`LeafData`
`divExp`)? Does dropping it make the `∀ p ∈ stepEdges, StepRel` invariant too weak to constrain a
resolution (e.g. does a "resolution" with WRONG child exponents still satisfy StepRel)?

**Q2 (transport signature-fit / no-laundering).** `LeafJacobian` supplies only the FORWARD derivative
`Dφ` and the identity `|det Dφ| = (∏ u^{divExp−1}) · jacUnit`. It supplies NO inverse map `πsymm`, no
`Dπsymm`, no bounded-unit hypothesis on the inverse, and no `π wstar = wstar`. Moreover `|det Dφ|` is
NOT bounded-unit (it has the vanishing monomial factor `∏ u^{divExp−1}`). The banked transport lemma
`rlctAtOn_boundedUnit_localHomeomorph` needs a full local diffeomorphism with bounded-unit Jacobian in
BOTH directions. A blow-up/monomialization chart `π(u,y) = (u, u·y)` is NOT a local diffeo on the
exceptional locus `{u=0}` (its Jacobian det = u vanishes there), which is exactly where the RLCT
basepoint sits. Question: can `region_glue` actually discharge its integral from `LeafPullback` +
`LeafJacobian` as stated, using this transport lemma? Or is the bundle under-provisioned — does
`region_glue` need the construction to ALSO expose a FACTORIZATION `chartMap = (monomial blow-up) ∘
(bounded-unit diffeo)` (not just the determinant product), so the transport strips the unit part and
direct monomial integration handles the singular part? Is there a laundering risk (the CoV burden
relocated into region_glue's own opaque sorry rather than discharged from the leaf data)?

**Q3 (attainment via emitted path).** The bundle asserts `minAdm M ∈ terminalExponents t` where
`terminalExponents` ranges over the tree's EMITTED leaves (those reachable through edges). Does
membership in this list faithfully realize "the minimal exponent is ATTAINED by a leaf the resolution
actually emits", or is a stronger explicit-path witness (a concrete root→leaf edge list) needed to
rule out a phantom leaf? Is there any way `minAdm ∈ terminalExponents t` holds vacuously or by a leaf
not genuinely on the tree?

**Q4 (any other soundness gap).** Given the goal is `rlct = ½·codim` with the tightness at binding
cells (zero slack — any lossy over-approximation is FALSE there), is there anything in these
statements that could be satisfied by a WRONG resolution, or that overclaims relative to the paper?
