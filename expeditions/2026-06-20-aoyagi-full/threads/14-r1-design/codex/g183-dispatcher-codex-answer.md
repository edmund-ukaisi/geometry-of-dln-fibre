- (C=∃) the achiever path resolves to the minimiser T*, its binding divisor has codim = minAdm(Mval).
VALIDATED (exact): (2,2,2) codims {4,3}, min 3 = minAdm, λ=3/2; (3,2,3) minAdm 5, λ=5/2; (2,2,2,2) minAdm 3.
The (2,2,2) tree: step-1 A-pivot card 4 = Mval(t=(0,0)); step-2 card 3 = Mval(t=(1,0)) = the achiever binding.
</task>

<output_contract>
Terse, decisive:
1. The DANGEROUS gap: is "each C1 node's divisor codim = some Mval(T)" actually GUARANTEED by the
   pivotBlowupOn-on-a-rank-defect-center construction, or can a node produce a divisor whose codim is
   NOT a Mval (breaking C≥, letting a path undershoot minAdm)? If it can, what extra condition on the
   pivot choice forces codim = geometric codim = Mval?
2. C≥ rests on "every divisor codim ≥ minAdm". Is that right, or could the ACCUMULATION (min over a path
   of codim/2) dip below minAdm/2 via some path that resolves through non-Mval strata or over-blows-up?
3. The achiever (C=∃): the dispatcher must REACH the minimiser T*. Is "resolve each factor to its T*-rank
   by iterated rank-defect blow-ups" guaranteed to produce a leaf path whose binding codim = minAdm? Any
   case where the minimiser is NOT reachable by the C1/C5 rank-descent (so C=∃ fails)?
4. The recipe's biggest green-but-wrong risk: name the single most likely way a type-checking routeStep
   encodes the WRONG combinatorics (wrong codim, wrong cover, wrong leaf set) and still builds.
5. Does the LEAF condition (terminal when "no rank-defect coupling remains") correctly coincide with the
   recursion bottoming out at a UNIT (threshold ⊤, doesn't bind), or can a non-unit core be misclassified
   as a leaf (silently dropping a binding divisor)?
</output_contract>

<grounding_rules>
The QIP values (Mval, minAdm), the (2,2,2)/(3,2,3)/(2,2,2,2) validations, and the node taxonomy are
TRUSTED. Reason about the recipe's correctness — specifically whether the codim=Mval claim and the C≥/C=∃
obligations are GUARANTEED by the construction or need extra conditions. Distinguish "the recipe is right
but the proof needs lemma X" from "the recipe can produce a wrong tree". Flag the C1-condition (codim =
geometric codim, not Jacobian rank) as the suspected load-bearing seam.
</grounding_rules>

codex
I’ll treat this as a proof-design review, not an implementation task. The key point to isolate is whether the dispatcher stores geometric rank-pattern data, or just whatever coordinate count the current chart happens to expose.
codex
1. **C1 gap:** not guaranteed. `pivotBlowupOn` only knows “blow up this coordinate subspace.” It does not know that the subspace is the strict transform of an admissible rank-pattern stratum. A type-checking dispatcher can record `c = card pivotCoords` or a Jacobian/Hessian rank and get a divisor codim that is not any admissible `Mval(T)`.

   The needed condition is: every C1/C5 pivot must carry a witness `T` with `Adm M T`, and a proof that the pivot center is the smooth strict transform/normal slice of the rank-pattern stratum `S_T`, with selected coordinates a regular parameter system for its ideal:
   `codim(center) = height(S_T) = Mval(M,T)`.
   Also prove the exceptional multiplicity is exactly one pivot square, i.e. axis `(k,h) = (1, c-1)`.

2. **C≥:** yes, but only after that certification. If every accumulated divisor has ratio `Mval(T)/2` for an admissible root-lifted `T`, then `min_path codim/2 ≥ minAdm/2` is immediate. Accumulation itself cannot lower the value; NC subdivisions give positive combinations/weighted averages of existing divisor ratios. The only way to dip below `minAdm/2` is a bogus axis: non-admissible `T`, non-`Mval` codim, wrong discrepancy, or wrong multiplicity. Blowing up too broad a center is especially dangerous because it can create a falsely small `c`.

3. **C=∃:** not automatic. “Resolve each factor to its `T*` rank” is insufficient unless you prove a reachability lemma for coupled product rank patterns. You need:

   `for every minimizer T*, there exists a legal C1/C2/C4/C5 chart path whose transformed target remains admissible after each peel/pass/split, and whose binding C1/C5 center is exactly S_T* with codim Mval(T*)`.

   If the dispatcher is greedy about the active factor, drops mixed C5 branches, or treats factor ranks independently from kernel-image incidence, it can miss the minimizer. I do not see a forced counterexample if the route tree really covers all admissible rank-pattern strata, but that coverage is a theorem, not a consequence of termination.

4. **Biggest green-but-wrong risk:** computing `codim` from local coordinate cardinality/raw rank data instead of threading an admissible rank-pattern witness plus `codim = Mval`. This will type-check, terminate, and pass small symmetric tests, while failing thin or mixed cases like the suspected `(4,3,2)` pattern.

5. **LEAF:** “no rank-defect coupling remains” is too weak. A leaf must carry a unit certificate: the residual core ideal is a unit after removing accumulated monomial factors, so its threshold is `⊤`. Otherwise scalar/rank-one remnants, downstream products after C2, or unresolved C4/C5 cases can be misclassified as leaves and silently drop the binding divisor. The Lean predicate should be closer to `Leaf -> IsUnit residualCore`, not merely “no C1 applies.”
tokens used
18,501
1. **C1 gap:** not guaranteed. `pivotBlowupOn` only knows “blow up this coordinate subspace.” It does not know that the subspace is the strict transform of an admissible rank-pattern stratum. A type-checking dispatcher can record `c = card pivotCoords` or a Jacobian/Hessian rank and get a divisor codim that is not any admissible `Mval(T)`.

   The needed condition is: every C1/C5 pivot must carry a witness `T` with `Adm M T`, and a proof that the pivot center is the smooth strict transform/normal slice of the rank-pattern stratum `S_T`, with selected coordinates a regular parameter system for its ideal:
   `codim(center) = height(S_T) = Mval(M,T)`.
   Also prove the exceptional multiplicity is exactly one pivot square, i.e. axis `(k,h) = (1, c-1)`.

2. **C≥:** yes, but only after that certification. If every accumulated divisor has ratio `Mval(T)/2` for an admissible root-lifted `T`, then `min_path codim/2 ≥ minAdm/2` is immediate. Accumulation itself cannot lower the value; NC subdivisions give positive combinations/weighted averages of existing divisor ratios. The only way to dip below `minAdm/2` is a bogus axis: non-admissible `T`, non-`Mval` codim, wrong discrepancy, or wrong multiplicity. Blowing up too broad a center is especially dangerous because it can create a falsely small `c`.

3. **C=∃:** not automatic. “Resolve each factor to its `T*` rank” is insufficient unless you prove a reachability lemma for coupled product rank patterns. You need:

   `for every minimizer T*, there exists a legal C1/C2/C4/C5 chart path whose transformed target remains admissible after each peel/pass/split, and whose binding C1/C5 center is exactly S_T* with codim Mval(T*)`.

   If the dispatcher is greedy about the active factor, drops mixed C5 branches, or treats factor ranks independently from kernel-image incidence, it can miss the minimizer. I do not see a forced counterexample if the route tree really covers all admissible rank-pattern strata, but that coverage is a theorem, not a consequence of termination.

4. **Biggest green-but-wrong risk:** computing `codim` from local coordinate cardinality/raw rank data instead of threading an admissible rank-pattern witness plus `codim = Mval`. This will type-check, terminate, and pass small symmetric tests, while failing thin or mixed cases like the suspected `(4,3,2)` pattern.

5. **LEAF:** “no rank-defect coupling remains” is too weak. A leaf must carry a unit certificate: the residual core ideal is a unit after removing accumulated monomial factors, so its threshold is `⊤`. Otherwise scalar/rank-one remnants, downstream products after C2, or unresolved C4/C5 cases can be misclassified as leaves and silently drop the binding divisor. The Lean predicate should be closer to `Leaf -> IsUnit residualCore`, not merely “no C1 applies.”
