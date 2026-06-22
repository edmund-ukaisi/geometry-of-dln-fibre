<task>
Lean/Mathlib RLCT resolution for deep linear networks. I'm designing the rank-pattern DISPATCHER
(the `classify`/`routeStep` recipe) that builds a resolution tree whose leaves' monomial thresholds
have infimum = the learning coefficient. I need a red-team on the recipe's CORRECTNESS (the green-but-
wrong risk: a dispatcher that type-checks but encodes the wrong combinatorics).

SETUP. Reduced widths M = (M_0,...,M_L) (a node = a matrix chain core ‖C_L···C_1‖² at its origin, C_s
an M_s × M_{s+1} matrix, the loss = ‖product‖²). The dispatcher recursively classifies M into:
- LEAF: terminal (the core is a unit, no rank-defect coupling remains).
- C1 (coupled rank-defect): blow up the active factor's rank-defect center (a pivotBlowupOn on a
  coordinate subspace), factor out the pivot square, do a det-1 Schur peel that drops ΣM by 2, recurse
  on the reduced widths M'. Each C1 node contributes ONE exceptional divisor of codim c (axis (k,h)=(1,c-1),
  ratio c/2).
- C2 (full-rank pass-through): active factor full-rank but product drops downstream — pass it through, L drops.
- C4 (width-1/rank-1 pinch): Fubini product split, two children.
- C5 (mixed partial-drop): C1+C2 composite at one node.
- C3: NC-completion post-pass (k≥2 divisors), not a tree node.
Termination: lex(L, ΣM, ncDefect).

THE VALUE CLAIM (what makes the dispatcher CORRECT, not just terminating). The achiever value is
lambdaCore = ½·minAdm(Mval), where Mval(M,t) = Σ_j (t_{j-1}-t_j)(M_j - t_j) over rank patterns t
(weakly-decreasing, t_L=0), and minAdm = min over admissible t. The dispatcher's leaves accumulate
codim-lists; the leaf threshold = min over the path of (codim/2); the cover's ⨅ over leaves must = lambdaCore.

THE LOAD-BEARING RECIPE CLAIM (the "C1-condition"): each C1 node's exceptional-divisor codim = the
GEOMETRIC codim of the rank stratum it resolves = some Mval(T) (NOT the raw Jacobian/Hessian rank — those
disagree in "thin product" cases like (4,3,2)). Then:
- (C≥) every path's min-codim ≥ minAdm(Mval) — because every divisor codim is some Mval(T) ≥ minAdm by def.
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
