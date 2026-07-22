<task>
You are a decorrelated second opinion on an EXACT-ALGEBRA question in a resolution-of-singularities
construction (Aoyagi's blow-up normal form for deep linear networks). You have a read-only sandbox
with sympy. BUILD and RUN exact checks; correctness matters more than speed. Do NOT trust my framing
of what "should" happen — derive it.

## The objects (match these EXACTLY)

We fold the loss core `‖∏_{s=1}^{L} C^(s)‖²` (each C^(s) is M^(s)×M^(s+1), entries fresh symbols) along
a tree of blow-ups. Along a path we carry:
- a diagonal `diag(b_1,...,b_{M(S)})`, each `b_i` a monomial in exceptional coords `u_{s,k}` ONLY,
  with `b_i = ∏_{ t̃_{s,k} < i } u_{s,k}`  (so b_1 | b_2 | ... , and b_i is SQUAREFREE in each u).
  Here `t̃_{s,k} = min` of the divisor's profile T_{s,k}.
- a residual family `foldResid` = the core generators (entries of ∏C) STRICT-TRANSFORMED along the
  path: at each edge we compose a coordinate map applied to the coords, defined per edge type below.

Two coordinate maps on the flat coords w (center = a Finset of coords, pivot = one coord):
- `blockBlowupMap center pivot w`:  j=pivot → w_pivot ;  j∈center → w_pivot · w_j ;  else → w_j.
- `blockBlowupCoordQuot pivot j w`:  j=pivot → 1 ;  else → w_j.      (the "strict transform" quotient)
  KEY: for j∈center, blockBlowupMap(...)_j = w_pivot · blockBlowupCoordQuot(...)_j.

`edgeδ = [cleared = 0]` (i.e. δ=1 iff this is the FIRST clear of the current layer, J=0).

The FOUR edge types and their EXACT ledger transitions (Aoyagi pp.16/17/20/21). Let J=cleared,
resRows = M(S)−J, resCols = M^(S+1)−J, runLen = the run-length J_1 to the next occupied b-chain level:
- case2   : new divisor, exponent M = resRows·resCols, profile tail := J  (so t̃ = J); cleared+1.
             foldResid edge map: δ=1 → blockBlowupCoordQuot(pivot) ∘ shear ; δ=0 → blockBlowupMap ∘ shear.
- case11  : BOOST an existing divisor mergeIdx: exponent += runLen·resCols; profile tail := J (t̃ RESET
             to J); numDiv/cleared UNCHANGED. edgeShear = id. foldResid edge map as above by δ.
- case12  : SPLIT: new divisor inherits mergeIdx's profile with tail := J (t̃ = J), exponent =
             mergeIdx.exp + runLen·resCols; mergeIdx UNCHANGED; cleared+1. edgeShear = Schur blockShear.
- rollover: ledger UNCHANGED; cleared := 0; edge map = identity (no blow-up, no shear).

## The claim I need adjudicated: the residual "boost-readiness" at a case11 δ=1 edge

At a case11 δ=1 boost, the reused pivot is an EARLIER-born divisor's birth coordinate `w = u_pivot`.
The boost CENTER = {w} ∪ {a partial block of the CURRENT layer}. The GEOMETRIC support of the residual
is the LARGER full current-layer block. "Boost-readiness" is the three-part claim about the PARENT
residual r (each entry):
  A1: r vanishes when all center coords → 0.
  A2: r has TOTAL degree ≤ 1 in the center coords (JOINTLY — no monomial with two center factors,
      INCLUDING no w²).
  A3: after substituting center coords c → w·c, r is exactly divisible by w^1.
(A1+A2 ⟺ r is "degree-1 supported on the boost center"; A3 is the divisibility the recursion consumes.)

## What to check — build exact sympy for BOTH:

(1) SINGLE boost, widths (2,2,2,2), binding path: case2(J=0,δ=1) born u11; case2(J=1,δ=0) born u12;
    rollover; then case11(δ=1) boosts u12 (pivot w=u12). Construct foldResid at the boost-parent node
    and TEST A1/A2/A3 with center = {u12} ∪ {layer-2 col-0 block}. Report TRUE/FALSE per part.

(2) DOUBLE boost, widths (3,3,2,2), the "coupled binder" path: the binder u13 is born in layer 1, then
    boosted TWICE with the SAME pivot coordinate w = u13's birth coord — first at state (S=2,J=1) which
    is δ=0 (cleared=1), then at (S=3,J=0) which is δ=1 (cleared=0). Construct foldResid at the parent of
    the SECOND (δ=1) boost — i.e. after the δ=0 boost#1 (which uses blockBlowupMap, NOT the strict-
    transform quotient) and the rollover — and TEST A1/A2/A3 with the second boost's center
    = {w} ∪ {layer-3 partial block}. CRITICAL sub-question: does any residual monomial carry w² (i.e.
    does the δ=0 boost#1's blockBlowupMap multiply-in of w, combined with the b-chain ratio b_i/b_1
    which also carries w, produce a w² term)? If so, A2 FAILS at the δ=1 boost. Report the exact max
    exponent of w in any monomial, and whether A2 holds.

If constructing the exact (3,3,2,2) fold is too heavy, build the smallest faithful model that has: a
Deg1-supported parent residual with a b-chain ratio carrying w on the "suffix" rows, a δ=0 case11 boost
(blockBlowupMap center1 w) where center1 is a DIFFERENT (earlier/current) layer block, then a δ=1 case11
boost with center2 = {w} ∪ (a different layer block). State your modeling assumptions explicitly.

## Also answer (design-level):
(3) Is a per-divisor, per-path "ε exponent" normal form F_{p,j} = ∑_τ q_τ · ∏_d u_d^{ε_d(τ)} with the
    transport "ε_{d} += #(blow-up center entries the path reads), with a δ=1 reset" the RIGHT inductive
    object to prove boost-readiness? Or is there a simpler carried invariant that suffices (e.g. a
    per-LAYER degree bound, or "support∖center coords occur only multiplied by w")? Distinguish what the
    δ=1 boost actually CONSUMES from what the induction needs to CARRY.
</task>

<output_contract>
1. A1/A2/A3 verdict for the SINGLE boost (2,2,2,2): TRUE/FALSE per part, with the exact residual.
2. A1/A2/A3 verdict for the DOUBLE boost (3,3,2,2 or your faithful model): TRUE/FALSE per part; the
   EXACT max exponent of w per monomial; whether w² appears and whether A2 survives. Show the residual.
3. The sympy you ran (both cases).
4. Design answer to (3): is the per-divisor/per-path ε normal form the right object; if not, the
   smallest sufficient carried invariant; and precisely which part the δ=1 boost consumes vs the
   induction carries.
5. Flag every INFERENCE vs OBSERVED-from-sympy fact explicitly.
</output_contract>

<grounding_rules>
- Exact algebra only for verdicts; a float/Monte-Carlo check may guide but is never the verdict.
- If a modeling choice is forced (e.g. the exact shear β at a step), state it and check the verdict is
  robust to it. Do NOT guess a transition rule not given above; if a rule is ambiguous, say so.
- Mark clearly which claims are proven by your sympy run vs which are reasoned/inferred.
</grounding_rules>
