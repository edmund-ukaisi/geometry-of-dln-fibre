<task>
You are red-teaming ONE algebraic claim that decides whether a Lean formalisation front is opened
(formaliser-long, tractable) or flagged as a research gap. DECORRELATED — I withhold my conclusion.

SETUP. Deep linear network: parameters = a chain of matrices (C_1,…,C_L), loss
F = ‖C_L···C_1 − B‖²_Frobenius, B a fixed rank-r target. At a global minimum v (a point of the fibre
{C : C_L···C_1 = B}), we must SPLIT the loss into [regular nondegenerate quadratic block] ⊞ [singular
homogeneous core], to peel the smooth directions (the "regular block") before resolving the core. This
split is the "L2-at-v" step. (It is logically upstream of, and a different mechanism from, the
resolution of the core.)

At v, the loss has a critical point (F=0 is the minimum, ∇F=0). F = ‖dP(δ)‖² + O(δ³), where dP is the
linear part of the PRODUCT map μ(C)=C_L···C_1 at v: dP(δ) = Σ_s (downstream_s)·δ_s·(upstream_s), with
downstream_s = C_L···C_{s+1}, upstream_s = C_{s-1}···C_1. The regular block = the image of dP (the
Morse directions where the Hessian dP^T dP is nondegenerate); its dimension = rank(dP). The singular
core = the complement (the fibre-tangent ⊕ the bottleneck-forced singular directions).

THE SPLIT MECHANISM (to avoid the Mathlib-absent general constant-rank/Morse theorem): exhibit the
regular block as a TRIANGULAR UNIT-PIVOT system — order the regular generators g_1,…,g_q (q=rank(dP))
so each g_i = u_i·z_i + h_i with u_i(0) a UNIT (nonzero) and h_i in already-solved variables; then solve
z_i = (g_i − h_i)/u_i by division-by-unit (analytic, unit denominator), iterated. This is elementary
(no constant-rank theorem). For a chain product the pivots u_i are entries of the up/downstream product
sub-blocks (which are units on the surviving ranks), and the multilinearity makes each pivot variable
occur linearly. A prior result established this for the DEEPEST point (identity corners ⟹ unit pivots)
and argued it for a general optimal v via a gauge-to-identity-corner.

THE HARD CASE. A general optimal v has a "rank pattern" T_v = (t_1,…,t_L), t_s = rank(C_s···C_1) (the
partial-product ranks). A "rank-exact" v has t_s = r at every layer (simplest). A "non-rank-exact"
T_v has interior variation (e.g. t = (3,3,2,2,2,0): ranks rise/fall mid-chain). A "deep multi-drop"
T_v has MULTIPLE simultaneous interior drops — several layers each dropping rank at once (e.g.
t = (3,2,2,1,0): drops at layers 1 (3→2), 3 (2→1), 4 (1→0); or t = (4,2,2,1,0) etc.). The proposed
serialization is "peel the highest-rank-layer first" — process the drops one at a time in a rank order,
each peel a triangular-unit step on its sub-block.

THE QUESTION (decide WITNESS vs OBSTRUCTION):
Q1. At a deep multi-drop T_v, does the "peel highest-rank-layer first" serialization yield a UNIFORM
    triangular-unit-pivot system — i.e. can the q=rank(dP) regular generators be ordered (across the
    multiple drop layers) so each has a unit pivot in an already-solved-variable-free position? Or do
    the simultaneous drops COUPLE (a generator from drop-layer-A shares its pivot variable with
    drop-layer-B) in a way that blocks a triangular order?
Q2. The pivots u_i are entries of up/downstream product sub-blocks. At a multi-drop v, are these
    sub-blocks still UNITS (invertible on the surviving ranks) at every drop layer simultaneously, or
    can a downstream drop make an upstream layer's pivot sub-block singular (a zero pivot — breaking
    the unit-division)? Distinguish: "each drop layer's pivot lives on its OWN surviving-rank sub-block
    (independent units)" vs "a shared downstream factor couples the pivots and can vanish."
Q3. Is the multi-drop genuinely a SERIALIZATION of single-drop steps (process leftmost/highest drop,
    reduce to a chain with one fewer drop, recurse — each step a clean triangular-unit peel on a strict
    sub-block), analogous to how a partial-drop resolution serializes one rank-unit at a time? Or does a
    multi-drop have IRREDUCIBLE coupling that a single-drop analysis misses?
Q4. NET: does the L2-at-v split serialize to triangular-unit-pivot at ARBITRARY T_v (then it is
    formaliser-scale, the same character as the rank-exact/deepest case)? Or is there a deep multi-drop
    T_v where the serialization fails and the split genuinely needs the abstract constant-rank/Morse
    theorem? If it fails, give the SMALLEST T_v that breaks it.
</task>

<output_contract>
Answer Q1–Q4 in order, ≤180 words each. For Q4 end with one line:
VERDICT: WITNESS (serializes triangular-unit at all T_v) | OBSTRUCTION: <smallest breaking T_v + the exact coupling that forces constant-rank>.
Mark each claim [FACT] (forced by the stated algebra) or [INFERENCE] (judgement). Do NOT rubber-stamp;
if the highest-rank-first serialization hides a coupling at a multi-drop, give the minimal counter-structure.
</output_contract>

<grounding_rules>
Reason about matrix-chain products, Schur complements, the linear part dP of the product map, unit-pivot
(triangular Gaussian) elimination vs the abstract constant-rank/Morse-splitting theorem, and multilinearity.
The load-bearing distinction: "the regular block serializes into per-drop-layer triangular-unit peels
(elementary, formaliser-scale)" vs "a multi-drop has coupled pivots that cannot be triangularized without
the abstract constant-rank theorem (Mathlib-absent)". Flag inference vs forced-fact explicitly.
</grounding_rules>
