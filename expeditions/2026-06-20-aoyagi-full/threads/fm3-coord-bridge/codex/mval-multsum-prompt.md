<task>
I am formalising in Lean 4 (Mathlib) the identity "Aoyagi's Mval = the Le Halleur–Rimányi
quadratic multiplicity form (multSum)" for deep-linear-network fibre codimensions. I need a
DIAGNOSIS of the cleanest proof route and a check on whether the identity is a free ring
identity (admissibility-free) or needs realizability/admissibility hypotheses.

DEFINITIONS (exact Lean, transcribed):

1. Mval — a SINGLE sum over the exponent vector T (the "Kostant exponents"):
   Mval M T = ∑_{j : Fin L} (tPrev M T j − T_j) * (M_{j+1} − T_j)   (over ℤ)
   where tPrev M T j = M_0 if j=0, else T_{j-1}.  M : Fin (L+1) → ℕ, T : Fin L → ℕ.
   (This is Aoyagi p.22: (M_1−t_1)(M_2−t_1) + ∑_{j=2}^L (t_{j-1}−t_j)(M_{j+1}−t_j), t_0:=M_1.)

2. multSum — a QUADRUPLE nested sum over the multiplicity array m̄ of a Kostant list L_data
   (a list of intervals (a,b), 0≤a≤b≤N):
   multSum = ∑_{i∈Icc 1 N} ∑_{u∈Icc i N} ∑_{j∈Icc u N} ∑_{v∈Icc j N}
                m̄_{i-1, j-1} * m̄_{u, v}
   where m̄_{a,b} = #{p ∈ L_data : p = (a,b)} (the interval-multiplicity array).
   This equals finrank of the deformation Ext¹ of the corresponding type-A quiver rep
   (Voigt's formula), = the geometric codim of the orbit.

3. The BRIDGE: a rank pattern r : i,j ↦ ℤ has a "diff array" m̄ = diff(r) (the 2D finite
   difference / Möbius inversion: m̄_{a,b} = r_{a,b} − r_{a-1,b} − r_{a,b+1} + r_{a-1,b+1}).
   For the DLN "cascade achiever" with exponent vector T, the resolution rank pattern is
   r_{ij} = ρ_j + (M_i − ρ_i)   where ρ is the running rank: ρ_0 = M_0, ρ_{j+1} = T_j
   (so ρ = "expSurvivor"). diff(r) of THIS r is the Kostant data whose multSum we compute.

THE CLAIM (controller, via a decorrelated pen-and-paper + codex, says it's TRUE, GENERAL,
ring-provable, NO admissibility): Mval(M,T) = multSum(diff(r(T))) for r_{ij}=ρ_j+(M_i−ρ_i),
as a ring identity in the integer entries of M and T — symbolically multSum − Mval = 0.

WHAT I ALREADY HAVE in Lean (green): Mval (def above); multSum via orbitLinearCodim_eq_multSum
(the quadruple-sum, over a List L_data); multiplicityArray (m̄); the diff/cumulDiff inversion
(RankPattern.cumulDiffEquiv, .symm = diff); A1's lambdaCore_eq_clean (lambdaCore = cleanCore at
an achiever); lambdaCore M = ½·minAdm definitionally (minAdm = (Adm M).inf' Mval).

WHAT I TRIED / the concern: the single-sum (L terms) vs quadruple-sum (≈N⁴ terms over m̄) gap
is large. The quadruple sum must COLLAPSE to the single sum. I worry the collapse silently uses
a property of THIS specific r (the column-constant / cascade structure) that I might mis-state
as "general ring identity" when it actually needs r to come from a valid ρ (admissibility).
</task>

<output_contract>
Respond in exactly these sections, terse:

1. ADMISSIBILITY VERDICT (1 short paragraph): Is Mval = multSum(diff r(T)) a FREE ring identity
   in the entries of M,T (for r_{ij}=ρ_j+(M_i−ρ_i)), with NO admissibility constraint (no T_j ≤
   bounds, no monotonicity)? Or does the quadruple-sum collapse require a property that only holds
   for admissible/realizable T? If it needs a hypothesis, state EXACTLY which and why.

2. THE COLLAPSE (the math): show the key step that reduces the quadruple sum ∑_{i,u,j,v} m̄_{i-1,j-1}·m̄_{u,v}
   to the single sum ∑_j (tPrev−T_j)(M_{j+1}−T_j). What is m̄ = diff(r) explicitly for this r
   (which entries are nonzero, in terms of M,T,ρ)? Where does the quadruple sum factor / telescope?

3. CHEAPEST LEAN ROUTE (ranked, 2–3 options): given the def mismatch (single-sum Mval over Fin L
   vs quadruple-Icc-sum multSum over a List-backed m̄), what is the lowest-friction route? In
   particular: (a) prove m̄=diff(r) has a closed form then substitute + telescope, vs (b) avoid
   the List/intervalDirectSum layer and prove a multSum-of-array form directly, vs (c) something
   else. Name the Mathlib pain points (Icc-sum reindexing, the ℤ-vs-Fin casts).

4. THE OVER-NAME TRAP (1 paragraph): the controller flagged that multSum=cleanCore is a VALUE
   COINCIDENCE AT THE ACHIEVER, not per-stratum; and that the geometric reading (multSum = codim
   of the orbit closure) only holds when diff(r) is a genuine NONNEGATIVE Kostant partition
   (width-monotone M), failing on width-spike M. Does the RING identity Mval=multSum survive on
   width-spike M (where m̄=diff(r) has NEGATIVE entries, so it is NOT a Kostant partition and
   multSum is no longer a geometric codim)? I.e. is the ring identity strictly broader than the
   geometric reading? Confirm or correct.
</output_contract>

<grounding_rules>
Distinguish what you can DERIVE symbolically (the diff(r) entries, the collapse) from what you
INFER about the Lean route (you cannot see my files). Flag any step where you are guessing the
Mathlib lemma name. If the collapse does NOT go through as a free ring identity, SAY SO plainly —
do not force it; that is the most valuable possible answer (it would mean the controller's "general
ring identity" framing is wrong and I must scope it to admissible/realizable T).
</grounding_rules>
