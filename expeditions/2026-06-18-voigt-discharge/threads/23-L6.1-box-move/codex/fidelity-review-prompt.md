<task>
You are a skeptical Lean-4 / algebraic-geometry reviewer doing a FIDELITY audit (does the
Lean statement say what it claims to say?). Do NOT trust the docstring; reason from the
statements. Context: equioriented type-A quiver 0→1→2 with dimension vector d=(1,2,1).
A tuple A assigns edge0 : 2×1 matrix (v0→v1) and edge1 : 1×2 matrix (v1→v2), over a field k.
The group G_d = GL(d_0)×GL(d_1)×GL(d_2) acts by (P•A)_i = P_{i+1}·A_i·(P_i)^{-1}.
orbitSet U = { canonicalCoord(A) : ∃ P∈G_d, P•U = A }  (the orbit, a point set in k^{RepCoord}).

Two Lean headlines (Mathlib `MvPolynomial.zeroLocus`/`vanishingIdeal`, both at value-field=coeff-field=k):

ENGINE (general d): given U D : Tuple d and a tuple of univariate polynomials Fpoly,
 if tupleEval Fpoly 0 = D  (entrywise eval at t=0)
 and ∀ t≠0, ∃ P∈G_d, P•U = tupleEval Fpoly t
 then canonicalCoord D ∈ zeroLocus(vanishingIdeal(orbitSet U)).
The proof feeds an L6.0 limit lemma: a polynomial curve whose t≠0 points lie in a set Z has its
t=0 limit in zeroLocus(vanishingIdeal Z) = Zariski closure of Z.

WITNESS (d=(1,2,1)): U = upstairs (edge0=[[1],[0]], edge1=[[1,0]]); D = downstairs
(edge0=[[1],[0]], edge1=[[0,1]]). Family F t : edge0=[[1],[0]], edge1=[[t,1]].
Claimed: F 0 = D; and for t≠0 the base change P0=I, P1=[[1,-1/t],[0,1]], P2=[t] gives P•U = F t.
Headline: canonicalCoord D ∈ zeroLocus(vanishingIdeal(orbitSet U)).

Questions:
1. Does "canonicalCoord D ∈ zeroLocus(vanishingIdeal(orbitSet U))" faithfully express
   "D is in the Zariski closure of the orbit of U"? Any gap between this and the intended claim
   (e.g. closure-of-orbit vs orbit-of-closure, value field issues, radical/Nullstellensatz subtleties)?
2. Is the t≠0 hypothesis "∃P, P•U = F t" the right thing (points in the ORBIT, not the closure)?
   Is the direction P•U = F t (not P•F t = U) correct for "F t ∈ orbit(U)"?
3. Is the witness a GENUINE non-vacuous instance, or could it be vacuously true / a restatement?
   Verify by hand: P1·[[1],[0]]·P0^{-1} = [[1],[0]] and P2·[[1,0]]·P1^{-1} = [[t,1]] for the given P.
4. Rank patterns: upstairs (r01,r12,r02)=(1,1,1), downstairs=(1,1,0). Is downstairs genuinely a
   DEGENERATION of upstairs (lower in orbit-closure order), i.e. r02 drops 1→0 while r01,r12 hold?
   Does that match the box move M_{[0,2]}⊕M_{[1,1]} ⇝ M_{[0,1]}⊕M_{[1,2]}?
5. Any way the engine's conclusion could be WEAKER or STRONGER than the box-move claim intends?
</task>

<output_contract>
Five numbered answers, terse. For each, a verdict (OK / CONCERN: <what>) and the one-line reason.
End with one line: OVERALL FIDELITY = PASS or PASS-WITH-NOTES or FAIL, and the single most important caveat.
</output_contract>

<grounding_rules>
Distinguish what you can VERIFY by direct computation (the 2×2/1×2 matrix arithmetic, rank patterns)
from what is INFERENCE about Lean/Mathlib semantics you cannot run. Flag each. If a claim needs a
Mathlib fact you are unsure of, say so explicitly rather than asserting it.
</grounding_rules>
