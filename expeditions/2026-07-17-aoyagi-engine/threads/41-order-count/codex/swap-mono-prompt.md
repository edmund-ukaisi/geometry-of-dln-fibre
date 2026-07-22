<task>
Lean 4 (Mathlib v4.29) proof-strategy for ONE arithmetic lemma. All quantities are naturals ℕ;
truncated subtraction. I need the CLEANEST tactic strategy (which case-splits, which competitor
instantiations of the minimiser hypotheses, ideally closing each case by `omega`). I do NOT need
polished Lean code — I need the decomposition that makes it go through, and any pitfall.

DEFINITIONS (exact):
  swapR (P X Q A B : ℕ) : ℕ :=
    if A ≤ B ∧ B - A ≤ P - X then X + (B - A)
    else if B < A ∧ A - B ≤ X - Q then X - (A - B)
    else P + Q - X
  swapFℤ (P X Q A B : ℕ) : ℤ := ((P:ℤ)-X)*((A:ℤ)-X) + ((X:ℤ)-Q)*((B:ℤ)-Q)   -- parabola in X

LEMMA (swapR_mono_of_min):  goal  swapR P X Q A B ≤ swapR P' X' Q' A B
Hypotheses:
  ranges (unprimed):  Q ≤ X, X ≤ P, X ≤ A, Q ≤ A, Q ≤ B
  ranges (primed):    Q' ≤ X', X' ≤ P', X' ≤ A, Q' ≤ A, Q' ≤ B
  coord order:        P ≤ P', X ≤ X', Q ≤ Q'    (same A, B on both sides)
  minimality (hmin):  ∀ Y:ℕ, Q ≤ Y → Y ≤ P → Y ≤ A → swapFℤ P X Q A B ≤ swapFℤ P Y Q A B
  minimality (hmin'): ∀ Y:ℕ, Q' ≤ Y → Y ≤ P' → Y ≤ A → swapFℤ P' X' Q' A B ≤ swapFℤ P' Y Q' A B

CONTEXT / already established (numerically verified 0-fail over all such tuples, R≤7, and on real
binding profiles L≤5):
- The lemma is TRUE. Atomic swapR-in-X monotonicity is FALSE without hmin/hmin' (counterexample
  (P,X,Q,A,B)=(1,0,0,0,1)->1 vs (1,1,0,0,1)->0), so the minimiser hyps are load-bearing.
- swapFℤ is a parabola in X with vertex at X* = (P+A-B+Q)/2. The finite difference is linear:
  swapFℤ P (X+1) Q A B - swapFℤ P X Q A B = 2*X - P - A + 1 + B - Q  (over ℤ).
  So from hmin: F(X) ≤ F(X+1) [valid when X+1≤P and X+1≤A] gives   2X ≥ P+A+Q-B-1.
              F(X) ≤ F(X-1) [valid when X-1≥Q i.e. X>Q]        gives   2X ≤ P+A+Q-B+1.
  i.e. X is essentially round((P+A-B+Q)/2) clamped to [Q, min(P,A)].
- I intend: rcases le_or_lt A B; in each, both swapR reduce to a 2-branch `if` (the other arm dead),
  giving a 4-case grid (unprimed branch × primed branch). Per case I want to feed omega the ranges,
  coord-order, the two branch (in)equalities from split_ifs, and the RIGHT instantiations of hmin /
  hmin' (as linear facts via the finite-difference identity), then `omega`.
- The subtle cases (A ≤ B): unprimed = translation-up (X+(B-A)), primed = reflection (P'+Q'-X'):
  need X+(B-A) ≤ P'+Q'-X'. And the mirror in the B<A regime. These seem to need BOTH minimalities.
- Endpoint pitfall: the neighbour inequalities F(X)≤F(X±1) are CONDITIONAL (need X+1≤min(P,A) resp
  X>Q). At an endpoint they are unavailable; must be handled (e.g. X=P or X=A or X=Q sub-splits).
</task>

<output_contract>
1. VERDICT: is the rcases-le_or_lt-A-B + 4-case + omega plan the cleanest, or is there a materially
   simpler route (e.g. a single clamp-formula characterization of swapR on minimisers, proven once,
   from which monotonicity is pure omega)? Recommend ONE.
2. For the RECOMMENDED route, give the case grid and, PER CASE, the EXACT competitor point(s) to
   instantiate hmin/hmin' at (e.g. "hmin at Y=X+1", "hmin' at Y = P+Q-B", …) and note which cases
   need which minimality (or none). Be concrete about the endpoint sub-splits needed so that every
   neighbour inequality used is actually valid.
3. PITFALLS: truncated-ℕ-subtraction traps in swapR/swapFℤ; anything that will make omega fail
   silently (e.g. needing a `push_cast`/finite-difference `have` before omega can use hmin).
Keep it tight; this is a strategy consult, not a code dump.
</output_contract>

<grounding_rules>
Mark any claim you are INFERRING vs one you can VERIFY by the given algebra. If you suspect the
lemma or a sub-case is false as stated, say so and give the tuple. Do not invent Mathlib lemma names.
</grounding_rules>
