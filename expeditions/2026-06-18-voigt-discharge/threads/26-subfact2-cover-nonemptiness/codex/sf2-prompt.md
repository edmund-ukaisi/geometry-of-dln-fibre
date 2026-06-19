<task>
A combinatorial existence claim about integer "rank patterns" of type A_n. I want you to
independently attempt a PROOF, or find a counterexample, or give a firm verdict that it
requires heavy machinery. Attack it from scratch; do not assume my framing is the right one.

SETUP (all indices integer; vertices 0..n).
- An interval multiplicity array m assigns m_{[a,b]} >= 0 to each interval [a,b], 0<=a<=b<=n.
- Its "rank pattern" is the cumulative sum r_{ij} = sum over intervals [a,b] with a<=i and j<=b
  of m_{[a,b]}, defined for 0<=i<=j<=n. (So r is a "south-west to north-east" cumulant of m.)
- The dimension vector is d_t = sum_{a<=t<=b} m_{[a,b]} = r_{tt}.
- Inversion (second finite difference): m_{[a,b]} = r_{a,b} - r_{a,b+1} - r_{a-1,b} + r_{a-1,b+1},
  with r treated as 0 when index out of range (a<0, b>n, or a>b).
- Two rank patterns are comparable s <= r iff s_{ij} <= r_{ij} for all i<=j.

GIVEN. Two rank patterns s < r arising from multiplicity arrays m(s), m(r) >= 0 with the SAME
dimension vector d (so r_{tt} = s_{tt} = d_t for all t). Define the residual g = r - s >= 0
(componentwise, with g_{ii} = 0 for all i since the diagonals agree). Let supp(g) = {(i,j): i<j, g_{ij}>0}.

Note m(r) - m(s) = diff(g) where diff is the second-difference operator above (linearity), but
m(r) and m(s) are each >= 0 individually.

EXTREMAL CELL. Among cells (i,j) with g_{ij}>0, pick j0 = the minimal such column index j; then
among cells in column j0 with g>0 pick i0 = the maximal such row index i. So:
  - g_{i0,j0} > 0;
  - every column j < j0 is entirely zero in g (g_{i,j}=0 for all i, all j<j0);  [j0-minimality]
  - in column j0, g_{i,j0}=0 for all i > i0.                                     [i0-maximality]

CLAIM TO SETTLE. There exists an interval [a,e] with a <= i0, e >= j0, such that
  (1) m(r)_{[a,e]} >= 1, AND
  (2) the rectangle [a,i0] x [j0,e] = {(i,j): a<=i<=i0, j0<=j<=e} is entirely inside supp(g)
      (i.e. g_{ij} > 0 for every cell in that rectangle).

A SHARPENING I am confident of (please verify, then it is the difficulty isolator):
Because r_{i0,j0} = sum over [a,e] with a<=i0, e>=j0 of m(r)_{[a,e]}, and
g_{i0,j0} = r_{i0,j0} - s_{i0,j0} > 0 with s_{i0,j0} = sum over the same index set of m(s)_{[a,e]} >= 0,
there MUST exist a covering interval [a,e] (a<=i0, e>=j0) with m(r)_{[a,e]} >= 1. So requirement (1)
alone is free. The entire difficulty is whether some such covering interval ALSO satisfies (2)
(rectangle inside supp(g)).

KNOWN NEGATIVE FACTS (verified on >300 instances each), so a naive selector will not work:
  - Taking the maximal axis-aligned rectangle inside supp(g) anchored at (i0,j0): its far corner
    [a,e] can have m(r)_{[a,e]} = 0.
  - Single-row (a=i0) and single-column (e=j0) covering intervals jointly FAIL on some instances.
So the proof cannot be a monotone/greedy selector; it must be a genuine existence argument.

CANDIDATE ROUTES (try whichever you find most promising; invent your own):
  R1. Induction on |supp(g)| or on n: peel the extremal cell; show the residual stays a valid
      difference of two same-d nonneg multiplicity arrays.
  R2. Structural: g is a difference of two cumulant matrices of nonnegative arrays. Does total
      nonnegativity / monotone-staircase structure force the covering rectangle at the extremal corner?
  R3. Contradiction: suppose EVERY covering interval [a,e] (a<=i0,e>=j0, m(r)_{[a,e]}>=1) has a zero
      cell in its rectangle [a,i0]x[j0,e]. Derive a contradiction with nonnegativity of m(s), or with
      i0/j0 extremality.
</task>

<output_contract>
Respond in these sections, terse:
1. VERDICT: one of {PROVED (elementary), COUNTEREXAMPLE, REQUIRES-HEAVY-MACHINERY}, one line.
2. PROOF or COUNTEREXAMPLE or OBSTRUCTION: the actual argument / explicit instance / why it resists.
   If PROVED, give the argument in full with each inequality justified. If you use the inversion
   identity, show the second-difference manipulation explicitly.
3. KEY LEMMA: if proved, the one load-bearing sub-statement, phrased so it could be formalised.
4. CONFIDENCE + what would change your mind.
Distinguish clearly: what you PROVED vs what you CONJECTURE vs what you checked on examples.
</output_contract>

<grounding_rules>
- Do not claim a step is "clear" without the inequality. The setup is small; be concrete.
- If you give a counterexample, give explicit m(s), m(r) as interval lists and I will check it.
- If you reach for Abeasis-Del Fra / lace diagrams / quiver-rep machinery, say so explicitly and
  name the cleanest known proof to port.
- Do not rubber-stamp my sharpening; verify the "(1) is free" claim yourself.
</grounding_rules>
