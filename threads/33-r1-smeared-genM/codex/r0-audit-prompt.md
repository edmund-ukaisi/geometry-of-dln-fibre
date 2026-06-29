<task>
Verify a discrete-optimization classification claim that decides whether a Lean formalisation branch
is BOUNDED or a WALL. Setup (deep linear network rank-flow at depth L=2, M = (M0,M1,M2) ∈ ℕ³):

Admissible exponent vectors T = (T0, T1) with: T0 ∈ [0, min(M0,M1)], T1 = 0 (forced: last = 0),
T0 ≥ T1. The Aoyagi value to minimise over T:
  Mval(T0) = (M0 − T0)·(M1 − T0) + T0·M2.
Let r = argmin T0 (the minimiser; "deepRank"). minAdm = min value = Mval(r) (∈ ℕ, ≥ 0).

Derived quantities at L=2 (I have transcribed these from the Lean defs Text/Wext/tach/InteriorDrop):
  deepRank = r,  deepRows = M1.
  InteriorDrop(M)  ⟺  (M2 > 0) ∧ (r < M0) ∧ (r < M1).
  BoundaryClean(M) ⟺  ¬InteriorDrop ∧ r = M1.
  BoundarySmeared(M) ⟺ ¬InteriorDrop ∧ r < M1.
These three are exclusive+exhaustive (proven in Lean).

The SMEARED chart I am building needs r ≥ 1 (it places a radial pivot in an r-dimensional rank block;
r = 0 makes the unit U = ‖P₁·H̄‖² an empty sum = 0, degenerate — a WALL for that chart).

CLAIM TO ADJUDICATE: in the regime the spine actually invokes the smeared branch — namely
1 ≤ minAdm M AND BoundarySmeared M — we ALWAYS have r ≥ 1. My argument:
  (i) 1 ≤ minAdm forces M0 ≥ 1, M1 ≥ 1, M2 ≥ 1 (if any Mi were 0 with the relevant index, minAdm = 0).
  (ii) Suppose r = 0. Then minAdm = Mval(0) = M0·M1 ≥ 1 (from (i)), so M0 ≥ 1 ∧ M1 ≥ 1, and M2 ≥ 1.
       Then InteriorDrop holds: M2 > 0 ∧ 0 < M0 ∧ 0 < M1. So M is INTERIOR, NOT smeared.
  (iii) Hence BoundarySmeared (which includes ¬InteriorDrop) excludes r = 0. So r ≥ 1. ∎

A brute sweep over M ∈ [0,8]³ confirms: 0 SMEARED cases with r = 0 and minAdm ≥ 1; all 120 such r=0
minAdm≥1 cases classify INTERIOR.

The OTHER obligation (a): deepRank = r ≤ admBound(0) = min(M0,M1) ≤ M0, directly from T0 ∈ [0,min(M0,M1)].
</task>

<output_contract>
1. Is the (i)→(iii) argument SOUND? Specifically scrutinise step (i): does 1 ≤ minAdm really force
   M0,M1,M2 ≥ 1 at L=2? (Give the exact implication or a counterexample.) And step (ii): is the
   InteriorDrop condition at L=2 exactly (M2>0 ∧ r<M0 ∧ r<M1), so r=0 with all Mi≥1 ⟹ interior?
2. Any width regime where r=0 is SMEARED with minAdm≥1 that the [0,8]³ sweep would miss (e.g. large
   asymmetric widths, or a non-uniqueness-of-argmin subtlety: if there are multiple argmins, does the
   smeared branch ever pick r=0 while another argmin gives r≥1)? Note: the Lean tStar is an ARBITRARY
   argmin (Classical.choose); the chart claims to be minimizer-INDEPENDENT.
3. VERDICT for obligation (b) "r≥1 in the smeared branch (minAdm≥1)": BOUNDED (a short lemma) or WALL?
   And for (a) "deepRank ≤ M0": BOUNDED or WALL?
Be concise. Flag inference vs proof.
</output_contract>

<grounding_rules>
Reason from the optimization + the stated L=2 derived conditions. The InteriorDrop/Clean/Smeared
conditions are GIVEN (transcribed from Lean, exclusive+exhaustive). If the argmin-nonuniqueness point
in (2) threatens minimizer-independence, say so explicitly — that is the subtle risk.
</grounding_rules>
