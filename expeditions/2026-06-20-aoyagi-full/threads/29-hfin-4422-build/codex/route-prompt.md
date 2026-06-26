<task>
I am formalising in Lean 4 + Mathlib a finiteness statement and want the CLEANEST mathematical
route (one that minimises Lean machinery), then a sanity check it is TRUE.

GOAL (to prove):
  ∫_{(−1,1)^28} ‖A0 · A1 · A2‖_F^{−2c'}  dμ  <  ∞   for every real c' with 0 ≤ c' < 2,
where the 28 integration variables are the free Cartesian entries of:
  A0 : 4×4 real matrix  (16 entries),
  A1 : 4×2 real matrix  (8 entries),
  A2 : 2×2 real matrix  (4 entries),
‖·‖_F is the Frobenius norm, the product A0·A1·A2 is a 4×2 matrix, μ is Lebesgue on the box (−1,1)^28.
(The exponent is −c' applied to ‖P‖^2, i.e. (‖P‖^2)^{−c'} = ‖P‖^{−2c'}.)

CONTEXT / what I already have as Lean bricks:
  - radial_ball_iff: on EuclideanSpace ℝ (Fin (m+1)), ∫_{ball 0 R} ‖x‖^s < ∞  ⟺  s > −(m+1).
    So a pure n-dimensional sum-of-squares ∫_{box} (Σ_{i<n} x_i^2)^{−c'} < ∞ ⟺ c' < n/2. (PROVEN, reusable.)
  - The singular locus is {A0·A1·A2 = 0}. The number 2 = ½·minAdm where minAdm = 4 is the codimension
    of {A2=0} (the deepest-factor vanishing), the binding stratum.
  - I can do measure-preserving shears / linear changes of variables, Tonelli/Fubini, monotone domination
    (W ≥ 0 ⟹ (Σ P_i^2 + W)^{−c'} ≤ (Σ P_i^2)^{−c'} for c' ≥ 0), and a radial blow-up A2 = a·R with
    Jacobian |a|^{r^2−1}.

The "official" plan (from a design spec) is a rank-stratified recursion: radial-blow-up the deepest
2×2 factor A2 = a·R, stratify by rank(R)=j, peel a Morse block, recurse on a strictly-lower corank core,
terminate by radial_ball_iff. That is HIGH-effort in Lean (atlas of r^2 charts, Schur normal form,
WellFounded recursion). I want to know if there is a SHORTER route SPECIFIC to (4,4,2,2).

CANDIDATE SHORTCUT I am considering (please verify or refute):
  Bound ‖A0·A1·A2‖^2 BELOW by a sum of squares in a *subset* of the coordinates, after a measure-preserving
  linear change, so that the integral is dominated by a pure n-dim ∫(Σ x_i^2)^{−c'} with n ≥ 4 (giving
  c' < 2). Concretely: is it true that on the box, ‖A0·A1·A2‖^2 ≥ (const) · ‖A2‖^2 · (something bounded
  below)? NO — A0,A1 can be near-singular making the product small even when A2 is not. So a naive global
  lower bound by ‖A2‖^2 FAILS. The integral's finiteness is genuinely a statement about the *generic*
  rank-4·rank-2 situation, with measure-zero bad strata where A0 or A1 drop rank.

QUESTIONS:
  1. Is the GOAL actually TRUE (c' < 2 ⟹ finite)? Give the heuristic exponent count: near a generic point
     of {A0·A1·A2 = 0}, what is the codimension, and does the worst stratum give threshold exactly 2?
     Are there DEEPER strata (A0 or A1 dropping rank simultaneously with A2) that could lower the threshold
     below 2 and make the integral DIVERGE for some c' < 2? This is the kill-condition I most need checked.
  2. Among these routes, rank by LEAST Lean effort, assuming the bricks above:
     (a) the full rank-stratified recursion (spec's plan);
     (b) a single measure-preserving change of variables that exhibits ‖A0·A1·A2‖^2 as
         (clean 4-dim sum of squares in new coords) + (W ≥ 0), VALID generically, then monotone-dominate
         + radial_ball_iff + Tonelli — analogous to the (2,2,2) δ-block shear that turned the deepest block
         into a clean Σ^4 squares;
     (c) any other shortcut.
  3. For route (b): does a GLOBAL (whole-box) measure-preserving linear shear exist that turns
     ‖A0·A1·A2‖^2 into Σ_{i<4}(linear-in-A2-entries)^2 + nonneg, OR is the rank-drop of A0/A1 a genuine
     obstruction forcing the stratification? If it is an obstruction, is it confined to a measure-zero set
     that can be handled by an a.e. argument (so the clean shear works a.e.)?
</task>

<output_contract>
  Four sections, terse:
  1. TRUE/FALSE + the exponent-count argument for the threshold, and explicit verdict on whether any
     deeper stratum lowers the threshold below 2 (the divergence kill-condition).
  2. Ranked routes (least Lean effort first), one-line justification each.
  3. For the top route: the precise change of variables / domination, written explicitly enough to
     transcribe (name the new coordinates and the exact inequality).
  4. The single biggest risk in the top route + the cheapest way to de-risk it.
</output_contract>

<grounding_rules>
  Distinguish what you can prove vs. what is heuristic. If the exponent count is heuristic, say so.
  If route (b)'s global shear does NOT exist, say so plainly and do not invent one — the stratification
  may genuinely be necessary, and I need to know that before spending Lean effort. Flag any step where
  the rank-drop of A0 or A1 breaks the argument.
</grounding_rules>
