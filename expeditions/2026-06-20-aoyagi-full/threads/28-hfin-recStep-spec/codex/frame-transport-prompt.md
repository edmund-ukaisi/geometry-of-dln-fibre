<task>
I am formalising in Lean 4 + Mathlib (lintegrals over ℝⁿ boxes) the LAST gap of a
deep-linear-network RLCT computation: the "frame transport" for the (3,3,4) case.

SETUP (all concrete, no abstraction):
- A0 is a 3×3 real matrix, A1 is a 3×4 real matrix. Their product A0·A1 is 3×4.
- frobSq(M) = ∑_{ij} M_{ij}²  (entrywise squared Frobenius norm).
- I have a clean measure-preserving reshape (DONE, mirroring a banked (4,4,2,2) precedent)
  reducing the target box integral to exactly:

      I := ∫_{A0 ∈ [-1,1]^{3×3}} ∫_{A1 ∈ [-1,1]^{3×4}}  frobSq(A0·A1)^{−c'}   dA1 dA0

  and I must prove  I < ∞  for  2 < c' < 4.  (The c' ≤ 2 case is separately easy.)

- I have a BANKED, sorry-free lemma `resolved334_lt_top`:

      ∫_{Δ ∈ [-1,1]^{2×2}} ∫_{S ∈ [-1,1]^{2×4}} ∫_{T ∈ [-1,1]^4}
          (∑_i T_i² + frobSq(Δ·S))^{−c'}  dT dS dΔ   < ∞     for 2 < c' < 4.

  (Δ is 2×2, S is 2×4, T is a 4-vector. This is the disjoint-sum normal form:
   a 4-dim Morse spectator T ⊕ the corank-2 core frobSq(Δ·S).)

GOAL: a measure-theoretic argument bounding I by (a constant times) the resolved334 integral,
i.e. a cover-up-to-null + per-chart change-of-variables that brings frobSq(A0·A1) over the
9+12=21 box coordinates into the ‖T‖² ⊕ frobSq(Δ·S) normal form.

WHAT I KNOW about the geometry (from a verified pen-and-paper cert):
- The singularity of frobSq(A0·A1) as c'→4 is at the rank-drop locus of the product / of A1.
- The achiever blow-up chart (single chart, realising the deepest point, BANKED) factors
  frobSq(A0·A1)∘φ = u₀²·U where U = a²·(1+τ₁²+τ₂²+τ₃²) ⊕ ‖c·(1,τ) + Δ·S‖²
  — a Schur-frame: pivot u₀, a "T-row" a·(1,τ₁,τ₂,τ₃) (the Morse spectator, 4 entries),
  and a 2×4 residual block c·(1,τ) + Δ·S. |det Dφ| = |u₀|⁷·|u₁|².
- The design doc proposes an r²-entry argmax atlas (here r relates to the 3×3 / rank structure):
  cover by max-modulus-entry charts, each a radial blow-up Δ=a·R, per-chart Jacobian |a|^{r²−1},
  integrand a²·‖R·S‖², inner recursion by nested Schur-complement minor-pivot neighbourhoods.

THE TENSION I want your read on:
The banked `resolved334_lt_top` was proved by an "S-first transpose-fibre" route that AVOIDS
the nested minor-pivot recursion entirely — it directly resolves ∫∫ frobSq(Δ·S)^{−c''} < ∞ for
c'' < 2 via a transpose + fibre lemma + 2×2 Morse leaf. So the INNER core is already closed.
The remaining question is purely the OUTER reduction: how to get from
   I = ∫∫ frobSq(A0·A1)^{−c'}   (21 raw box coords, the rank-drop singularity)
to a bound by the resolved normal form, WITHOUT re-deriving the inner recursion.

QUESTIONS (this is the decision I'm buying):
1. Is there a SIMPLER outer reduction than the full r²-entry argmax atlas, given that the inner
   core is already banked? Specifically: can I integrate out A0 (the 3×3 left factor) FIRST via a
   fibre-type bound, OR slice/blow-up only along the minimal singular directions, reducing the
   3×3·3×4 problem to the 2×2·2×4 + 4-dim-Morse normal form in FEWER charts?
2. The (4,4,2,2) precedent resolved its analog by a PURE iterated fibre bound (no blow-up) because
   its threshold (2) was reachable by the product-of-fibre-thresholds. For (3,3,4) the pure fibre
   route caps at min(3/2,...) = 3/2 ≪ 4, so a blow-up IS needed. Confirm: is the obstruction
   genuinely that the A1-rank-drop locus must be resolved by a non-trivial (non-MP) change of
   variables — i.e. there is no measure-preserving global reparametrization that lands the normal
   form, and a Jacobian-weighted cover (with |a|^{power} divisors) is unavoidable?
3. Rank the candidate Lean structures by total lemma-count / risk:
   (a) full r²-entry argmax atlas + recStep over all charts (the design doc's N4);
   (b) a reduced cover keying only on the rank-2-vs-rank-3 distinction of A1 (one blow-up of the
       "which 2×2 minor of A1 is the pivot" type, 6 charts, each landing the normal form);
   (c) integrate-A0-first fibre bound, then a single radial blow-up on the residual.
   For the cheapest viable one, sketch the chart map(s), the Jacobian, and how the integrand lands
   in the ∑T² + frobSq(Δ·S) shape that `resolved334_lt_top` consumes.
4. Honest bound on lemma count and the single highest-risk Lean step for your recommended route.
</task>

<output_contract>
Four numbered sections matching Q1–Q4. Lead each with a one-line verdict, then the reasoning.
Be concrete about the chart maps and Jacobians (give explicit formulas where you can).
For Q3, give the lemma-count estimate per option and pick one.
Keep under ~900 words. No Lean syntax needed — math + structure.
</output_contract>

<grounding_rules>
Distinguish (i) what is forced by the rank geometry (a theorem) from (ii) a heuristic /
plausible-but-unchecked structural suggestion. Flag any step where you are guessing about the
measure-theoretic legality (e.g. whether a proposed cover is genuinely up-to-null, whether a
Jacobian divisor is integrable at the claimed threshold). If you think the whole "reduce-to-
resolved334" framing is the wrong move and I should prove I<∞ directly by a self-contained
fibre+blow-up chain, say so and outline that instead.
</grounding_rules>
