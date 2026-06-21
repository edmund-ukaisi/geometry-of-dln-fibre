<task>
You are a decorrelated second-model fidelity reviewer for a Lean 4 + Mathlib (v4.29) formalisation
of a commutative-algebra lemma. I want your independent opinion on whether the Lean STATEMENT is a
FAITHFUL rendering of the informal mathematical claim — NOT whether the proof compiles (it does; build
is green, sorry-free, axioms = [propext, Classical.choice, Quot.sound]).

INFORMAL CLAIM (the intended mathematics):
"Let R → S be a flat, quasi-finite-at-a-prime morphism of Noetherian commutative rings. Let Q be a
prime of S, and let p = Q ∩ R be its contraction to R (the prime Q 'lies over'). Then Q and p have
the same Krull height: ht(Q) = ht(p). Geometrically: the fibre of Spec S → Spec R over p contributes
nothing to the height of Q, because quasi-finiteness forces Q to be isolated/minimal in that fibre.
Specialises to: an étale R-algebra S preserves prime height."

THE LEAN STATEMENTS (Mathlib v4.29 conventions; `open Algebra`):

  variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

  -- Mathlib defs in play:
  --   `Ideal.under R Q` := `Q.comap (algebraMap R S)`  (contraction of Q to R)
  --   `Algebra.QuasiFiniteAt R Q` := `Algebra.QuasiFinite R (Localization.AtPrime Q)`
  --       (docstring: "S is R-quasi-finite at p if Sₚ is R-quasi-finite; for S essentially
  --        of finite type over R this is equivalent to p being isolated in its fiber")
  --   `Ideal.height` = Krull height of a prime.
  --   `instance over_under : Q.LiesOver (Q.under R)` is automatic.

  theorem Ideal.height_eq_under_of_flat_quasiFiniteAt
      [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
      (Q : Ideal S) [Q.IsPrime] [Algebra.QuasiFiniteAt R Q] :
      Q.height = (Q.under R).height

  theorem Ideal.height_eq_under_of_etale
      [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.Etale R S]
      (Q : Ideal S) [Q.IsPrime] :
      Q.height = (Q.under R).height

The proof routes through Mathlib's going-down height-additivity lemma
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (stacks 00ON: ht(Q) = ht(p) + ht(image of Q
in S/pS)), discharging `HasGoingDown` from `Module.Flat` (instance `HasGoingDown.of_flat`), and proving
the fibre term = 0 from `QuasiFiniteAt.eq_of_le_of_under_eq` (any prime ≤ Q with the same contraction
to R equals Q).

QUESTIONS (answer each, decorrelated — do not assume the formaliser is right):

1. Is `Q.under R` (= `Q.comap (algebraMap R S)`) the correct object for "the prime p that Q lies over"
   (the contraction Q ∩ R)? Any subtlety?

2. Is `Algebra.QuasiFiniteAt R Q` (= `QuasiFinite R (Localization.AtPrime Q)`) the FAITHFUL hypothesis
   for "S is quasi-finite over R at the prime Q"? Does it secretly assume MORE than the informal notion
   (e.g. does it covertly require finite type, or only quasi-finiteness of the single localization)?
   Or LESS (e.g. is it too weak — does the standard 'isolated in its fibre' notion need finite-type /
   essentially-of-finite-type to coincide, and if so does the LEMMA still hold as stated without it)?
   Crucially: is the lemma as stated (no finite-type hypothesis on S) actually TRUE, or is there a
   counterexample where Sₚ is R-quasi-finite but ht(Q) ≠ ht(p)?

3. The headline carries BOTH `[IsNoetherianRing R]` and `[IsNoetherianRing S]`. The informal claim
   names "Noetherian rings". Is requiring R Noetherian (in addition to S) a genuine/expected hypothesis
   for this height-equality, or does it smell like an artifact that should be removable? (It is forced
   here by the cited going-down lemma's section variable.)

4. Is `Etale ⟹ Flat + QuasiFiniteAt` a correct specialisation, with no additional hidden hypotheses
   needed for the étale corollary beyond what étale already gives?

5. Does the name `height_eq_under_of_flat_quasiFiniteAt` overclaim or underclaim relative to the
   statement? Is anything in the informal claim NOT captured, or does the Lean assert MORE than proved?
</task>

<output_contract>
Five numbered sections matching the five questions. For each: a one-word verdict
(FAITHFUL / SUSPECT / MISMATCH / cannot-tell) then 2-5 sentences of justification.
End with a one-line overall verdict: FAITHFUL / FAITHFUL-WITH-CAVEAT / MISMATCH.
Be terse and concrete. If you suspect a counterexample, give it explicitly.
</output_contract>

<grounding_rules>
Distinguish clearly between (a) facts you are confident about from standard commutative algebra /
Mathlib conventions, and (b) inference or suspicion. Flag any claim that depends on Mathlib's exact
v4.29 definitions which you cannot see. Do not assert the lemma is true or false without stating
whether that is a theorem you know or an inference. If you cannot determine faithfulness from the
information given, say cannot-tell and name the missing fact.
</grounding_rules>
