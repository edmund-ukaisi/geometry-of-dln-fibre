<task>
Lean 4 + Mathlib. I need a STRATEGY (not code) for a bridge lemma in a resolution-of-singularities
formalisation. Coordinates u : Fin D → ℝ. A fixed finite S : Finset (Fin D) (a "center"/support block),
all contained in one "layer" — there is a fixed X : Finset (Fin D) with S ⊆ X (X = the layer's coords).

Definitions (paraphrased faithfully; V = univ throughout, so ignore V):
  IgnoresCoords c S  :=  ∀ w, ∀ m ∈ S, ∀ t, c (Function.update w m t) = c w   -- c does not read S-coords
  AffineOn f X       :=  ∃ a b, IgnoresCoords a X ∧ (∀ x∈X, IgnoresCoords (b x) X)
                                ∧ ∀ u, f u = a u + ∑_{x∈X} b x u · u x         -- total degree ≤1 in X

I have a fixed function F : (Fin D → ℝ) → ℝ satisfying BOTH:
  (H1) SUPPORT-DECOMP on S:  ∃ c, (∀ i, Continuous (c i)) ∧ ∀ u, F u = ∑_{i∈S} c i u · u i.
       [note: nothing says c i ignores S — the c may itself read S-coords.]
  (H2) AffineOn F X   (with S ⊆ X).

I WANT (the "bridge"): a NEW support-decomposition on S whose coefficients IGNORE S:
  (GOAL) ∃ c', (∀ i, Continuous (c' i)) ∧ (∀ u, F u = ∑_{i∈S} c' i u · u i) ∧ (∀ i, IgnoresCoords (c' i) S).

Why I need it: a downstream "crux" lemma consumes exactly (GOAL) (the IgnoresCoords-S coefficients let it
show c' i (σ u) = c' i (τ u) for two maps σ,τ that AGREE off S). H1's raw c does not suffice.

Context facts that may or may not help:
  - From (H1) at u=0: F 0 = 0.
  - S ⊆ X, and AffineOn's a, b_x ignore X ⊇ S, hence ignore S.
  - The two decompositions (H1's ∑_{i∈S} c_i u_i and H2's a + ∑_{x∈X} b_x u_x) are the SAME F.
  - X ∖ S may be nonempty (X is the uncapped layer, S the capped block).
</task>

<output_contract>
Terse, in this order:
1. VERDICT: Is (GOAL) DERIVABLE from (H1)+(H2)? TRUE / FALSE / TRUE-with-extra-hypothesis. If it needs an
   extra hypothesis, state the WEAKEST one (e.g. "F reads no X∖S coord", or "a ≡ 0", or a uniqueness
   condition), and whether that extra hypothesis is itself derivable from (H1)+(H2).
2. If TRUE: the construction of c' + the key steps, naming the mechanism (uniqueness of the affine
   decomposition over independent coords? a substitution/partial-derivative extraction? restricting the
   AffineOn b_x to S and showing the X∖S part + a cancel?). Which of H1/H2 each step consumes.
3. If FALSE (or needs the extra hyp): the counterexample shape (a concrete F satisfying H1+H2 but where NO
   IgnoresCoords-S decomposition exists), OR why the extra hyp is unavoidable.
4. ALTERNATIVE: instead of the bridge, is it cleaner to RE-PROVE the crux (F(σu)=u_p·F(τu) for center-coord
   maps σ,τ agreeing off S) directly from (H2)'s AffineOn (using a,b_x ignore S) rather than routing through
   an IgnoresCoords-S support-decomp? Sketch which is less Lean-friction.
</output_contract>

<grounding_rules>
Distinguish what FOLLOWS from (H1)+(H2) vs what you ASSUME. If a step needs coords to behave as independent
polynomial variables (they are just real functions here — F is an arbitrary function, not a polynomial),
FLAG it — that is the crux of whether "uniqueness of decomposition" is available. Do not claim a Mathlib
lemma exists at v4.29 unless confident; I verify names.
</grounding_rules>
