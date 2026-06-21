<task>
You are a decorrelated second reviewer on a Lean 4 + Mathlib formalisation. I am the fidelity
reviewer; I want your independent mathematical read on TWO questions about a "codimension bridge"
module. Do NOT trust my framing; judge the math itself.

SETTING. Over an algebraically closed field k, σ a finite type, R = MvPolynomial σ k (the polynomial
ring = coordinate ring of affine space A^|σ| over k, where |σ| = Nat.card σ = dim of the ambient
affine space). For a subset Z ⊆ (σ → k) (a point set in affine space), Mathlib defines:
  - vanishingIdeal k Z : Ideal R   (the ideal of polynomials vanishing on Z)
  - Ideal.height p : ℕ∞             (the supremum of lengths of chains of primes descending from p)
  - ringKrullDim (R ⧸ p) : WithBot ℕ∞   (Krull dimension of the quotient ring; ⊥ iff trivial ring)

The module proves and USES this already-established catenary identity (call it L5), valid over ANY
field, for any PRIME p of R = MvPolynomial (Fin n) k, transported to a Fintype index σ:
  (height p : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = (Nat.card σ : WithBot ℕ∞).

It then DEFINES the "variety dimension":
  varietyDim Z : ℕ∞ := (ringKrullDim (R ⧸ vanishingIdeal k Z)).unbotD 0
i.e. take the WithBot ℕ∞ Krull dimension of the coordinate ring of Z, and replace a ⊥ result by 0.

And proves the BRIDGE HEADLINE, under the hypothesis hp : (vanishingIdeal k Z).IsPrime:
  (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞)        [additive, in ℕ∞]
  (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z        [subtraction corollary, ℕ∞]
The proof: from L5 at p = vanishingIdeal k Z; since p is prime, R/p is nontrivial, so
ringKrullDim(R/p) ≥ 0 hence ≠ ⊥, so unbotD 0 recovers the genuine value m; cast WithBot ℕ∞ down to ℕ∞.

QUESTION 1 (bridge fidelity). Does "height(vanishingIdeal Z) + varietyDim Z = Nat.card σ" faithfully
state the classical fact "geometric codimension of Z = (dimension of ambient affine space) − (dimension
of Z)" for an IRREDUCIBLE affine variety Z? In particular:
  (a) Is height(vanishingIdeal Z) the correct algebraic encoding of the codimension of the variety
      V(vanishingIdeal Z) (= Zariski closure of Z) in affine n-space?
  (b) Is ringKrullDim(R ⧸ vanishingIdeal Z) the correct encoding of dim of that variety?
  (c) Is "(vanishingIdeal k Z).IsPrime" the right algebraic stand-in for "Z is an irreducible variety"?
      Note over an alg. closed field, prime vanishing ideal ⟺ irreducible closed set. But Z here is an
      ARBITRARY subset, not assumed closed. Does prime vanishingIdeal silently force/assume anything
      about Z, and is the identity still the honest "codim of the Zariski closure of Z" statement?

QUESTION 2 (unbotD 0 soundness). varietyDim uses .unbotD 0 to coerce WithBot ℕ∞ → ℕ∞, defaulting ⊥↦0.
ringKrullDim is ⊥ exactly when the ring is trivial (the zero ring), i.e. when vanishingIdeal Z = ⊤
(Z empty over alg closed field, or no points). Is it SOUND that the bridge headline only fires under
hp : prime (which makes R/p nontrivial, so dim ≠ ⊥, so unbotD 0 is faithful and never silently swallows
a real ⊥)? Is there any case where unbotD 0 could turn a genuinely-⊥ (or genuinely-undefined) dimension
into a misleading "0" that makes the additive identity TRUE-BUT-VACUOUS or FALSE-yet-accepted? Could the
subtraction form "height = card − varietyDim" hide a truncated-subtraction artifact in ℕ∞ (where
a − b = 0 when a < b)? The proof claims varietyDim Z ≤ Nat.card σ makes it lossless — is that right
under the prime hypothesis?

Also: is the additive form genuinely more faithful/bedrock than the subtraction form in ℕ∞, given ℕ∞
has truncated (lossy) subtraction? Or is this a distinction without a difference here?
</task>

<output_contract>
Two sections, QUESTION 1 and QUESTION 2. For each, a verdict line (FAITHFUL / SOUND / or the specific
defect), then at most 5 bullet points of reasoning. End with a one-line OVERALL: does the bridge
honestly capture "codim = ambient − dim", and is unbotD 0 sound? Be terse and concrete; name the exact
edge case if you find one.
</output_contract>

<grounding_rules>
This is a math-fidelity read, not a Lean-syntax check. State plainly when something is a mathematical
FACT (provable/standard) vs an INFERENCE about what the Lean encoding does. If you suspect a defect but
cannot confirm without seeing the Lean source, say "POSSIBLE DEFECT, needs source check" and name what
to check. Do not invent Mathlib lemma names.
</grounding_rules>
