<task>
Decorrelated fidelity audit of a Lean 4 / Mathlib v4.29 formalisation.

FILE: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/voigt-discharge/lean/DLNFibre/Core/NoetherMonicPositioning.lean
Supporting (imported, already proved):
  /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/voigt-discharge/lean/DLNFibre/Core/PolynomialDimension.lean
  /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/voigt-discharge/lean/DLNFibre/Core/IntegralDimension.lean

Mathlib original the private block is copied from:
  /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/voigt-discharge/lean/.lake/packages/mathlib/Mathlib/RingTheory/NoetherNormalization.lean

CLAIM being audited: for R = MvPolynomial (Fin n) k, k ANY field, p a prime ideal,
the headline `height_add_ringKrullDim_quotient_eq` asserts
  (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = (n : WithBot ℕ∞).
Companion: `height_add_coheight_eq` (order form on PrimeSpectrum:
Order.height p + Order.coheight p = n). The `≤` half (height_add_coheight_le)
is imported. The `≥` half is the new induction core `nat_le_height_add_coheight`.
Mathlib v4.29 has NO IsCatenary / IsEquidimensional / `ringKrullDim = trdeg`,
so the `≥` proof is necessarily self-contained from bricks.

Read the file and answer the 4 questions in the output_contract. Read the
imported files and the Mathlib original if you need to verify a lemma's meaning.
</task>

<output_contract>
Four numbered sections, terse, specifics only:

1. VACUITY. Does `height_add_ringKrullDim_quotient_eq` genuinely assert
   height + dim = n with no hidden vacuity in WithBot ℕ∞ arithmetic?
   (In WithBot ℕ∞: ⊥ + x = ⊥, ⊤ absorbs +.) Could it be trivially/vacuously
   true for any degenerate prime, or is it a real constraint at every prime?

2. INDUCTION SOUNDNESS. Is `nat_le_height_add_coheight` logically valid?
   Focus on: (a) the p=⊥ successor branch (coheight ⊥ = krullDim = n via
   coheight_bot_eq_krullDim, then le_add_self); (b) the p≠⊥ branch — monic
   positioning, peel variable 0 via finSuccEquiv, additive height law
   P.height = q.height + fiber.height with fiber.height ≥ 1, IH on q = P.under;
   (c) the coheight transfer hcoP (coheight p = coheight q, via
   ringKrullDim(R/p) = ringKrullDim((k[x_d])[X]/P) = ringKrullDim(k[x_d]/q)
   and ringKrullDim_quotient_eq_coheight). Any logical gap, off-by-one, or
   misuse of a lemma?

3. p=⊥ WEAKENING. Does the p=⊥ branch (using le_add_self, dropping height ⊥)
   make the proven bound weaker than the `n ≤ height + coheight` it claims,
   or is it sound because height ⊥ = 0?

4. HYPOTHESES / NAMING. Any hypothesis stronger than needed (e.g. Field where
   CommRing suffices, an unused Noetherian/Infinite/IsAlgClosed)? Any name that
   overclaims relative to what is proved?
</output_contract>

<grounding_rules>
- Distinguish OBSERVED (you read it in the file) from INFERRED (you reason it
  should hold). Tag each finding.
- Do NOT propose Lean code edits. Diagnosis only.
- If a lemma's behaviour is load-bearing and you cannot confirm it from the
  files, say so explicitly rather than assuming.
</grounding_rules>
