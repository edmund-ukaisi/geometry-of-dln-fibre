<task>
Lean 4 + Mathlib (v4.29). I am formalising one step of Aoyagi's resolution-of-singularities
recursion for deep linear networks (the coupled corank≥2 "Case 1"). I need a design review of the
cleanest ABSTRACT matrix statement for the "Q̂ cofactor" machinery, and a check of whether it is
even needed given a simpler route.

SETUP (all functions are ℝ-valued on ℝ^D = (Fin D → ℝ), continuous near 0; "the deepest point" is 0):
- A family F : Fin M → ℝ^D → ℝ ("generators"). g : ℝ^D → ℝ^D (a coordinate map so far).
- Interior invariant `StepInv F g b resid q V` (V an open nbhd of 0) asserts:
  (i) each q i j : ℝ^D→ℝ is ContinuousOn V;
  (ii) deepest-point vanishing: ∀ i, (F i ∘ g) 0 = 0;
  (iii) factorization: ∀ u∈V, ∀ i, (F i∘g) u = ∑_j (q i j u) · (b u · resid j u).
  [b : ℝ^D→ℝ is the dominant monomial; resid : Fin nR → ℝ^D→ℝ the residual block entries.]
- One recursion step post-composes g with σ = sh ∘ blockBlowupMap S p, where:
  * blockBlowupMap S p w j = (if j = p then w p else if j∈S then w p * w j else w j)  -- block-center
    blow-up: pivot p∈S ↦ w_p; other center coords j∈S\{p} ↦ w_p·w_j; SPECTATORS j∉S ↦ w_j (FIXED).
  * sh is a unipotent shear (Jacobian ≡ 1), sh 0 = 0.
- The child dominant law: b' u = (w_p)^δ · b(σ u), δ ∈ {0,1} a state property ([J=0]).
- The divisibility chain b_1 | b_2 | ... | b_M holds (b_1 = the dominant `b`; the others are folded
  into resid/q at the StepInv abstraction).

I HAVE ALREADY PROVEN (sorry-free, axiom-clean) the EXACT-DIVISION atom:
  for j∈S,  blockBlowupMap S p w j = w p * (if j=p then 1 else w j)   [continuous/analytic quotient],
and its center-combination corollary. Via this, for the δ=1 child I can build a child StepInv by
taking nR'=1, resid'=(fun _:Fin 1↦1), q'_i0 = ∑_j (q i j ∘ σ)·quot_j  (continuous), because when the
residual entries are center coordinates, (F i∘g∘σ) = w_p·(b∘σ)·(∑_j (q i j∘σ)·quot_j) = b'·q'_i0.
This route NEVER uses the left row-operation / Q̂.

THE CERTIFICATE (thread 34) instead says the honest construction uses a LEFT row-operation Q₁ (det-0
as a source map, so NOT absorbable into σ), reincorporated as the conjugated cofactor
  Q̂ = diag(b')·Q₁⁻¹·diag(b')⁻¹    (unipotent, ContinuousOn, = I at 0, off-diagonal entries may vanish),
which "regenerates the row quotients": q' = (φ*U)·Q̂·h·(φ*V).

MY WORRY / WHY I'M CONSULTING: my simple route collapses resid'→(Fin 1, const 1), which makes the
child look TERMINAL and discards the residual structure the NEXT recursion step needs (a "lazy
witness" — the reviewers flagged exactly this as relocating the monument out of this leaf). The
honest child must keep resid' as the NEXT center-coordinate block, and THAT is where Q̂ enters (the
row-mixing that a pure per-entry pullback cannot produce).
</task>

<questions>
1. Is my worry correct — i.e. for the child StepInv to carry a NON-trivial residual that the next
   step can consume (rather than a collapsed Fin-1 residual), is the Q̂ conjugation genuinely
   required, or can a per-entry pullback of resid (resid'_j = resid_j∘σ, suitably re-divided) also
   keep the residual structure? Give the sharp reason.
2. What is the cleanest ABSTRACT Lean/Mathlib statement of the Q̂ machinery that AVOIDS the diagonal
   inverse `diag(b')⁻¹` (since b'(0)=0, so entries vanish — `x⁻¹` junk at 0 is a trap)? My instinct:
   define Q̂ ENTRYWISE from an explicit continuous ratio `c a b` (a divisibility witness
   b'_a = c a b · b'_b for a≥b in the chain) as  Q̂_ab = c a b · (Q₁⁻¹)_ab , and prove the
   CONJUGATION RELATION  diag(b') * Q₁⁻¹ = Q̂ * diag(b')  directly (no inverse), plus:
   Q̂ unipotent, Q̂ ContinuousOn, Q̂(0) = I. Is this the right decomposition? What hypotheses on Q₁
   (lower-triangular? just "unit lower-triangular"? `Q₁ 0 = I`?) and on the ratio are minimal and
   honest? Any Mathlib pitfalls at v4.29 (Matrix.mul, diagonal, BlockTriangular, det, unit-triangular)?
3. Is there a decomposition that lets the leaf consume the exact-division atom + a SMALL Q̂ fact,
   rather than a big matrix module? Rank the sub-lemmas by how load-bearing each is for a
   divisibility-only (NOT Bézout) child StepInv.
</questions>

<output_contract>
Three sections, one per question. Be concrete about Lean statements (give the theorem signatures you
would write). Flag any place my instinct is wrong. Keep it under ~700 words; prioritise the sharp
reasons over exhaustive detail. Mark clearly what is your inference vs. a definite Mathlib fact.
</output_contract>
