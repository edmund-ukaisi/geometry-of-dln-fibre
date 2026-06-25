# Decorrelated design review — R2-3 trivialization AlgEquiv (Lean 4 / Mathlib v4.29)

## Context (the math, certified true)
We formalise Lehalleur-Rimányi Lemma 4.6 (fibre codimension of deep-linear-network multiplication).
For a dimension vector d = (d_0,...,d_N), `Rep_d = ∏_i Mat(d_i, d_{i-1})`, `mult(A) = A_N ⋯ A_1`.
Fix a rank `r` and a pivot chart (the top-left r×r minor `ΔP` of the product is invertible).

CERTIFIED (pen-and-paper, Singular over ℚ, 11 cases + decorrelated Codex): the fibre ideal
`I_E = (mult(Ã) − E)` is RADICAL; `F_E = k[Ã]/I_E` is REDUCED, for every N≥1, every d, every target
(depends only on rank E). The fibre is reducible + non-equidimensional in general but always reduced.

## The route (b), already chosen
We want, on the pivot chart, the trivialization AlgEquiv
    S ≅ₐ[R] R ⊗_k F_E
where:
- R = SchurLoc = Localization.Away(detSchurS) — the regular base ring of dim δ (ALREADY BUILT for the
  single-matrix base via G2-2: `basePresentationEquiv : A_loc/Iad ≅ₐ[k] SchurLoc`).
- S = O(Σ̄^r ∩ chart), carried in the engine ONLY as the reduced
  `Sred = (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)[1/ΔP]`, where
  `sigmaIdeal = vanishingIdeal(Σ̄^r)` (radical, REDUCIBLE on the deep chain, NOT prime).
- F_E = k[Ã]/(mult(Ã)−E), E the rank-r normal form.
The endpoint normalization: write target B = L·E·H (L,H unipotent), set Ã_1 = A_1 H⁻¹, Ã_N = L⁻¹A_N,
middles unchanged ⟹ mult(A)=B ⟺ mult(Ã)=E ⟹ the product trivialization.

Then route (b) reducedness: Sred reduced (engine `vanishingIdeal_isRadical`) → via the AlgEquiv,
R ⊗_k F_E reduced → (k→R faithfully flat, char 0) F_E reduced → I_E radical.
I have ALREADY PINNED the descent lemma in Lean (compiles):
    isReduced_of_injective includeRight (includeRight_injective (algebraMap k R).injective)
needs only [Nontrivial R]. So the descent is solved.

## What G2-2 gives me (single matrix N=1, `dStratum q p`)
- `blockAlgEquivLoc : A_loc ≃ₐ[k] MvPolynomial B22block SchurLoc` (localize the block-eliminate equiv).
- `basePresentationEquiv : A_loc/Iad ≅ₐ[k] SchurLoc`.
- These are all for a SINGLE matrix. The deep `mult` (product of N factors) is genuinely different —
  the total rank ideal FACTORS (reducible), so the B22-graph-elimination trick does NOT port.

## THE QUESTION (sharp, Lean-mechanical)
The recon estimated R2-3 at 7-10 modules of new scheme-free affine scaffolding (the wall). I want the
SMALLEST load-bearing Lean deliverable that genuinely carries the certified reducedness into the
downstream (height-additivity → codim = δ), without grinding the full deep endpoint-normalization
AlgEquiv if it's not strictly necessary.

1. Is there a SHORTER route to `F_E reduced` / the radical-collapse `fibreGenIdeal = vanishingIdeal(fibre)`
   that does NOT require constructing the full deep `S ≅ R ⊗_k F_E` AlgEquiv from scratch? E.g.:
   - directly proving `F_E` (= the cut algebra `MvPolynomial(Ã coords)/(mult(Ã)−E)`) reduced via a
     base-change / faithfully-flat argument against the ALREADY-reduced `Sred`, where the link is
     a localization/quotient map rather than a full product AlgEquiv?
   - Note: the actual downstream consumer is the radical-collapse of `MultComorphism` pt 4:
     `fibreGenIdeal d B = radical(fibreGenIdeal d B) = vanishingIdeal(fibre d B)`. If I can prove
     `(fibreGenIdeal d B).IsRadical` directly (the cut ideal is its own radical), that IS the deliverable
     and route (b) is just one proof strategy for it.

2. If the full AlgEquiv IS needed: what is the cleanest Lean construction of the endpoint-normalization
   automorphism of `Rep_d` over R, and the product iso `S ≅ R ⊗_k F_E`? Which Mathlib pieces
   (`IsLocalization.Away.mapₐ`, `Algebra.TensorProduct.*`, `AlgEquiv` composition) and which order?

3. Reachability honesty: given one formaliser tide, is the realistic deliverable (a) the full deep
   AlgEquiv + reducedness chain, or (b) a committed PARTIAL (the scaffold + the descent lemma landed,
   the deep product-iso left as the next rung)? What is the highest-value piece to bank first?

Please reason from the Lean-mechanical reality (Mathlib v4.29, IsLocalization/TensorProduct API), not
just the math. Flag any place where the "obvious" construction hits a dependent-type or
instance-resolution wall.
