<task>
I am formalising in Lean 4 + Mathlib (v4.29) the "deep product trivialization" of the rank-≤r
locus chart for deep linear networks (multiplication map of N composable matrices). I need a sharp
reachability verdict on ONE construction and ITS descent, plus the cheapest route if reachable.

SETUP (all objects below are LANDED, sorry-free, in a Lean engine "Core"):

Fix a dimension vector d : Fin (N+1) → ℕ. Let q = d 0 (source), p = d (last) (target).
- `RepCoord d := Σ i : Fin N, Fin (d i.succ) × Fin (d i.castSucc)` — one coordinate per matrix
  entry across all N edges. `Rep_d ≅ (RepCoord d → k)`.
- `mult d A = A_N ⋯ A_1 : Matrix (Fin p) (Fin q) k`. Over the polynomial ring, the generic product
  entries are `multPoly d r c : MvPolynomial (RepCoord d) k` (entries of mult of the generic tuple).
- `ΔPdeep d r := det` of the top-left r×r submatrix of `Matrix.of (multPoly d)` (the pivot minor of
  the PRODUCT, a polynomial in ALL the tuple coordinates).
- `sigmaIdeal d r := vanishingIdeal (productRankLocusLE d r)` (rank ≤ r locus), radical & prime.
- `IadDeep d r := (sigmaIdeal d r).map (algebraMap _ (Localization.Away (ΔPdeep d r)))`.
- `Sred d r := Localization.Away (ΔPdeep d r) ⧸ IadDeep d r`  — the deep chart ring. PROVED reduced.
- `SchurLoc q p r := Localization.Away (detSchurS q p r)` — the base ring (entries of the r×r pivot
  block Δ, the off-blocks B12 (r×(q−r)), B21 ((p−r)×r), with detΔ inverted; the B22 (p−r)×(q−r)
  block ELIMINATED via the Schur relation B22 = B21 Δ⁻¹ B12). dim = δ = r(p+q−r).
- `FibreAlg d B := MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B` where
  `fibreGenIdeal d B := span { multPoly d r c − C (B r c) }` (the fibre mult⁻¹(B) coordinate ring).
  E = rank normal form diag(I_r, 0).
- LANDED `schurToSred : SchurLoc q p r →ₐ[k] Sred d r` (gives Sred its SchurLoc-algebra structure).
- LANDED `gaugeEquiv d P : MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R` for a gauge
  P : ∀ v, (Matrix (Fin (d v)) (Fin (d v)) R)ˣ (one invertible matrix per vertex), over an ARBITRARY
  CommRing R. With `gaugeEquiv_multPoly`: `gaugeEquiv d P (multPoly d r c) = (P_last · Matrix.of
  (multPoly d) · P_0⁻¹) r c`. This is on the UNQUOTIENTED, UNLOCALIZED ring.
- LANDED `MvPolynomial.algebraTensorAlgEquiv R A : A ⊗[R] MvPolynomial σ R ≃ₐ[A] MvPolynomial σ A`.

TARGET: build `e : Sred d r ≃ₐ[k] SchurLoc q p r ⊗[k] FibreAlg d E`. (dim check at (2,2,2),r=1:
Sred dim 7 = SchurLoc dim 3 + FibreAlg dim 4.) Then it discharges a LANDED conditional theorem
(`fibreGenIdeal_isRadical_of_trivialization`) → fibreGenIdeal d E radical unconditionally.

THE STRUCTURAL OBSTACLE I SEE. The N=1 case is solved by a *coordinate relabeling*: RepCoord
(dStratum q p) ≅ B22block ⊕ SchurVar (matrix entries split into eliminated B22 + free Schur data),
and the localized quotient kills B22, leaving SchurLoc (the fibre is a POINT for N=1). For deep
N≥1 the fibre is NOT a point. The Schur data of M = mult(A) are POLYNOMIAL FUNCTIONS of ALL tuple
coordinates (entries of a product of N matrices) — NOT a sub-block of coordinates. So the split
Sred ≅ SchurLoc ⊗ FibreAlg is NOT a relabeling of RepCoord; it genuinely uses the gauge to change
variables, and the gauge L,H themselves are built from the SchurLoc-fraction-field elements
M21·Δ⁻¹ and Δ⁻¹·M12 (so the gauge has SchurLoc coefficients, not k). And `gaugeEquiv` is on the
UNQUOTIENTED, UNLOCALIZED ring — descending it through `Localization.Away ΔPdeep ⧸ IadDeep` AND
exhibiting the SchurLoc ⊗ FibreAlg split is the hard half.

WHAT I'VE TRIED/CONSIDERED:
1. Descend gaugeEquiv to the localization: needs gaugeEquiv to preserve ΔPdeep up to a unit. But the
   gauge has SchurLoc coefficients (L,H involve Δ⁻¹), so gaugeEquiv would have to be over the ring
   AFTER localizing, not over k or over MvPolynomial. The landed gaugeEquiv is over a constant
   coefficient ring R, with P a CONSTANT (coefficient-ring) gauge — but the genuine L,H are NOT
   constants, they are non-constant rational functions of the base coordinates. This looks like a
   mismatch: the landed gaugeEquiv may be the WRONG tool for the genuine descent.
2. algebraTensorAlgEquiv gives SchurLoc ⊗ MvPolynomial(RepCoord d) k ≅ MvPolynomial(RepCoord d)
   SchurLoc — a base-change of the fibre polynomial ring. Could the split be: Sred ≅ MvPolynomial
   over SchurLoc of the "fibre directions" modulo the fibre relations over E? But identifying the
   "fibre directions" as a coordinate subset is exactly the obstacle in (1).
</task>

<output_contract>
Four sections, terse, no preamble:

1. REACHABILITY VERDICT (one of: REACHABLE-CHEAP / REACHABLE-HARD-BUT-BOUNDED / WALL). One paragraph
   justifying. Be brutally honest — if the genuine `e` for deep N requires scheme-theoretic
   machinery Mathlib v4.29 lacks (e.g. faithfully-flat descent of an iso through a
   localization-quotient, or a smooth-fibration trivialization), say WALL and name the missing piece
   precisely. The expedition's correct outcome if WALL is to close against `e` as the single named
   residual (everything else is banked) — so a WALL verdict is a legitimate, valuable answer, NOT a
   failure. Do not invent a route that doesn't survive contact with Lean.

2. THE GAUGE MISMATCH. Is my concern (1) correct — that the landed constant-coefficient `gaugeEquiv`
   (P a coefficient-ring unit) cannot carry the genuine non-constant L,H (rational in base coords)?
   If so, what is the RIGHT object: a gauge over SchurLoc (so P : ∀ v, (Matrix _ _ SchurLoc)ˣ acting
   on MvPolynomial (RepCoord d) SchurLoc), and does the split then become a clean base-change? Or is
   there a genuinely different decomposition M = LEH that keeps the gauge constant?

3. IF REACHABLE: the SHORTEST build order (≤ ~8 steps), naming the Mathlib lemmas/AlgEquivs at each
   step. Identify which step carries the real content vs which are plumbing. Flag any step that is a
   "≥ 2 module" sub-project.

4. THE SINGLE RISKIEST STEP and the cheapest way to de-risk it BEFORE grinding (an `example` block
   pinning an API, a dimension/non-vacuity check, etc.).
</output_contract>

<grounding_rules>
You may reason from standard commutative-algebra/algebraic-geometry facts and from Mathlib v4.29 API
you are confident exists, but FLAG any lemma name you are not sure exists in v4.29 as "VERIFY".
Distinguish "this is mathematically true" (I have a pen-and-paper certificate that the split holds
and fibreGenIdeal d E is radical — that is NOT in question) from "this is mechanically reachable in
Lean v4.29 with bounded effort" (the ONLY question). Do not reassure; if it's a wall, say so.
</grounding_rules>
