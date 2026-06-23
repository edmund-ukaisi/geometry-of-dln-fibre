<task>
Lean 4 / Mathlib v4.29 formalisation. I must prove sub-lemma (3) "MP-of-transvection": the general
det-1 Schur straightening of a block matrix is MEASURE-PRESERVING. Choose the cheapest route. This is
reusable bedrock; I want the route with the least Fin-indexing / det-lift friction.

THE MAP. From the (already GREEN) block identity `hardPivot_schur_blockId`:
  L = fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ) 0 (-c) 1      -- unipotent, clears col-0 block
  R = fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ) (-b) 0 1      -- unipotent, clears row-0 block
  L · (fromBlocks 1 b c D) · R = fromBlocks 1 0 0 (D - c·b)
with b : Matrix (Fin m)(Fin n) ℝ, c : Matrix (Fin l)(Fin m) ℝ, D : Matrix (Fin l)(Fin n) ℝ.
I need: the straightening map on the PARAMETER space — i.e. `A ↦ L · A · R` viewed as a map on the
matrix entries `Matrix (Fin (m+l)) (Fin (m+n)) ℝ` (or its flattening to `Fin _ → ℝ`) — is
`MeasurePreserving` for Lebesgue `volume`. (L, R are FIXED data; the variable is A. Both det 1.)

DOWNSTREAM CONSUMER. A separate lemma `schur_straighten_of_data` already takes a chart
`χ : (Fin nReg → ℝ) × (Fin N' → ℝ) ≃ₜ (Fin N → ℝ)` with `MeasurePreserving χ` as a HYPOTHESIS. (3) is
the lemma that will (later, in a held lane) supply such a χ. So (3) should be stated reusably on the
matrix/vector space, decoupled from the chain flattening.

MATHLIB PIECES I FOUND (verify names if you cite more):
- `volume_preserving_transvectionStruct (t : TransvectionStruct ι ℝ) : MeasurePreserving (toLin' t.toMatrix)` — Lebesgue/Basic.lean:389. NOTE: this is the action `x ↦ M·x` on `ι → ℝ` (mulVec), NOT `A ↦ L·A·R` on a matrix space.
- `map_matrix_volume_pi_eq_smul_volume_pi {M : Matrix ι ι ℝ} (hM : det M ≠ 0) : Measure.map (toLin' M) volume = ofReal |det M|⁻¹ • volume` — Basic.lean:411. det-1 ⟹ MeasurePreserving, but again the `x ↦ M·x` action.
- `Matrix.det_kronecker` — Kronecker.lean:383.
- `measurePreserving_piCongrLeft`, `MeasurableEquiv.piCongrLeft`, reindexing equivs (measure-preserving).
- A PROVEN GREEN PRECEDENT in-repo: `measurePreserving_shearAt {n} (i : Fin (n+1)) (g) (hg : Measurable g) : MeasurePreserving (fun x => Function.update x i (x i + g (x ∘ i.succAbove)))` on `Fin (n+1) → ℝ` — single-coordinate shear, FULLY GENERAL, via piFinSuccAbove + skew_product + add_right. The (2,2,2) case `measurePreserving_lemma2` composes 3 of these + a perm on `Fin 7` (hardcoded coords, fin_cases+ring).

THE THREE CANDIDATE ROUTES:
- ROUTE A (shears): write `A ↦ L·A·R` on the flattened `Fin (rows·cols) → ℝ` as a COMPOSITION of
  `measurePreserving_shearAt` — one shear per entry of c (row-clears) and per entry of b (col-clears).
  PRO: green precedent, no det computation. CON: the Fin-indexing — flatten Matrix↔Fin, index the ~(l·m + m·n) shears, composition-order bookkeeping; the precedent hardcodes Fin 7.
- ROUTE B1 (Kronecker det): `A ↦ L·A·R` is `toLin'` of the big matrix `(Rᵀ ⊗ L)` (vectorize A). Its det
  is `det(L)^{cols}·det(R)^{rows} = 1`. Then `map_matrix_volume_pi_eq_smul_volume_pi` with det=1.
  PRO: no per-entry bookkeeping. CON: must (i) identify the vectorization Matrix-space ≃ (Fin _→ℝ) as a
  measure-preserving equiv, (ii) prove `A↦L·A·R = toLin' (Rᵀ⊗L) ∘ vec` (the vec identity), (iii) the
  Kronecker det = 1 lift.
- ROUTE B2 (vectorize + transvection generators): same vectorization, but instead of Kronecker, note
  `L·A·R` decomposes A↦L·A then ·R, each a product of `TransvectionStruct` generators acting on vec(A),
  use `volume_preserving_transvectionStruct` directly. CON: expressing left/right matrix mult as a
  composite of `toLin'` of transvections on the vectorized space.

WHAT I'VE TRIED: nothing in Lean yet (scoping). The (2,2,2) shear precedent IS green.
</task>

<output_contract>
  1. RANK the three routes by total expected Lean friction (1 = cheapest). One line each justifying.
  2. For the WINNER: the concrete lemma chain (named Mathlib lemmas + the in-repo precedent), in order,
     to get from the map to `MeasurePreserving`. Flag each Mathlib name as "verify" if you're not sure
     it exists in v4.29.
  3. The single biggest RISK in the winning route + the cheapest way to de-risk it (e.g. a concrete
     small-size instance first — which size?).
  4. Should (3) be stated on `Matrix (Fin R)(Fin C) ℝ` directly, or on the flattened `Fin (R*C) → ℝ`,
     for cleanest reuse by the χ consumer? One line.
  Under ~450 words. Mark inference vs. fact; do not invent lemma names.
</output_contract>

<grounding_rules>
  Lean type theory + the Mathlib lemmas I listed (with their stated signatures) are fact. Any ADDITIONAL
  Mathlib lemma you cite must be marked "verify — may not exist in v4.29". Distinguish "this definitely
  works" from "this likely works but needs a glue lemma".
</grounding_rules>
