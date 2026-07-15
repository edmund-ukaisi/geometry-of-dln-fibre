<task>
Lean 4 + Mathlib (v4.29) DESIGN question — LOCK the shape of the coverage/gluing tranche of a
stratified-resolution atlas BEFORE formalising. Argue whichever way; flag traps.

GOAL (Tide B, §3.2 coverage + §3.3 gluing). Deep linear net: `prod H A : Matrix (Fin (H 0)) (Fin (H
(last))) ℝ` = layer product, `A : Params H = ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H
s.succ)) ℝ` (a Pi of matrix spaces, carries volume/MeasureSpace by inferInstance). Target: from the
banked ATLAS-PARAMETERISED gluing
  `lintegral_lt_top_of_finite_cover {ι}[Fintype ι] (C : ι → Set α)(D : Set α)(f : α→ℝ≥0∞)
     (hcover : μ(D \ ⋃ i, C i)=0)(hfin : ∀ i, ∫⁻ x in C i, f < ⊤) : ∫⁻ x in D, f < ⊤`
produce, for the deep rank locus `D = {A | (prod H A).rank ≤ s}`, the finiteness `∫⁻_D f < ⊤` from
PER-CELL finiteness (`hfin`) supplied as a HYPOTHESIS (that hypothesis is a later tide's job — do NOT
prove it here). `f` is a GENERIC ℝ≥0∞ integrand (loss-independent).

BANKED SPINE (all sorry-free, ℝ):
- leaf: `rankEqLocus_eq_iUnion_pivot_inter (r) : {M | M.rank = r} = ⋃ (ρ:Fin r↪Fin m)(κ:Fin r↪Fin n), (pivotChart ρ κ ∩ {M | M.rank ≤ r})`, `pivotChart ρ κ = {M | IsUnit (M.submatrix ρ κ)}`. Non-vacuous (r=0 cell = {M=0}).
- general-pivot bridge: `generalPivot_reduce_rank (X)(M)(ρ κ : Fin M.rank↪·)(hU) : (X*M).rank = (X*M.submatrix id κ*(M.submatrix ρ κ)⁻¹).rank`.
- chain descent: `prodAux_reduce_rank (H)(A)(k q)(hk)(Q)(ρ κ : Fin (effLayer·Q).rank↪·)(hU) : (prodAux (k+1)·Q).rank = (prodAux k · (effLayer·Q).submatrix id κ * ((effLayer·Q).submatrix ρ κ)⁻¹).rank`. (`prod = prodAux L`; effective state = right factor Q; descends (k+1,q)→(k, (effLayer·Q).rank).)
- `pivotLocus_eq_iUnion`, `exists_nonsingular_submatrix_of_le_rank`, `exists_square_minor` (rank=k ⟹ ∃ nonzero k-minor).
- gluing `lintegral_lt_top_of_finite_cover` / `_finset_cover` (Fintype / Finset indexed).

CONTROLLER'S GUARDS (bake in): (i) ∫ stays generic-f, loss-independent; (ii) per-cell finiteness is a
TIDE-D HYPOTHESIS, never proved here; (iii) coverage is the NON-VACUOUS exact-rank form (leaf+descent),
NEVER the vacuous {rank≤s} set-inclusion (the rank-0 empty-minor chart = univ makes bare ⊆ trivial);
(iv) measurability of the rank-stratified cells must be GENUINE (cite the standard fact — determinantal
/ {det≠0} loci are measurable/open under the continuous entry maps — not hand-waved).

KEY TENSION I need resolved: for the GLUING consumer, `hcover : μ(D \ ⋃ C)=0` — if the cells `⋃ C`
cover D as a SET (D ⊆ ⋃ C) then hcover is trivial (μ ∅). But making the cells EXHAUST D set-wise is the
vacuous move (rank-0 chart=univ). So which is it: is the gluing's hcover meant to be the trivial "cells
cover a neighbourhood of D" (content deferred to hfin), OR does the non-vacuity have to live in the
cell DEFINITIONS (exact-rank {E=0} slices) with the coverage still a genuine ⊆? Resolve precisely.
</task>

<output_contract>
1. INDEX SHAPE. Nested per-level unions vs a single flat `Σ`-type CR-tree `Fintype` index for feeding
   `lintegral_lt_top_of_finite_cover`. Pick ONE, justify by Lean-reachability, give the concrete index
   type (or the nested-recursion statement) + how `hfin`/`hcover` thread. If nested: does the recursion
   bottom out cleanly (chain length induction) and does each level's gluing compose?
2. THE hcover RESOLUTION. Precisely: what is `D`, what are the cells `C i`, and what makes `hcover`
   BOTH provable AND non-vacuous-in-the-right-place. If the honest structure is "coverage is a genuine
   set fact + non-vacuity is in the cells + the CONTENT is hfin (tide D)", say so and give the exact
   `D`, `C i`, and the coverage lemma signature. Flag if the whole §3.3 is legitimately a thin wiring
   whose only new content is the finite cell family + measurability (with hfin+the geometry deferred).
3. MEASURABILITY. The exact Mathlib fact(s) making `pivotChart ρ κ = {A | IsUnit ((effective layer of A).submatrix ρ κ)}`
   (pulled back to `Params H`) a MeasurableSet — name them (continuity of det/entries + `IsOpen`/
   `measurableSet_lt`/preimage), VERIFIED-name or ABSENT. Is `MeasurableSet` even needed, or does
   `lintegral_lt_top_of_finite_cover` only need `hcover`/`hfin` (no per-cell measurability)? Check the
   banked lemma's actual hypotheses.
3. CHEAPEST GENUINE FIRST GREEN of this tranche + rough LoC band for the whole tranche.
4. TRAP CHECK: where would this accidentally (a) smuggle the loss into tide B, (b) collapse to the
   vacuous coverage, or (c) hand-wave measurability. One line each.
</output_contract>

<grounding_rules>
Flag inference vs fact; mark Mathlib lemma names VERIFIED / UNVERIFIED / ABSENT. Prefer the shape that
maximally reuses the banked spine + gluing lemma and keeps tide B loss-independent. Distinguish
"mathematically right" from "cheaply reachable in Lean now".
</grounding_rules>
