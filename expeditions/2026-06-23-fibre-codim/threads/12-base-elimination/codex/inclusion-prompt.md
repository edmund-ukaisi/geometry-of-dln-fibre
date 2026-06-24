<task>
Lean 4 + Mathlib v4.29. ONE step left in a determinantal-base elimination: the inclusion
J ⊆ Ψ(Iad) (the "Schur-content" step). I have everything else landed. I want the lowest-friction
Lean route to this inclusion, committing before I grind.

LANDED (sorry-free, DLNFibre.Core):
- A_eng := MvPolynomial (RepCoord (dStratum q p)) k. detΔ := detPivotPoly q p r hp hq : A_eng (the
  top-left r×r minor of the generic matrix). A_loc := Localization.Away detΔ.
- Iad := (sigmaIdeal (dStratum q p) r).map (algebraMap A_eng A_loc). PRIME, height Iad = C (landed).
- blockAlgEquiv : A_eng ≃ₐ[k] MvPolynomial B22block (MvPolynomial SchurVar k)
  (B22block = Fin(p-r)×Fin(q-r), SchurVar = (Fin r×Fin r)⊕(Fin r×Fin(q-r))⊕(Fin(p-r)×Fin r)).
  blockAlgEquiv_detPivot : blockAlgEquiv detΔ = C detSchurS  (detSchurS = det of the Δ-coord matrix
  in MvPolynomial SchurVar k; detSchurS_ne_zero landed). multPoly (dStratum q p) a b = X ⟨0,(a,b)⟩
  (landed multPoly_stratum_apply). repCoordReindex_pivot: pivot coord ↦ Sum.inr (Sum.inl (i,j)).
- The localized Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd (Sd = Localization.Away detSchurS) via
  IsLocalization.algEquivOfAlgEquiv blockAlgEquiv (SPECIFY-confirmed typechecks).
- forcedNum : Matrix (Fin(p-r)) (Fin(q-r)) (MvPolynomial SchurVar k) := B21S * (ΔS).adjugate * B12S
  (ΔS i j = X (inl (i,j)), B12S i j = X (inr (inl (i,j))), B21S a i = X (inr (inr (a,i)))).
- forcedB22 ab : Sd := IsLocalization.mk' Sd (forcedNum ab.1 ab.2) ⟨detSchurS, _⟩.
- J := graphIdeal forcedB22 in MvPolynomial B22block Sd. height J = C (landed
  height_graphIdeal_forcedB22_eq). J prime (graphIdeal_isPrime, Sd domain).
- THE BORDERED SCHUR MINOR (landed, DeterminantalChartRing): det_fromBlocks_scalar_eq gives
  det[[Δ,u],[v,d]] = d·detΔ − (v·adjΔ·u) over any CommRing; and
  det_submatrix_multPoly_mem_sigmaIdeal : every (r+1)-minor of multPoly ∈ sigmaIdeal. So the Schur
  expression  B22_{ab}·detΔ − (B21·adjΔ·B12)_{ab}  is an (r+1)-minor (bordered: pivot rows/cols +
  row a+r, col b+r) and lies in sigmaIdeal, hence its image lies in Iad.

GOAL: J ⊆ Ψ(Iad)  (where Ψ(Iad) = Iad.map (Ψ : ... →+* ...)). Equivalently (likely easier): each
generator X_{ab} − C(forcedB22 ab) of J lies in Ψ(Iad); or Ψ.symm of each generator lies in Iad.

The KEY identity I expect: the bordered (r+1)-minor of multPoly at (pivot rows ∪ {row a+r}, pivot
cols ∪ {col b+r}) — call it minorPoly_{ab} ∈ A_eng — satisfies
  blockAlgEquiv (minorPoly_{ab}) = C detSchurS · X_{ab} − C (forcedNum_{ab})       (*)
(its B22 entry ↦ the B22 coord X_{ab}; detΔ ↦ C detSchurS; the B21·adjΔ·B12 entry ↦ C forcedNum_{ab},
all SchurVar-only). And minorPoly_{ab} ∈ sigmaIdeal (landed) ⟹ its A_loc-image ∈ Iad ⟹ Ψ of that ∈
Ψ(Iad). Then C detSchurS is a unit in Sd (detSchurS inverted), so dividing (*) by C detSchurS:
  X_{ab} − C(forcedB22 ab) ∈ Ψ(Iad).

THE QUESTIONS:
1. Is the right route "show generator ∈ Ψ(Iad)" or "show Ψ.symm generator ∈ Iad"? Which is lower
   friction given Ψ = algEquivOfAlgEquiv (a localization-of-AlgEquiv)?
2. The identity (*): is proving blockAlgEquiv(minorPoly) = C detSchurS · X_{ab} − C forcedNum_{ab}
   the right spine? It's the bordered analogue of my blockAlgEquiv_detPivot / renameEquiv_detPivot
   (det commutes with the algebra maps; entries map to coord/SchurVar vars). Or is there a way to
   AVOID computing (*) entrywise — e.g. apply det_fromBlocks_scalar_eq directly in
   MvPolynomial B22block Sd to forced/coordinate matrices? Which is cleaner?
3. The "divide by the unit C detSchurS" step: cleanest Lean? `C detSchurS` (= algebraMap of detSchurS,
   a unit in Sd) — multiply the cleared generator by IsLocalization.Away.invSelf or
   (IsLocalization.map_units)... and the membership `unit * x ∈ Iad' ⟹ x ∈ Iad'` is `Ideal.unit_mul_mem_iff_mem` or `Ideal.mul_unit_mem_iff_mem`. Which exact lemma at v4.29?
4. Once J ⊆ Ψ(Iad): Iad = Ψ.symm '' J ... the squeeze. `Ψ(Iad) = J` from le_antisymm (J ⊆ Ψ(Iad) +
   height_strict_mono_of_is_prime ruling out J ⊊ Ψ(Iad)), then A_loc/Iad ≅ (MvPoly B22block Sd)/J ≅ Sd.
   The cleanest way to (a) get height (Ψ(Iad)) = height Iad = C [height_map_algEquiv], (b) the
   quotient iso A_loc/Iad ≅ (MvPoly B22block Sd)/(Ψ Iad) [Ideal.quotientEquivAlgOfEq / quotient of
   AlgEquiv], composed with graphIdealQuotientEquiv. Exact lemma names.

Constraint: do NOT route through ringKrullDim Sd = δ (localization can drop dim; unnecessary).
</task>

<output_contract>
1. Route for Q1 (forward vs symm) — pick one, 1 sentence why.
2. Q2: is (*) the spine, or is there an entrywise-free shortcut (apply det_fromBlocks_scalar_eq in the
   target ring)? Recommend the lower-friction one; if (*), the proof spine (which landed lemmas).
3. Q3: exact v4.29 lemma for "unit multiple ∈ ideal ⟹ elt ∈ ideal" + how to express C detSchurS as a unit.
4. Q4: the exact chain (height transport + quotient iso composition) with v4.29 lemma names.
Flag each lemma (confident-v4.29)/(unsure). Lemma names over prose.
</output_contract>

<grounding_rules>
Flag every Mathlib lemma name (confident-exists-v4.29)/(unsure—verify); don't invent names. Distinguish
"exists" from "applies". The localization-of-AlgEquiv (algEquivOfAlgEquiv) + ideal map/quotient interplay
is the likely friction — be concrete.
</grounding_rules>
