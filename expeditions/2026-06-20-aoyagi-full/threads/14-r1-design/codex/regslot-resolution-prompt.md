<task>
Lean 4 / Mathlib (DLN RLCT). A coordinate-derivative obligation is over-stated; determine whether a
WEAKER obligation (already what the consumer needs) dodges a substantial layout restructure. This is the
RESOLUTION of a prior consult (which confirmed: an index Equiv can't express the X-SUM Σ_s X_s).

DECL-CONFIRMED FACTS (from the Lean source, this session):
- The "deepest point" gauge straightening is a self-map regStraighten : (R × C × S) → (R × C × S)
  (R=reg, C=core, S=spectator/gauge), fixing core+spectator, applying a pivot map deepestEPivot on R.
- PIN1's RLCT peel `rlctAtOn_comp_localDiffeo` (the consumer) has signature:
    (f : M → M) (e : M ≃L[ℝ] M) (hf : HasStrictFDerivAt f (e : M →L[ℝ] M) wstar) (hfix : f wstar = wstar)
    ⟹ rlctAtOn (F ∘ f) wstar = rlctAtOn F wstar.
  So PIN1 needs d(regStraighten)(0) to be SOME INVERTIBLE continuous-linear-equiv `e : M ≃L M` — NOT
  specifically the projection `fst`/`id`. (The `_deriv` obligation was WRITTEN as `= ContinuousLinearMap.fst`,
  which is STRONGER than the peel needs.)
- #91 (proven): the derivative d(P−B)|_0 of the gauge-normalized product residual has X-corner = Σ_s X_s
  (SUM over all L layers' X_s blocks), Y-corner = Y_{last}, Z-corner = Z_{first}.
- The reg slot (Fin nReg) carries ONE X-block (r²); the L−1 interior X_s live in the gauge slot. The
  per-layer X_s are read separately (readX p s reads layer-s X). So the X-summing Σ_s X_s mixes reg + gauge.
- PIN2 (separate, g161) needs deepestEPivot's VALUE ≈ E (loss residual) ≈ Σ_s X_s — that's a value
  constraint on deepestEPivot, NOT on the derivative being fst.

THE QUESTION (the resolution fork):
Given PIN1 needs only that d(regStraighten)(0) is an INVERTIBLE CLE (not fst), consider the candidate:
regStraighten's derivative is a SHEAR — reg-out = Σ_s X_s (the sum), gauge keeps the individual interior
X_s as separate coordinates (NOT consumed), core/spec/Y/Z fixed. Is this shear an INVERTIBLE linear map
on R×C×S? (Intuition: a "sum the first coordinate into reg, keep the rest" map. E.g. (a,b) ↦ (a+b, b)
is invertible (det 1, unitriangular); (a,b) ↦ (a+b, a+b) is NOT.)
If invertible: PIN1 closes with the WEAKER invertible-derivative obligation, NO substantial summing-section
restructure of the reg slot — just (i) weaken the _deriv obligation from `= fst` to `= e` for the explicit
shear CLE `e`, and (ii) PIN2 separately gets deepestEPivot's value ≈ Σ_s X_s. Bounded.
If NOT invertible (the summing collapses dimensions): then the reg/gauge split must be restructured so
reg = image(sum), gauge = ker(sum) — the (b-substantial) path.

<output_contract>
1. VERDICT (one line): is the "sum-into-reg, keep-individuals-in-gauge" shear an INVERTIBLE CLE? YES/NO + the crisp linear-algebra reason.
2. IF YES: the exact shear CLE shape (which unitriangular/permutation structure makes it invertible), and confirm PIN1 closes with the weakened `_deriv = e` (e the shear) WITHOUT a reg-slot restructure. State what PIN2 separately needs (value ≈ Σ_s X_s) and that it's independent of the derivative shape.
3. IF NO: why the summing collapses (which dimensions coincide), and that (b-substantial) reg=image/gauge=ker is forced.
4. The SINGLE cheapest decl-check to confirm the verdict (e.g. "does regStraighten keep the interior X_s as free gauge coordinates, or consume them into the reg sum?").
5. BLAST RADIUS: bounded (weaken _deriv obligation + explicit shear CLE, ≤~60 LoC, no reg-slot restructure) vs substantial (reg-slot image/ker restructure + consumer ripple).
</output_contract>

<grounding_rules>
Reason from the stated types/facts (you don't have full source). Flag inference vs fact. The load-bearing
question is purely linear-algebra (is the shear invertible) — answer that crisply; the Lean packaging
follows. Name any Mathlib lemma as "verify" if you cite one.
</grounding_rules>
