<task>
Lean 4 + Mathlib (v4.29). I need to prove a "bridge" lemma and want (1) a correctness check that
it is TRUE (or a counterexample), and (2) the cleanest proof strategy + the delicate Lean idioms.

Context: `D : ℕ`, coordinates `Fin D → ℝ`, region `V = Set.univ` (always, here). Definitions:

  IgnoresCoords (c : (Fin D → ℝ) → ℝ) (S : Finset (Fin D)) (V) : Prop :=
    ∀ w ∈ V, ∀ m ∈ S, ∀ t : ℝ, c (Function.update w m t) = c w
  -- (agreement form, on V=univ: `IgnoresCoords c S univ ↔ ∀ u v, (∀ s∉S, u s = v s) → c u = c v`,
  --  banked as `ignoresCoords_univ_iff_agree`.)

  Deg1SupportedOn (resid : Fin nR → (Fin D → ℝ) → ℝ) (S) (V) : Prop :=
    ∀ j, ∃ c : Fin D → (Fin D → ℝ) → ℝ,
      (∀ i, ContinuousOn (c i) V) ∧
      (∀ u ∈ V, resid j u = ∑ i ∈ S, c i u * u i) ∧
      (∀ i, IgnoresCoords (c i) S V)

  AffineOn (f : (Fin D → ℝ) → ℝ) (X : Finset (Fin D)) (V) : Prop :=
    ∃ (a : (Fin D → ℝ) → ℝ) (b : Fin D → (Fin D → ℝ) → ℝ),
      IgnoresCoords a X V ∧ (∀ x ∈ X, IgnoresCoords (b x) X V) ∧
      (∀ u ∈ V, f u = a u + ∑ x ∈ X, b x u * u x)
  -- NOTE: AffineOn gives NO continuity on a or b.

  PerLayerDeg1From (f) (fromLayer : ℕ) (V) : Prop := ∀ ℓ, fromLayer ≤ ℓ → AffineOn f (layerCoords d ℓ) V

  Deg1SupportedSlot (resid) (j) (S) (fromLayer) (V) : Prop :=
    (∃ c : Fin D → (Fin D → ℝ) → ℝ,
      (∀ i, ContinuousOn (c i) V) ∧ (∀ u ∈ V, resid j u = ∑ i ∈ S, c i u * u i))   -- "clause 1"
    ∧ PerLayerDeg1From d (resid j) fromLayer V                                       -- "clause 2"

  -- `blockCoords d ℓ ⊆ layerCoords d ℓ` (blockCoords is layerCoords capped on one axis by a width;
  --  both are `Finset (Fin D)` images of a `tupIdx` filter; the ⊆ is provable).

THE BRIDGE I WANT (V = univ throughout). Fix a layer `ℓ`, and set `S := blockCoords d ℓ`,
`fromLayer := ℓ`. Assume for every j:
    Deg1SupportedSlot (resid) j S ℓ univ      -- i.e. clause1 (support ⊆ S, continuous coeffs) AND
                                              --      clause2 (PerLayerDeg1From from ℓ)
Prove:
    Deg1SupportedOn (resid) S univ            -- continuous coefficients that ALSO IgnoresCoords S.

MY PROOF SKETCH (please validate or refute, and sharpen):
For each j, from clause2 at ℓ get AffineOn (resid j) (layerCoords d ℓ): resid j u = a u + ∑_{x∈L} b_x u·u_x
with a, b_x ignoring L := layerCoords d ℓ ⊇ S.
Step 1 (a ≡ 0): for any u let u₀ = u with all L-coords zeroed. Then resid j u₀ = a u₀ (clause2 sum
vanishes) and resid j u₀ = ∑_{i∈S} c₀_i u₀ · (u₀)_i = 0 (clause1; S ⊆ L so all S-coords are 0 in u₀).
So a u₀ = 0; a ignores L so a u = a u₀ = 0.
Step 2 (b_x ≡ 0 for x ∈ L\S): for any u and t, let u_x^t = u with all L-coords zeroed except x↦t.
clause2: resid j u_x^t = a(u_x^t) + b_x(u_x^t)·t = 0 + b_x(u)·t (a=0; b_x ignores L). clause1:
resid j u_x^t = ∑_{i∈S} c₀_i·(u_x^t)_i = 0 (x ∉ S so all S-coords are 0). So b_x(u)·t = 0 ∀t ⟹ b_x u = 0.
Step 3: hence resid j u = ∑_{x∈S} b_x u·u_x with b_x ignoring L ⊇ S (so IgnoresCoords b_x S).
Step 4 (continuity): AffineOn's b_x is NOT given continuous. Reconstruct continuous coefficients:
define c_i(u) := resid j (fun k => if k ∈ S then (if k = i then 1 else 0) else u k). Claim c_i = b_i,
so c_i ignores S and c_i is continuous (resid j is continuous by clause1 = ∑ c₀_i u_i, c₀_i continuous;
and the coordinate-setting map is continuous). And ∑_{i∈S} c_i u·u_i = ∑ b_i u·u_i = resid j u.

QUESTIONS:
Q1. Is the bridge TRUE? If not, give a concrete D, S, ℓ, resid counterexample.
Q2. Are Steps 1–2 (extracting a≡0 and off-block b≡0 from "affine identity holds for all values of the
    free L\S coords, with coefficients constant in those coords") correct? Any hidden gap — e.g. does
    "IgnoresCoords over L" really let me treat a, b_x as constants in the L\S coords while I vary them?
Q3. Step 4 continuity: is c_i = b_i actually forced, and is the indicator-construction the cleanest way
    to get CONTINUOUS IgnoresCoords coefficients, or is there a slicker route (e.g. prove resid j itself
    is continuous and IgnoresCoords-decompose directly)?
Q4. The cleanest Lean idioms for the point manipulations: extracting a≡0 / b_x≡0 by evaluating at
    Function.update / piecewise points, and the "b_x·t = 0 ∀t ⟹ b_x = 0" step. Any Mathlib pitfalls?
</task>

<output_contract>
Four sections Q1..Q4. Q1 first, with an explicit TRUE / FALSE(+counterexample) verdict. Keep each
answer tight and concrete. If any step is subtly wrong, say exactly where and give the fix. Prefer
naming the exact obstruction over restating my sketch.
</output_contract>

<grounding_rules>
Flag INFERENCE vs. a fact you are confident of. Do not invent Mathlib lemma names you are unsure exist
— if you cite a lemma, mark it "verify name". The proof strategy (diagnosis) is what I need; any Lean
code is illustrative and I will re-derive/build it locally.
</grounding_rules>
