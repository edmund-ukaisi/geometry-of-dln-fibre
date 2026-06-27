<task>
Lean 4 + Mathlib v4.29. I need the cleanest WORKING tactic to prove a `HasFDerivAt` for a multivariate
rational map's component, off a pole, and match it to a hand-written matrix-CLM. This is a sharp Lean
idiom question — I have the math, I need the right lemma sequence (Mathlib v4.29 has NO `HasFDerivAt.div`).

THE SETUP (a self-map `shear121 : (Fin 4 → ℝ) → (Fin 4 → ℝ)`):
  noncomputable def shear121 (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
    ![u 0, u 1, u 2 - (u 1 / u 0) * u 3, u 3]

  -- the intended fderiv, as the CLM of an explicit 4×4 matrix (transvection, det 1):
  noncomputable def shear121DerivMat (u : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0],
      ![(u 1 / (u 0)^2) * u 3, -(1 / u 0) * u 3, 1, -(u 1 / u 0)], ![0, 0, 0, 1]]
  noncomputable def shear121Deriv (u : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
    (Matrix.toLin' (shear121DerivMat u)).toContinuousLinearMap

GOAL:
  theorem shear121_hasFDerivAt {u : Fin 4 → ℝ} (hu : u 0 ≠ 0) :
      HasFDerivAt shear121 (shear121Deriv u) u

WHAT I HAVE:
- `hap : ∀ k : Fin 4, HasFDerivAt (fun y : Fin 4 → ℝ => y k) (ContinuousLinearMap.proj (R := ℝ) k) u`
  (`= fun k => hasFDerivAt_apply k u`).
- `hasFDerivAt_pi''` to split into components.
- `hasFDerivAt_inv' (hx : x ≠ 0) : HasFDerivAt Inv.inv (-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x` (the abstract
  inversion fderiv; there is NO `HasFDerivAt.div`).
- `HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x`.
- For the matrix CLM, `(shear121Deriv u) v = (shear121DerivMat u).mulVec v` and the component
  `(shear121Deriv u v) 2 = (u1/u0²·u3)·v0 + (-(1/u0)·u3)·v1 + v2 + (-(u1/u0))·v3`.

WHAT FAILED (across several passes):
1. `(hap 1).div (hap 0) hu` → ERROR: `HasFDerivAtFilter.div` does not exist (no `.div` in v4.29).
2. Assembling comp-2 as `(hap 2).sub (((hap 1).mul ((hasFDerivAt_inv' hu).comp u (hap 0))).mul (hap 3))`
   then `.congr_fderiv` with an `ext v; simp only [...CLM apply lemmas...]; field_simp; ring` to match
   `shear121Deriv`'s comp-2 → the `congr_fderiv` step gets "typeclass instance problem is stuck, often
   due to metavariables", and separately a `shear121Deriv_toLin` (matching the pi-CLM to the matrix
   mulVecLin via `fin_cases <;> simp <;> ring`) TIMED OUT at whnf (200000 heartbeats).
3. The `mulLeftRight`-shaped output of `hasFDerivAt_inv'` doesn't simplify to my explicit `smul`-of-proj
   form under `simp`/`field_simp` cleanly.

QUESTIONS:
1. What is the EXACT, minimal v4.29 tactic to prove `HasFDerivAt (fun y : Fin 4 → ℝ => y 1 / y 0)
   D u` for `u 0 ≠ 0`, where `D` is a clean explicit CLM? Specifically: is there a `HasFDerivAt.div`
   under a different name (e.g. `HasDerivAt` is 1-D; for `fderiv` of `f/g` is it `HasFDerivAt.div` gated
   behind an import I'm missing, or must I use `.mul` + `hasFDerivAt_inv'.comp`)? If the latter, give the
   exact term and the exact CLM `D` it produces (so I don't fight `congr_fderiv`).
2. For the `congr_fderiv` matching: what `simp`/`ext` lemma set reliably turns
   `(-mulLeftRight ℝ ℝ (u0)⁻¹ (u0)⁻¹).comp (proj 0)` (the inv-deriv composite) applied to `v` into a
   scalar `−(u0)⁻¹·(u0)⁻¹·(v 0)` so `field_simp`/`ring` closes? Name the `mulLeftRight` apply lemma.
3. ALTERNATIVE that avoids the whole CLM-matching: should I instead prove `DifferentiableAt ℝ shear121 u`
   off-pole via `fun_prop` (the @[fun_prop]-tagged `hasFDerivAt_inv'`/`differentiableAt_inv`), take
   `f' := fderiv ℝ shear121 u`, and then compute `|det (fderiv ℝ shear121 u)| = 1` WITHOUT a hand matrix
   — e.g. is there a Mathlib lemma giving `fderiv` of a `![...]`-valued map componentwise that I can feed
   to a det computation? Or is the hand-matrix + `congr_fderiv` genuinely the shortest path? Rank the two
   routes by v4.29 friction.
4. Is there a slicker route entirely: `shear121` off-pole is a `C¹` DIFFEOMORPHISM that is volume-
   preserving (a fiberwise z-translation, det 1). For my actual downstream need — the change-of-variables
   `∫⁻ phi''(S\N0) g = ∫⁻ (S\N0) 1·g(phi)` (leafH ≡ 0, so weight 1) — is there a Mathlib
   `MeasurePreserving`-based c-o-v that sidesteps `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
   (which needs the explicit `HasFDerivWithinAt`+`|det|`)? E.g. can I prove `MeasurePreserving shear121`
   on the off-pole set directly (transvection/shear preserves Lebesgue) and get the c-o-v from
   `MeasurePreserving.lintegral_comp` / `.setLIntegral_comp` instead?
</task>

<output_contract>
Answer Q1–Q4 in order. For Q1/Q2 give the EXACT Lean term/tactic (copy-pasteable, v4.29 names). For Q3
rank the two routes. For Q4 give a yes/no on whether a MeasurePreserving route sidesteps the fderiv, with
the precise Mathlib lemma name(s) if yes. End with "RECOMMEND:" — the single cheapest route to a sorry-free
`shear121_hasFDerivAt` (or to the c-o-v directly). Flag any lemma name you're not certain exists in v4.29.
</output_contract>

<grounding_rules>
Be precise about v4.29 Mathlib lemma names — if unsure a name exists, say "verify; may be named X". The
load-bearing uncertainty is Q1 (the quotient fderiv idiom without `.div`) and Q4 (whether MeasurePreserving
sidesteps it). Distinguish certain-Mathlib-fact from inference.
