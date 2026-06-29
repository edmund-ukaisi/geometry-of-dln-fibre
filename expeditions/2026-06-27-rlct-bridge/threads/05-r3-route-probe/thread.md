# Thread 05 — Wave 1b: deepest-stratum mildness + the resolved-chart Newton finding

**Seat:** `pen-and-paper` (adjudication; **no Lean**). **Date:** 2026-06-28.
**Scope (narrowed by controller 2026-06-28):** the L&R / rlct-bridge line stays BLIND to the parallel
Aoyagi formalisation — the analytic lower bound `rlct ≥ ½·codim` is a **CITED** result on our side, not
re-formalised. So this thread banks only **decorrelated L&R-side confidence in that citation**: the
independent mildness verdict + the Newton-degeneracy finding. (The resolution-datum spec / cost
estimate for an R3 tide is OUT of scope and removed.)
**Method:** exact algebra — sympy symbolic peels, an exact Newton-polytope LP (calibrated against
`x²`→½, `x²+y²`→1, codim-3 CI→3/2, `lct⟨x,y,z⟩`=3), exact polar integrals, and exact
torus-critical-point (Kushnirenko–Varchenko) degeneracy witnesses; one decorrelated
`local-codex-consult` at `xhigh` (frame-in / facts-in / **hypothesis-out**). Builds on R1
(`threads/02-deepest-stratum-rlct`).
Artefacts: `codex/newton-resolved-{prompt,answer}.md`; scratch `/tmp/rprobe_*.py`.

---

## VERDICT — MILD (the cited Aoyagi equality is sound at this witness)

> **`(2,2,2,2,2)` r=0 deepest stratum: local rlct `= 3/2 = ½·codim`.** Independent of R1's two routes,
> via an exact reduction of the resolved local model to a monomial sum-of-squares with an exact polar
> integral. The cited `rlct = ½·codim` equality holds at the `|δ|=2` witness where the three
> θ-invariants diverge. No evidence of anything `< 3/2`.

This is decorrelated L&R-side corroboration of the citation (`RlctInterface.cited_aoyagi_dln`), not a
re-proof of the analytic lower bound.

### The independent reduction (exact)

Starting in the layer-1 incidence chart `A₁ = α[[1,a],[b, ab+δ]]` with a free next factor, the
composite's entry ideal reduces (unit elimination — two entries form an invertible diffeo in two of
the variables, a genuine Morse pair `w₁, w₂`; `/tmp/rprobe_ideal_reduce.py`,
`/tmp/rprobe_local_model.py`) to the clean deepest-stratum local model

    F  ~  w₁² + w₂² + δ²(s² + v²)        ( = w₁² + w₂² + (δs)² + (δv)² ).

Exact rlct two ways (`/tmp/rprobe_localrlct.py`): the Newton-polytope LP and an exact polar integral
`∫ δ^{−2z} dδ · ∫ R^{1−2z} dR` (with `s²+v²=R²`) both give `½ + ½ + ½ = 3/2`. The `δ`-axis binds at
threshold ½; the radial directions are non-binding (threshold 2). This matches R1's `λ ≤ 3/2` exact
upper bound, R1's two-route `3/2`, and the banked `Aoyagi.lambda(2,2,2,2,2) = 3/2 = C/2`.

Cross-check on R1/Codex's resolved ideal `J = ⟨zr−cp, a(c−zq), dr, adq⟩`: the Newton-LP on its
monomial support gives `lct = 3` (weight `(c,d,z)=(1,1,1)`; `/tmp/rprobe_J.py`), half for
sum-of-squares → `3/2`. Consistent.

## The Newton-degeneracy finding (exact — why the naive route fails, and why the citation is non-trivial)

The reason the rlct is genuinely a cited (not a one-line) result: the loss is **Newton-degenerate**,
so no single Kushnirenko/Saito–Varchenko theorem in the original coordinates computes it.

- **Original loss `K`, standard coords: DEGENERATE** (R1; reconfirmed). The homogeneous Newton face is
  `K` itself and vanishes on the real torus (explicit all-nonzero point with `A₄A₃A₂A₁ = 0`), so the
  naive toric bound `2 ≠ 3/2`.
- **The deepest-stratum reduced model `w₁²+w₂²+δ²(s²+v²)`: NONDEGENERATE.** It is a monomial
  sum-of-squares — every compact Newton face is a positive sum of monomial squares, never zero on
  `(ℝ*)ⁿ`, so no torus critical point. The Newton-LP value `3/2` is then exact. The degeneracy of `K`
  is removed only *after* the rank/SVD + Morse reduction (a coordinate change), not in the entries.
- **Across strata it is not uniform.** For the higher-width corank-≥2 residual `‖Δ·S‖²` (e.g. the
  `(2,2,4)` core), even the resolved *radial* chart leading form stays degenerate — an exact all-nonzero
  torus zero survives after `Δ = a[[1,u],[v,w]]` (`/tmp/rprobe_unsheared.py`); only a nonlinear shear
  `e = w−vu` removes it. So the standard-coordinate / single-radial-chart Newton picture is genuinely
  insufficient in general — consistent with why the equality is cited from Aoyagi rather than read off
  a Newton polyhedron. (This degeneracy structure is observed data; the lower bound itself stays
  cited.)

## Decorrelated Codex (xhigh, conclusion withheld) — `codex/newton-resolved-answer.md`

Codex independently reproduced the same `w₁²+w₂²+δ²s²+δ²v²` model with the same Kushnirenko
nondegeneracy argument, and the same `(2,2,4)` torus-degeneracy witness, and independently added the
"radial chart alone is still degenerate; the nonlinear shear is necessary" refinement (which I then
verified exactly). It built both witnesses itself from the setup — independent search, not a stamp.

---

## Confidence

- **`(2,2,2,2,2)` r=0 local rlct `= 3/2 = ½·codim` (MILD):** **high** — exact reduction + exact polar
  integral + exact Newton-LP, agreeing with R1's two routes and the banked formula; no evidence of
  `< 3/2`. (The rigorous analytic lower bound `≥ 3/2` is the cited Aoyagi/Watanabe piece — by the
  narrowed scope, cited, not re-formalised.)
- **`K` Newton-degenerate (standard coords); reduced model nondegenerate:** **certain** (exact torus
  witness; monomial-sos faces).
- **Resolved radial chart still degenerate at corank-≥2:** **certain** (exact all-nonzero torus zero).
- **Most likely way the mildness reading is wrong:** a hidden deeper-corner stratum with local rlct
  `< 3/2` that the upper bound and the reduction miss — the standing R1 caveat. Current exact evidence
  (the reduction + both routes + the validated formula) points firmly to `= 3/2`.

*Levels kept separate: the value `½·minAdm`/`½·codim` is the geometric content (banked); the
`rlct = ½·codim` reading rides on the cited Aoyagi equality, unchanged here. This thread is
decorrelated confidence in that citation, nothing more.*
