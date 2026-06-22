# Unit-weight (unit-Jacobian) rlctAtOn transport — LEMMA SHAPE for a114e07e's L2 half-(a) (pp-hall, 2026-06-22)

**Context.** The L2 deepest-point split chart χ is UNIT-Jacobian (det = a unit, e.g. `(w0+1)²(w4+1)`,
NOT ±1; #125 chart-interface section). So `rlctAtOn_comp_homeomorph` (S1Fubini.lean:54, REQUIRES
`MeasurePreserving`) does NOT apply. a114e07e needs the unit-weight transport lemma below instead.

## The lemma to state (a114e07e)
A `rlctAtOn` is invariant under an analytic diffeomorphism whose Jacobian is a UNIT (bounded above and
below by positive constants) near `w0`. Statement shape (on the general `[MeasureSpace][TopologicalSpace]
[BorelSpace]/[OpensMeasurableSpace]` domain — the same typeclass home as `rlctAtOn_unit_invariant_aux`):

    theorem rlctAtOn_comp_unitJac
        {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
        [MeasurableSpace E] [BorelSpace E]
        (χ : E → E) (χ' : E → (E →L[ℝ] E))             -- the chart + its fderiv
        (F : E → ℝ) (w0 : E)
        (hdiff  : ∃ U ∈ 𝓝 w0, ∀ x ∈ U, HasFDerivWithinAt χ (χ' x) U x)  -- χ C¹ near w0
        (hinj   : ∃ U ∈ 𝓝 w0, InjOn χ U)                               -- locally injective
        (hopen  : ∃ U ∈ 𝓝 w0, IsOpen (χ '' U))                         -- local diffeo image (or: χ open map)
        (hjac   : ∃ (U ∈ 𝓝 w0) (a b : ℝ), 0 < a ∧
                    ∀ x ∈ U, a ≤ |(χ' x).det| ∧ |(χ' x).det| ≤ b)       -- |det χ'| a UNIT near w0
        (hFmeas : Measurable F) :
        rlctAtOn (fun x => F (χ x)) w0 = rlctAtOn F (χ w0)

The hypotheses are exactly what the deepest-point χ supplies: χ is polynomial (so C¹ + analytic), locally
injective (it's a diffeo), and `|det χ'|` is a unit near `0` (the `(1+w0)`-type denominators are units).

## The proof skeleton (which banked atoms compose, in what order)
The RLCT is `weightedThreshold F 1 {w0}` = the `sSup` of admissible exponents `c'` (`|F|^{−c'}`
integrable on a nbhd). Transport the admissibility down-set across χ; the unit Jacobian doesn't move the
`sSup`. Three steps, each a banked atom or a Mathlib c-o-v:

**Step 1 — single change-of-variables (the integrand transport).** For each `c'`, the admissibility of
`F` at `χ w0` (`|F|^{−c'}` integrable on a nbhd of `χ w0`) transports to the admissibility of
`|det χ'|·(|F|^{−c'} ∘ χ) = |det χ'|·|F∘χ|^{−c'}` on a nbhd of `w0`, via
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` (Mathlib, the engine inside `perChart`,
`S1G5.lean:44`): `∫_{χ''V} g = ∫_{V∖N} |det χ'|·g(χ)`. Apply with `g = |F|^{−c'}` (as `ℝ≥0∞`, so NO
integrability side-conditions — the threshold integrand is `∞` above the rlct; ℝ≥0∞ handles it
unconditionally, exactly as G5 uses it). The `InjOn`-off-null adapter is `perChart`'s `N`-handling
(here `N = ∅` or the diffeo's exceptional, null). This is a SINGLE-chart `perChart` (no cover — one χ
covering a nbhd of `w0`), so no `g5_flat_cover` machinery, just the one c-o-v.

**Step 2 — strip the unit Jacobian (the weight).** The transported integrand carries the weight
`|det χ'|`, a UNIT bounded in `[a,b]`, `0<a`, near `w0`. Strip it by **`rlctAtOn_unit_invariant_aux`**
(`S1Local.lean:139`, GREEN): `rlctAtOn (fun x => u x · F x) w* = rlctAtOn F w*` for `u` measurable,
`a ≤ |u| ≤ b` on a nbhd. Here `u = |det χ'|` (measurable: χ' continuous ⟹ `(χ' ·).det` continuous;
`hjac` gives the bound). This removes the Jacobian weight without shifting the threshold — the crux of
"unit-Jacobian, not MP, still transports."

**Step 3 — germ-locality (assemble the nbhds).** The three nbhds (from `hdiff`/`hinj`/`hjac`) intersect
to one nbhd on which all hypotheses hold; `rlct_germ_local_aux` (`S1Local.lean:97`, GREEN — `F=G` on a
nbhd ⟹ equal RLCT) glues the local rewrites. (Or fold the nbhd intersection directly into Steps 1–2 as
`rlctAtOn_unit_invariant_aux` already does with its `∃ U ∈ 𝓝` hypotheses — germ-locality is implicit in
the `weightedThreshold`'s `∃ Ω open ⊇ {w0}`.)

**Composition order:** (Step 1 c-o-v: `rlctAtOn(F∘χ) w0` ← `rlctAtOn(|det χ'|·F) (χ w0)` via the
admissibility-down-set transport) ∘ (Step 2 unit-strip: `rlctAtOn(|det χ'|·F) (χ w0) = rlctAtOn F
(χ w0)`). Net: `rlctAtOn(F∘χ) w0 = rlctAtOn F (χ w0)`.

## Then the L2 half-(a) split assembles as (for a114e07e)
1. χ = the deepest-point unit-pivot chart (#125: replace each regular generator's unit-pivot variable by
   the generator; explicit, polynomial, unit-Jacobian).
2. `rlctAtOn_comp_unitJac` (above) transports `rlctAtOn(dlnLoss B) deepest = rlctAtOn(F∘χ⁻¹) (χ deepest)`
   to the split-coordinate form `rlctAtOn(Σ E_i² + core) 0`.
3. S1.5 smooth-block additivity (`smoothBlockND_rlct` + the Fubini split, GREEN) splits
   `rlctAtOn(Σ_{i<nReg} E_i² + core)` = `nReg/2 + rlctAtOn(core)`.
4. core = the homogeneous Schur-complement core → R1 (downstream).
⟹ `rlctAtOn(dlnLoss B) deepest = nReg/2 + rlctAtOn(core)` = the L2 `product_reduction` split,
constant-rank-FREE.

## The generator-equivalence caveat (aim for the weaker RLCT target)
The split is a unit-GENERATOR equivalence (the residual replaced by the Schur core, unit denominators),
NOT literal Euclidean equality after a source-only c-o-v. `rlctAtOn_comp_unitJac` is the right target:
it equates the RLCTs, which is all `product_reduction` needs — do NOT aim for `F∘χ = Σ E_i² + core`
literally (that's the stronger Morse splitting; the unit-Jacobian transport sidesteps it).

Atoms (all green, verified present): `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (Mathlib, via
`perChart` `S1G5.lean:44`) + `rlctAtOn_unit_invariant_aux` (`S1Local.lean:139`) + `rlct_germ_local_aux`
(`S1Local.lean:97`) + `smoothBlockND_rlct` (`S1SmoothBlock.lean:164`). No new analytic infra; no
constant-rank; no `MeasurePreserving`.
