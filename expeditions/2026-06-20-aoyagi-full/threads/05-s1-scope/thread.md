# Thread 05 — S1 scope: the RLCT invariance substrate (pp, read-only)

- **Seat:** `pp`. **Read-only + /tmp scratch** (`/tmp/s1_*.py`, `/tmp/codex-s1-*.md`); controller integrates.
- **Status:** scoped. One heavy core (S1.1) + four light corollaries. The shared analytic linchpin.

## The clean abstraction (ADOPT in the Lean — unifies S1, and matches the narrowed S2)

Weighted compact-fiber threshold:
`θ(G, ρ; K) := sSup { c≥0 : ∃ Ω open ⊇ K, IntegrableOn (|G|^(−c)·ρ) Ω volume }`.
Then `rlctAt F w* = θ(F, 1; {w*})`. All of S1 states in this one object; the Jacobian becomes the weight
`ρ` after a chart. Cleaner than the design-spec's atomic+cover split.

## S1.1 — THE LINCHPIN (weighted-threshold transport; the one heavy core)

`π : M → U` proper real-analytic; `w*∈U`, `K=π⁻¹{w*}`; null sets `E⊂M, Z⊂U` with `π : M∖E → U∖Z` an
analytic diffeo; `Jπ=|det Dπ|`. Then for nonneg measurable `φ`:
> `θ(F, φ; {w*}) = θ(F∘π, (φ∘π)·Jπ; K)`.
In particular `rlctAt F w* = θ(F∘π, Jπ; π⁻¹{w*})`; finite chart cover ⇒ `= min_i θ(F∘πᵢ, |det Dπᵢ|; Kᵢ)`.
Proof route: delete `E,Z` → Mathlib Jacobian change-of-variables on the diffeo part → restore null sets
(measure-zero) → properness ⇒ neighbourhood equivalence (every nbhd of `w*` pulls back to `π⁻¹(U₀)`).

**CRITICAL CORRECTION (Codex-caught, pp-verified):** do NOT state as *unweighted* `rlctAt(F∘π)=rlctAt(F)`
— that is **FALSE**. `F=x²+y²`, chart `(u,uv)`: unweighted threshold 1/2 ≠ original 1; the missing factor
is exactly `|det Dπ|=|u|` (`∫|u|^{1−2c} ⟹ c<1` ✓). **The Jacobian weight is mandatory.**

## S1.2 monotonicity (easy) · S1.3 ideal-invariance (moderate) · S1.4 corollaries (cheap)

- **S1.2:** `Σgⱼ² ≤ Σfᵢ²` near `w*` ⇒ `rlctAt G ≤ rlctAt F` (`t^{−c}` decreasing ⇒ integrability set ⊆).
- **S1.3:** `⟨Fᵢ⟩=⟨Gⱼ⟩` **as germs** (NOT just zero sets/radicals) ⇒ `rlctAt(ΣF²)=rlctAt(ΣG²)`
  (Cauchy–Schwarz bound both ways + S1.2 + scale-invariance `λ(cF)=λ(F)`).
- **S1.4(a)** Σ_X-elimination: `Σ_X≻0` ⇒ loss `=‖Lz‖²`, components of `Lz` and `z` generate the SAME ideal
  ⇒ S1.3. (positive-DEFINITE load-bearing.) **(b)** φ-independence: positive-bump sandwich.

## Mathlib gap (Codex verified vs live Jacobian docs)

Mathlib HAS (`Mathlib.MeasureTheory.Function.Jacobian`): `lintegral_image_eq_lintegral_abs_det_fderiv_mul`,
`integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`, image-measurability, Sard-like det=0⇒image-null
— all needing InjOn on a MEASURABLE set + differentiability there. **THE GAP:** a blow-up is injective
only OFF the exceptional null locus → need the **S1.1 wrapper** (delete null sets, apply Mathlib CoV on the
complement, restore null sets, then properness ⇒ fixed-set→local-neighbourhood integrability along
`π⁻¹{w*}`). This wrapper is the single heaviest analytic lemma in the tower below the R1 construction.

## Properness subtlety (amends thread-04/D1)

A SINGLE affine blow-up chart is NOT proper (preimage of the deepest point is a line). Properness is GLOBAL
(full resolution; exceptional fiber compact). Split: the per-chart INTEGRAL IDENTITY needs only
diffeo-off-null-set (lighter); the NEIGHBOURHOOD-TRANSPORT (RLCT-locality) needs PROPERNESS. ⇒ **D1 reuses
S1.1 (weighted-threshold transport), and its properness comes from the global blow-up of its own
submanifold `{v=0,wᵢ=0}`** — not a bare substitution. (Refines thread-04's "reuses S1's change-of-variables".)

## Ranking + verdict

`S1.1 >> S1.3 > S1.4(a) > S1.2 ≈ S1.4(b)`. S1.1 is THE one heavy core; the rest are corollaries. S1.1 is
the single interface D1/R1/S2-application all consume — as **weighted local-integrability transport along a
proper a.e.-analytic diffeo**, NOT bare-diffeo CoV and NOT unweighted RLCT invariance. D1 takes the
single-map form; R1 takes per-chart + min; S2-application takes the min + the cited bare-monomial threshold
(the narrowed S2 axiom). Exactly the right shape given S2 was narrowed.

## Controller note — skeleton-S1 refactor needed

The encoded skeleton's two S1 sorries (`rlct_unit_invariant`, `rlct_germ_local`) are a SUBSET of this
suite and do NOT include S1.1 (the weighted transport) — the very thing R1/D1 consume. When formalising
S1, add S1.1 (the `θ`-transport wrapper) as the core + restate the corollaries on top. Adopt the `θ(G,ρ;K)`
abstraction. (Let `rv`'s 0c audit reach the completeness gap independently.)
