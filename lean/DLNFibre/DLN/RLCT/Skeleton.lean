import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.Lambda
import DLNFibre.DLN.RLCT.Foundations.S1Transport
import DLNFibre.DLN.RLCT.Foundations.S1Local
import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import DLNFibre.DLN.RLCT.BGEngine
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.GetD

/-!
# `DLNFibre.DLN.RLCT.Skeleton` — the goal skeleton (the contract)

The single cited `axiom` (S2, the monomial-integral extraction), every named-`sorry` rung
statement (S1 / L1 / L2 / D1 / R1 / A1 / A2), and the headline `aoyagi_learning_coefficient`
(design-spec §8).

**Statements-first.** Each rung below is a named `sorry` with the statement it must eventually
prove; a `sorry` under a correct statement is a building block. The sorry-count trends down as
rungs close. The headline is *assembled* from the named pieces so its statement type-checks.

## The one citation (S2) — and where the line is drawn
Per controller standing decision 2 and the decorrelated Codex audit (`codex/s2-axiom-answer.md`),
the cited content is **only** the irreducible monomial-integral fact: the RLCT threshold and pole
order of a **weighted monomial integral** `∫ (∏ uⱼ^{hⱼ}) · (∏ uⱼ^{2kⱼ})^{−c} du`. Everything else
stays on our side:
- the **cover** and **change-of-variables** validity → S1;
- the **resolution charts** producing the `(k, h)` data → R1;
- the reduction of `rlctAt (dlnLoss)` to a min over charts of these monomial thresholds →
  a *derived theorem* (proven later from S1 + R1 + S2), **not** an axiom.

So the chart-level formula is a theorem, not a citation; the axiom is the bare monomial fact.
(Codex's recommendation #5 and the brief's standing decision 2 coincide here.)
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory ENNReal Topology

variable {L : ℕ}

/-! ## Monomial-model objects (the S2 substrate) -/

/-- The per-axis ratio `(hⱼ+1)/(2kⱼ)` in `ℝ≥0∞`; `kⱼ = 0` gives `⊤` (that axis never binds the
minimum — the function is a unit in that direction). Division is in `ℝ≥0∞` (in `ℝ`, `a/0 = 0`
would be wrong here). -/
noncomputable def axisRatio (h k : ℕ) : ℝ≥0∞ := ((h : ℝ≥0∞) + 1) / (2 * (k : ℝ≥0∞))

/-- **R1.2a (regular-sequence divisor ratio).** A binding divisor over a codim-`c` stratum has
`(k, h) = (1, c−1)` (k=1 from order-2 vanishing of a real sum-of-squares; `h=c−1` from the smooth
codim-`c` blow-up Jacobian), ratio `c/2`. The upper-bound seed (binding divisor on the minimizing
stratum realises `½·Mval(t)`). -/
theorem axisRatio_regularSeq (c : ℕ) (hc : 1 ≤ c) : axisRatio (c - 1) 1 = (c : ℝ≥0∞) / 2 := by
  unfold axisRatio
  rw [Nat.cast_one, mul_one]
  congr 1
  have : ((c - 1 : ℕ) : ℝ≥0∞) + 1 = ((c - 1 + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring
  rw [this, Nat.sub_add_cancel hc]

/-- **R1.2b (multiplicity control — the lower-bound inequality).** Any divisor with `m·k ≤ h+1` has
ratio `≥ m/2`. With `m = min_t Mval` and our core's regular-sequence `k=1, h=c−1` (so `m·k = m ≤ c =
h+1`), every divisor ratio is `≥ ½·min_t Mval` — the lower-bound mechanism (the regular sequence,
not codim, is why `rlct = ½·codim` here; `xᵏ`/`(x²+y²)²` show the bare codim bound is false). -/
theorem axisRatio_ge_of_mult (h k m : ℕ) (hk : 1 ≤ k) (hmult : m * k ≤ h + 1) :
    (m : ℝ≥0∞) / 2 ≤ axisRatio h k := by
  unfold axisRatio
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hstep : (m : ℝ≥0∞) / 2 = ((m : ℝ≥0∞) * k) / (2 * k) := by
    rw [mul_comm (2 : ℝ≥0∞) (k : ℝ≥0∞), ← ENNReal.mul_div_mul_right (m : ℝ≥0∞) 2 hk0 (by simp)]
    ring_nf
  rw [hstep]
  apply ENNReal.div_le_div_right
  calc (m : ℝ≥0∞) * k = ((m * k : ℕ) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((h + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast hmult
    _ = (h : ℝ≥0∞) + 1 := by push_cast; ring

/-- The weighted monomial integrand: density `∏ uⱼ^{hⱼ}` (the pulled-back Jacobian × bump) against
the monomial `∏ uⱼ^{2kⱼ}` (the resolved function) raised to `−c`. The object whose threshold S2
cites. -/
noncomputable def monomialIntegrand (d : ℕ) (k h : Fin d → ℕ) (c : ℝ) (u : Fin d → ℝ) : ℝ :=
  (∏ j, |u j| ^ (h j)) * (∏ j, |u j| ^ (2 * k j)) ^ (-c)

/-- The unit box `[0,1]^d` (a compact chart neighbourhood of the origin). -/
def unitBox (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)

/-- The RLCT threshold of the weighted monomial integral: `sSup` of the down-set of exponents
`c' ≥ 0` for which the integrand is integrable on the box. -/
noncomputable def monomialThreshold (d : ℕ) (k h : Fin d → ℕ) : ℝ≥0∞ :=
  sSup { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧
          IntegrableOn (monomialIntegrand d k h (c' : ℝ)) (unitBox d) volume }

/-- The combinatorial pole order of the weighted monomial integral: the number of axes attaining the
minimal ratio (the binding-factor multiplicity). -/
noncomputable def monomialOrder (d : ℕ) (k h : Fin d → ℕ) : ℕ :=
  (Finset.univ.filter
    (fun j : Fin d => axisRatio (h j) (k j) = ⨅ j' : Fin d, axisRatio (h j') (k j'))).card

/-- The *analytic* pole order of the weighted monomial integral (the multiplicity of the largest
pole of its zeta function). Opaque placeholder — like `rlctOrderAt`, the direct analytic definition
needs meromorphic continuation Mathlib lacks; its value is pinned by the S2 citation below. -/
opaque monomialOrderAnalytic (d : ℕ) (k h : Fin d → ℕ) : ℕ

/-! ## S2 — THE ONE CITED AXIOM (Aoyagi p.6 / Hironaka; design-spec §7.1) -/

/-- **S2 (cited).** The normal-crossing extraction of the RLCT value and pole order for a weighted
monomial integral. The threshold of `∫ (∏ uⱼ^{hⱼ}) (∏ uⱼ^{2kⱼ})^{−c}` is `min_j (h_j+1)/(2k_j)`,
and — **in the singular case `∃ j, kⱼ ≠ 0`** — the analytic pole order equals the number of axes
attaining that minimum (per axis: `∫₀^ε u^{h−2kc} du < ∞ ⟺ c < (h+1)/(2k)`; the order is the
binding-factor multiplicity). This is the **single permitted external citation** (Watanabe; Hironaka
resolution). The cover, change-of-variables, properness, and bump-independence are **not** cited —
they are proven on our side (S1, R1). The order half is the genuine analytic content (the
meromorphic pole-order computation for a product of one-variable factors; Codex audit §4), which is
why it equates the opaque `monomialOrderAnalytic` to the combinatorial `monomialOrder`.

The order-half is **scoped to `∃ j, kⱼ ≠ 0`** (Rung-0c FLAG 1): when all `kⱼ = 0` the integrand is a
unit (`F ≢ 0` at the point — the non-singular `F(w*)≠0` chart), every `axisRatio = ⊤` ties, and the
unconditional `monomialOrder = d` would be a stray claim about a regular point's pole order. The
threshold-half is correct in that degenerate case too (`⨅ ⊤ = ⊤`, the locally-nonvanishing RLCT),
so it stays unconditional; only the order-conjunct carries the singularity hypothesis. -/
axiom monomial_rlct (d : ℕ) (k h : Fin d → ℕ) :
    monomialThreshold d k h = (⨅ j : Fin d, axisRatio (h j) (k j))
    ∧ ((∃ j : Fin d, k j ≠ 0) → monomialOrderAnalytic d k h = monomialOrder d k h)

/-! ### R1.2 threshold-level divisor arithmetic (the lower/upper bracket; shape-independent).
The per-axis seeds `axisRatio_regularSeq` / `axisRatio_ge_of_mult` lift through S2's threshold value
`monomialThreshold = ⨅ axisRatio` to the chart threshold. These bracket a chart's threshold and are
the arithmetic the R1 value-match assembly consumes: the lower bound (every divisor obeys the
multiplicity bound ⟹ threshold `≥ m/2`) and the upper bound (one binding divisor realises `c/2`). -/

/-- **R1.2 lower bound (multiplicity control at the threshold).** If every axis obeys the
multiplicity bound `m·kⱼ ≤ hⱼ+1` (regular sequence: `kⱼ=1` ⟹ `m ≤ hⱼ+1`), the chart threshold is
`≥ m/2`. Lifts `axisRatio_ge_of_mult` over the axes via S2 (`monomial_rlct.1` + `le_iInf`). With
`m = min_t Mval` this is the per-chart half of `min over charts ≥ ½·min_t Mval`. -/
theorem monomialThreshold_ge_of_mult (d : ℕ) (k h : Fin d → ℕ) (m : ℕ)
    (hk : ∀ j, 1 ≤ k j) (hmult : ∀ j, m * k j ≤ h j + 1) :
    (m : ℝ≥0∞) / 2 ≤ monomialThreshold d k h := by
  rw [(monomial_rlct d k h).1]
  exact le_iInf (fun j => axisRatio_ge_of_mult (h j) (k j) m (hk j) (hmult j))

/-- **R1.2 upper bound (one axis bounds the threshold).** A single axis's ratio bounds the chart
threshold above (`monomial_rlct.1` + `iInf_le`): the binding-divisor seed. -/
theorem monomialThreshold_le_axis (d : ℕ) (k h : Fin d → ℕ) (j : Fin d) :
    monomialThreshold d k h ≤ axisRatio (h j) (k j) := by
  rw [(monomial_rlct d k h).1]; exact iInf_le _ j

/-- **R1.2 binding divisor (upper bound `c/2`).** A regular-sequence binding axis `(kⱼ,hⱼ)=(1,c−1)`
makes the chart threshold `≤ c/2` (the binding divisor over a codim-`c` stratum realises `½·c`).
With `c = Mval(t)` at the minimizing stratum this is the upper half of the value-match. -/
theorem monomialThreshold_le_regularSeq (d : ℕ) (k h : Fin d → ℕ) (c : ℕ) (hc : 1 ≤ c) (j : Fin d)
    (hkj : k j = 1) (hhj : h j = c - 1) :
    monomialThreshold d k h ≤ (c : ℝ≥0∞) / 2 := by
  refine (monomialThreshold_le_axis d k h j).trans ?_
  rw [hkj, hhj, axisRatio_regularSeq c hc]

/-! ## S1 — RLCT invariance substrate (thread 05; design-spec §8)

The shared analytic linchpin, in the `weightedThreshold` abstraction (`Foundations/Rlct.lean`):
**S1.1** weighted-threshold TRANSPORT (the heavy core), then the corollaries **S1.2** monotonicity,
**S1.3** ideal-invariance / germ-locality (the encoded `rlct_unit_invariant` + `rlct_germ_local`),
**S1.4** Σ_X-elimination + φ-independence, and **S1.5** disjoint-block additivity (the engine of the
L2 regular/core split). -/

/-- **S1.1 (the linchpin — weighted-threshold transport; thread 05).** Transport of the weighted
RLCT threshold along a **proper, a.e.-analytic diffeo** `π` on a finite-dim real space: off a null
set `E`, `π` is injective and differentiable with derivative `Dπ`, and `π` is proper. Then
`θ(F, φ; {w*})` equals `θ(F∘π, (φ∘π)·|det Dπ|; π⁻¹{w*})` — the **Jacobian weight `|det Dπ|` is
MANDATORY** (Codex-caught, pp-verified: the *unweighted* `rlctAt(F∘π)=rlctAt(F)` is FALSE — e.g.
`F=x²+y²`, chart `(u,uv)` gives `1/2 ≠ 1`, the missing factor being exactly `|det Dπ|=|u|`). Proof
route (the heaviest analytic lemma below R1): delete `E`, apply Mathlib's Jacobian
change-of-variables on the diffeo part (`integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`),
restore the null set, then properness gives that every nbhd of `w*` pulls back to one of `π⁻¹{w*}`
(fixed-set ↔ local-nbhd integrability). D1 takes the single-map form; R1 per-chart + finite `min`.

Rung-0c FLAG (measure pin): the unconstrained `[MeasureSpace M]` made the bare statement **FALSE**
(Codex: on `ℝ` with weight `|x| dx`, `π = x³` gives `2 ≠ 4/3`) — the Jacobian-change-of-variables
the proof route needs holds for the **additive Haar / Lebesgue** measure, not an arbitrary one.
Pinned via `[(volume : Measure M).IsAddHaarMeasure]`; `MeasurableSet E` added (with `volume E = 0`,
the proof's null-set deletion + the Luzin-N image `π(E)` null are then available). The
Jacobian-weight placement was already correct, kept. Non-vacuous: equates two thresholds. -/
theorem weightedThreshold_transport
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M]
    [FiniteDimensional ℝ M] [(volume : Measure M).IsAddHaarMeasure]
    (F φ : M → ℝ) (wstar : M)
    (π : M → M) (Dπ : M → (M →L[ℝ] M)) (E : Set M)
    (hproper : IsProperMap π)
    (hE_meas : MeasurableSet E)
    (hE_null : volume E = 0)
    (hinj : Set.InjOn π Eᶜ)
    (hderiv : ∀ m ∈ Eᶜ, HasFDerivAt π (Dπ m) m)
    (hsurj : Function.Surjective π)
    (hImE : volume (π '' E) = 0) :
    weightedThreshold F φ {wstar}
      = weightedThreshold (F ∘ π) (fun m => φ (π m) * |(Dπ m).det|) (π ⁻¹' {wstar}) :=
  weightedThreshold_transport_aux F φ wstar π Dπ E hproper hE_meas hE_null hinj hderiv hsurj hImE

/-- **S1.3 (Lemma 1, ideal invariance core).** The RLCT is invariant under multiplying `F` by a unit
`u` (measurable, bounded `0 < a ≤ |u| ≤ b` near `w*`) — the operative "depends only on the ideal"
content (reduces `λ(⟨Fᵢ⟩)` to `λ(∑Fᵢ²)`, removes the bump and `Σ_X`). `Measurable u` is the
11th-finding fidelity fix (the integrand pushforward needs it). Wired to `rlct_unit_invariant_aux`
(`Foundations/S1Local`). Non-vacuous: equates the RLCT of `u·F` to that of `F`. -/
theorem rlct_unit_invariant (H : Fin (L + 1) → ℕ) (F u : Params H → ℝ) (wstar : Params H)
    (a b : ℝ) (ha : 0 < a) (hmeas : Measurable u)
    (hu : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, a ≤ |u w| ∧ |u w| ≤ b) :
    rlctAt H (fun w => u w * F w) wstar = rlctAt H F wstar :=
  rlct_unit_invariant_aux H F u wstar a b ha hmeas hu

/-- **S1.4 (germ-locality / φ-independence).** The RLCT depends only on the germ of `F` at `w*`: if
`F` and `G` agree on a neighbourhood of `w*`, their RLCTs are equal. This is the bump-independence
content (the threshold is determined by the local behaviour near `w*`) and is what lets S2's
bump-free monomial conclusion connect to the bumped resolution. Non-vacuous: it equates `rlctAt F`
and `rlctAt G` from a local-agreement hypothesis. -/
theorem rlct_germ_local (H : Fin (L + 1) → ℕ) (F G : Params H → ℝ) (wstar : Params H)
    (hFG : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, F w = G w) :
    rlctAt H F wstar = rlctAt H G wstar :=
  rlct_germ_local_aux H F G wstar hFG

/-- **S1.5 (RLCT additivity — the smooth/regular block; thread 07, the L2-use form).** Splitting off
a **nondegenerate-quadratic** (regular) block from a disjoint singular block: for `Σᵢ xᵢ²` in the
fresh coordinates `x : Fin n → ℝ` and any `G(y)` on a disjoint block `Y`,
`λ(Σᵢ xᵢ² + G(y)²) = n/2 + λ(G(y)²)`. This is **exactly what L2 consumes** — the regular generators
of the block-reduced loss form a sum of squared coordinates (RLCT `= dim/2`), disjoint from the
singular core, so their ½-contributions add to `λ_core` to give the `[−r²+r(H¹+Hᴸ⁺¹)]/2` regular
shift.

Scope note (controller decision): stated at the **smooth-block specificity the claim needs**, NOT
the fully general real-analytic disjoint additivity (Aoyagi App. C Lemma 2). The bare-measurable
general form is FALSE (Codex: alternating step functions give `⊤ ≠ 2`) and the general real-analytic
version needs heavy Laplace/Tauberian machinery — a **roadmap** lemma off the critical path, not
carried here. The smooth block (`Σ xᵢ²`, RLCT `n/2`) is analytic-clean and closes the rung. Stated
on `rlctAtOn` (general singular block `Y`; the regular block is `Fin n → ℝ` at the origin).
Non-vacuous: equates the joint RLCT to `n/2` plus the block RLCT. **13th-finding fix (fm-2):** the
bare form is FALSE for a germ-vanishing block (`G ≡ 0` near `y0` ⟹ the block RLCT is `⊤`, so the LHS
`n/2 + ⊤ = ⊤` while the joint side need not be — `rlctAtOn_zero_eq_top`). Guarded by `hGmeas`
(`Measurable G`) + `hGne` (`G ≠ 0` a.e. on a nbhd of `y0`), the germ hygiene fm-2's lift uses. -/
theorem rlct_additive_smooth_block {n : ℕ}
    {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y]
    (G : Y → ℝ) (y0 : Y) (hGmeas : Measurable G)
    (hGne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), G z ≠ 0) :
    rlctAtOn (fun p : (Fin n → ℝ) × Y => (∑ i, p.1 i ^ 2) + G p.2 ^ 2) (0, y0)
      = (n : ENNReal) / 2 + rlctAtOn (fun y => G y ^ 2) y0 :=
  rlct_additive_smooth_block_aux G y0 hGmeas hGne n

/-! ## L1 / L2 — block elimination + product reduction (design-spec §8) -/

section BlockElim
open Matrix LinearMap Module

/-- Rank data for `block_elimination`: `finrank ker = b - r`, `r ≤ b`, `r ≤ a`. -/
private lemma block_elimination_rank_data {a b r : ℕ}
    (B : Matrix (Fin a) (Fin b) ℝ) (hB : B.rank = r) :
    Module.finrank ℝ (LinearMap.ker B.mulVecLin) = b - r ∧ r ≤ b ∧ r ≤ a := by
  classical
  have hrange : Module.finrank ℝ (LinearMap.range B.mulVecLin) = r := by
    simpa [Matrix.rank] using hB
  have hsum0 :
      Module.finrank ℝ (LinearMap.range B.mulVecLin)
        + Module.finrank ℝ (LinearMap.ker B.mulVecLin)
        = Module.finrank ℝ (Fin b → ℝ) :=
    B.mulVecLin.finrank_range_add_finrank_ker
  have hsum : r + Module.finrank ℝ (LinearMap.ker B.mulVecLin) = b := by
    simpa [hrange, Module.finrank_fin_fun] using hsum0
  have hker : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = b - r := by
    omega
  have hrb : r ≤ b := by
    omega
  have hra : r ≤ a := by
    simpa [hB] using Matrix.rank_le_height B
  exact ⟨hker, hrb, hra⟩


/-- **L1 (Lemma 2, block elimination).** For a rank-`r` target `B`, regular row/column operations
(Gaussian elimination / Schur complement) carry `B` to the **block-normal form** `diag(E_r, 0)`:
there exist invertible `P, Q` with `P·B·Q` the matrix that is the identity on the top-left `r×r`
block and `0` elsewhere. The reduction realising the regular/singular block split. (Rung-0c FLAG:
the old conclusion `(P·B·Q).rank = r` was **vacuous** — rank is unit-invariant, so it holds for any
units; the real content is the *explicit normal form*, which pins the block structure L2 needs.)
Non-vacuous: it asserts `P·B·Q` equals a specific matrix, not merely its rank. -/
theorem block_elimination (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r) :
    ∃ (P : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
      (Q : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ),
      IsUnit P ∧ IsUnit Q ∧
        P * B * Q = Matrix.of (fun (i : Fin (H 0)) (j : Fin (H (Fin.last L))) =>
          if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  classical
  let a := H 0
  let b := H (Fin.last L)
  let f : (Fin b → ℝ) →ₗ[ℝ] (Fin a → ℝ) := B.mulVecLin

  rcases block_elimination_rank_data (a := a) (b := b) (r := r) B hB with
    ⟨hkerB, hrb, hra⟩

  have hrange : Module.finrank ℝ (LinearMap.range f) = r := by
    simpa [f, Matrix.rank] using hB
  have hker : Module.finrank ℝ (LinearMap.ker f) = b - r := by
    simpa [f] using hkerB

  have hcoker : Module.finrank ℝ ((Fin a → ℝ) ⧸ LinearMap.range f) = a - r := by
    have hq :
        Module.finrank ℝ ((Fin a → ℝ) ⧸ LinearMap.range f)
          + Module.finrank ℝ (LinearMap.range f)
          = Module.finrank ℝ (Fin a → ℝ) :=
      Submodule.finrank_quotient_add_finrank _
    have hq' :
        Module.finrank ℝ ((Fin a → ℝ) ⧸ LinearMap.range f) + r = a := by
      simpa [hrange, Module.finrank_fin_fun] using hq
    omega

  let bKer : Basis (Fin (b - r)) ℝ (LinearMap.ker f) :=
    Module.finBasisOfFinrankEq ℝ (LinearMap.ker f) hker
  let bRange : Basis (Fin r) ℝ (LinearMap.range f) :=
    Module.finBasisOfFinrankEq ℝ (LinearMap.range f) hrange

  let bDomQuot : Basis (Fin r) ℝ ((Fin b → ℝ) ⧸ LinearMap.ker f) :=
    bRange.map (LinearMap.quotKerEquivRange f).symm
  let bCoker : Basis (Fin (a - r)) ℝ ((Fin a → ℝ) ⧸ LinearMap.range f) :=
    Module.finBasisOfFinrankEq ℝ ((Fin a → ℝ) ⧸ LinearMap.range f) hcoker

  let bDomRaw : Basis (Fin (b - r) ⊕ Fin r) ℝ (Fin b → ℝ) :=
    bKer.sumQuot bDomQuot
  let bDomS : Basis (Fin r ⊕ Fin (b - r)) ℝ (Fin b → ℝ) :=
    bDomRaw.reindex (Equiv.sumComm (Fin (b - r)) (Fin r))
  let bCodS : Basis (Fin r ⊕ Fin (a - r)) ℝ (Fin a → ℝ) :=
    bRange.sumQuot bCoker

  have hDomInl (j : Fin r) :
      f (bDomS (Sum.inl j)) = ((bRange j : LinearMap.range f) : Fin a → ℝ) := by
    have hq : Submodule.Quotient.mk (bDomS (Sum.inl j)) = bDomQuot j := by
      simpa [bDomS, bDomRaw] using
        (Module.Basis.sumQuot_inr bKer bDomQuot j)
    have h :=
      congrArg (fun q => ((LinearMap.quotKerEquivRange f) q : Fin a → ℝ)) hq
    simpa [bDomQuot, LinearMap.quotKerEquivRange] using h

  have hDomInr (j : Fin (b - r)) :
      f (bDomS (Sum.inr j)) = 0 := by
    change bDomS (Sum.inr j) ∈ LinearMap.ker f
    simpa [bDomS, bDomRaw] using (bKer j).2

  let Sigma : Matrix (Fin r ⊕ Fin (a - r)) (Fin r ⊕ Fin (b - r)) ℝ :=
    Matrix.of fun i j =>
      match i, j with
      | Sum.inl i', Sum.inl j' => if i' = j' then (1 : ℝ) else 0
      | _, _ => 0

  have hSigma : LinearMap.toMatrix bDomS bCodS f = Sigma := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            rw [LinearMap.toMatrix_apply, hDomInl j]
            dsimp [Sigma]
            rw [Module.Basis.sumQuot_repr_left bRange bCoker j, Finsupp.single_apply]
            simp [eq_comm]
        | inr j =>
            rw [LinearMap.toMatrix_apply, hDomInr j]
            simp [Sigma]
    | inr i =>
        cases j with
        | inl j =>
            rw [LinearMap.toMatrix_apply, hDomInl j]
            dsimp [Sigma]
            rw [Module.Basis.sumQuot_repr_inr_of_mem bRange bCoker _ (bRange j).2 i]
        | inr j =>
            rw [LinearMap.toMatrix_apply, hDomInr j]
            simp [Sigma]

  let eRows : (Fin r ⊕ Fin (a - r)) ≃ Fin a :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hra))
  let eCols : (Fin r ⊕ Fin (b - r)) ≃ Fin b :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hrb))

  let bDom : Basis (Fin b) ℝ (Fin b → ℝ) := bDomS.reindex eCols
  let bCod : Basis (Fin a) ℝ (Fin a → ℝ) := bCodS.reindex eRows

  have hReindex :
      LinearMap.toMatrix bDom bCod f =
        (LinearMap.toMatrix bDomS bCodS f).submatrix eRows.symm eCols.symm := by
    ext i j
    simp [bDom, bCod, LinearMap.toMatrix_apply]

  have hBlock :
      LinearMap.toMatrix bDom bCod f =
        Matrix.of (fun (i : Fin a) (j : Fin b) =>
          if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
    rw [hReindex, hSigma]
    ext i j
    dsimp [Sigma]

    have row_inl_val :
        ∀ {i : Fin a} {ir : Fin r}, eRows.symm i = Sum.inl ir → (i : ℕ) = (ir : ℕ) := by
      intro i ir hi
      have hi' : i = eRows (Sum.inl ir) := by
        calc
          i = eRows (eRows.symm i) := (Equiv.apply_symm_apply eRows i).symm
          _ = eRows (Sum.inl ir) := by rw [hi]
      simpa [eRows] using congrArg Fin.val hi'

    have row_inr_val :
        ∀ {i : Fin a} {ir : Fin (a - r)},
          eRows.symm i = Sum.inr ir → (i : ℕ) = r + (ir : ℕ) := by
      intro i ir hi
      have hi' : i = eRows (Sum.inr ir) := by
        calc
          i = eRows (eRows.symm i) := (Equiv.apply_symm_apply eRows i).symm
          _ = eRows (Sum.inr ir) := by rw [hi]
      simpa [eRows] using congrArg Fin.val hi'

    have col_inl_val :
        ∀ {j : Fin b} {jr : Fin r}, eCols.symm j = Sum.inl jr → (j : ℕ) = (jr : ℕ) := by
      intro j jr hj
      have hj' : j = eCols (Sum.inl jr) := by
        calc
          j = eCols (eCols.symm j) := (Equiv.apply_symm_apply eCols j).symm
          _ = eCols (Sum.inl jr) := by rw [hj]
      simpa [eCols] using congrArg Fin.val hj'

    have col_inr_val :
        ∀ {j : Fin b} {jr : Fin (b - r)},
          eCols.symm j = Sum.inr jr → (j : ℕ) = r + (jr : ℕ) := by
      intro j jr hj
      have hj' : j = eCols (Sum.inr jr) := by
        calc
          j = eCols (eCols.symm j) := (Equiv.apply_symm_apply eCols j).symm
          _ = eCols (Sum.inr jr) := by rw [hj]
      simpa [eCols] using congrArg Fin.val hj'

    rcases hi : eRows.symm i with ir | ia
    · have hiVal := row_inl_val hi
      rcases hj : eCols.symm j with jr | jb
      · have hjVal := col_inl_val hj
        by_cases hij : ir = jr
        · subst jr
          have hcond : (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r := by
            constructor
            · omega
            · simpa [hiVal] using ir.isLt
          rw [if_pos hcond]
          simp [Matrix.submatrix_apply, Matrix.of_apply, hi, hj]
        · have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
            intro hc
            apply hij
            ext
            omega
          simp [Matrix.submatrix_apply, Matrix.of_apply, hi, hj, hij, hcond]
      · have hjVal := col_inr_val hj
        have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
          intro hc
          omega
        simp [Matrix.submatrix_apply, Matrix.of_apply, hi, hj, hcond]
    · have hiVal := row_inr_val hi
      have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
        intro hc
        omega
      simp [Matrix.submatrix_apply, Matrix.of_apply, hi, hcond]

  let stdV : Basis (Fin b) ℝ (Fin b → ℝ) := Pi.basisFun ℝ (Fin b)
  let stdW : Basis (Fin a) ℝ (Fin a → ℝ) := Pi.basisFun ℝ (Fin a)

  have hstdLin : Matrix.toLin stdV stdW B = f := by
    dsimp [stdV, stdW, f]
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply']

  have hBstd : LinearMap.toMatrix stdV stdW f = B := by
    rw [← hstdLin]
    exact LinearMap.toMatrix_toLin stdV stdW B

  let P : Matrix (Fin a) (Fin a) ℝ := bCod.toMatrix stdW
  let Q : Matrix (Fin b) (Fin b) ℝ := stdV.toMatrix bDom

  refine ⟨P, Q, ?_, ?_, ?_⟩
  · dsimp [P]
    letI := Module.Basis.invertibleToMatrix bCod stdW
    exact isUnit_of_invertible _
  · dsimp [Q]
    letI := Module.Basis.invertibleToMatrix stdV bDom
    exact isUnit_of_invertible _
  · calc
      P * B * Q
          = P * (LinearMap.toMatrix stdV stdW f) * Q := by
              rw [← hBstd]
      _ = LinearMap.toMatrix bDom bCod f := by
              simpa [P, Q] using
                (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
                  bDom stdV bCod stdW f)
      _ = Matrix.of (fun (i : Fin a) (j : Fin b) =>
              if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := hBlock

end BlockElim

/-- **Deepest layers** (the SUFFICIENT characterization; pp + Codex, lessons 2026-06-20):
`w` lies in the fibre **and** every layer `A⁽ˢ⁾ = w s` is at rank exactly `r`, `rank (w s) = r`
(achievable since `r ≤ H⁽ˢ⁾` along a rank-`r` fibre's path). This is **sufficient** for the deepest
(maximal-local-RLCT) point — it implies all partial products are rank-`r` by submultiplicativity,
and the local RLCT is constant over it (a single GL gauge orbit). It is *not exhaustive* of the
λ-attaining set (the full set is larger — residual freedom), which is why we key D1/L2 to ONE
constructed `deepestPoint` rather than this `∀`-predicate. (The discarded per-partial-product form
was *too weak* — `(2,2,2)`, `(A¹=0, A² invertible)` has all partial products rank `0` but local RLCT
`2 ≠ 3/2`.) Used only to characterize the witness `deepestPoint_exists` produces. -/
def IsDeepLayers (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (w : Params H) : Prop :=
  w ∈ optimalSet H B ∧ ∀ s : Fin L, (w s).rank = r

/-- `[I_r|0] · [I_r;0] = I_r`: projection ∘ embedding (a left inverse) on `Fin r`. -/
private theorem proj_emb_eq_one {N r : ℕ} (hrN : r ≤ N) :
    (Matrix.of (fun (k : Fin r) (j : Fin N) => if (k : ℕ) = (j : ℕ) then (1 : ℝ) else 0))
      * (Matrix.of (fun (j : Fin N) (k : Fin r) => if (j : ℕ) = (k : ℕ) then (1 : ℝ) else 0))
    = (1 : Matrix (Fin r) (Fin r) ℝ) := by
  ext k k'; simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin N)]
  · show (if (k : ℕ) = ((⟨k, _⟩ : Fin N) : ℕ) then (1 : ℝ) else 0)
        * (if ((⟨k, _⟩ : Fin N) : ℕ) = (k' : ℕ) then (1 : ℝ) else 0) = _
    rw [Fin.val_mk, if_pos rfl, one_mul]
    by_cases h : (k : ℕ) = (k' : ℕ)
    · rw [if_pos h, if_pos (Fin.ext h)]
    · rw [if_neg h, if_neg (fun he => h (by rw [he]))]
  · intro b _ hb; rw [if_neg (fun he => hb (Fin.ext (by simpa using he.symm))), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The `r×r`-identity-corner block `diag(E_r, 0)` factors as `[I_r;0] · [I_r|0]`. -/
private theorem Dblock_factor {m n r : ℕ} :
    (Matrix.of (fun (i:Fin m) (j:Fin n) => if (i:ℕ) = (j:ℕ) ∧ (i:ℕ) < r then (1:ℝ) else 0))
      = (Matrix.of (fun (i : Fin m) (k : Fin r) => if (i : ℕ) = (k : ℕ) then (1 : ℝ) else 0))
        * (Matrix.of (fun (k:Fin r) (j:Fin n) => if (k:ℕ) = (j:ℕ) then (1:ℝ) else 0)) := by
  ext i j; simp only [Matrix.mul_apply, Matrix.of_apply]
  by_cases hi : (i : ℕ) < r
  · rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
    · show (if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)
        = (if (i : ℕ) = ((⟨i, hi⟩ : Fin r) : ℕ) then (1 : ℝ) else 0)
          * (if ((⟨i, hi⟩ : Fin r) : ℕ) = (j : ℕ) then (1 : ℝ) else 0)
      rw [Fin.val_mk, if_pos rfl, one_mul]
      by_cases hij : (i : ℕ) = (j : ℕ)
      · rw [if_pos hij, if_pos ⟨hij, hi⟩]
      · rw [if_neg hij, if_neg (fun h => hij h.1)]
    · intro k _ hk
      rw [if_neg (by simpa [Fin.ext_iff] using fun h => hk (Fin.ext h.symm)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg (by tauto), Finset.sum_eq_zero]; intro k _; rw [if_neg (by intro h; omega), zero_mul]

/-- The `r×r`-identity-corner block has rank exactly `r` (when `r ≤ m, n`): `≤ r` from the
`Dc · Dr` factorisation (`Dc` has `r` columns); `≥ r` because `Dc` has both a left inverse
(`[I_r|0]·Dc = I_r`) and `Dc = (Dc·Dr)·[I_r;0]`, so `r = rank I_r ≤ rank Dc ≤ rank (Dc·Dr)`. -/
private theorem Dblock_rank {m n r : ℕ} (hrm : r ≤ m) (hrn : r ≤ n) :
    (Matrix.of (fun (i : Fin m) (j : Fin n) =>
      if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)).rank = r := by
  set Dc : Matrix (Fin m) (Fin r) ℝ := Matrix.of (fun i k => if (i:ℕ) = (k:ℕ) then (1:ℝ) else 0)
  set Dr : Matrix (Fin r) (Fin n) ℝ := Matrix.of (fun k j => if (k:ℕ) = (j:ℕ) then (1:ℝ) else 0)
  set Sec : Matrix (Fin n) (Fin r) ℝ := Matrix.of (fun j k => if (j:ℕ) = (k:ℕ) then (1:ℝ) else 0)
  set DrM : Matrix (Fin r) (Fin m) ℝ := Matrix.of (fun k i => if (k:ℕ) = (i:ℕ) then (1:ℝ) else 0)
  have hfac : (Matrix.of (fun (i : Fin m) (j : Fin n) =>
      if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)) = Dc * Dr := Dblock_factor
  rw [hfac]
  have hle : (Dc * Dr).rank ≤ r := le_trans (Matrix.rank_mul_le_left _ _)
    (le_trans (Matrix.rank_le_card_width _) (by rw [Fintype.card_fin]))
  have hDceq : (Dc * Dr) * Sec = Dc := by
    rw [Matrix.mul_assoc, (proj_emb_eq_one hrn : Dr * Sec = 1), Matrix.mul_one]
  have hge : r ≤ (Dc * Dr).rank := by
    calc r = (1 : Matrix (Fin r) (Fin r) ℝ).rank := by rw [Matrix.rank_one, Fintype.card_fin]
      _ = (DrM * Dc).rank := by rw [(proj_emb_eq_one hrm : DrM * Dc = 1)]
      _ ≤ Dc.rank := Matrix.rank_mul_le_right _ _
      _ = ((Dc * Dr) * Sec).rank := by rw [hDceq]
      _ ≤ (Dc * Dr).rank := Matrix.rank_mul_le_left _ _
  exact le_antisymm hle hge

/-- The product of the all-zero parameter tuple is the zero matrix (for `L ≥ 1`, the recursion has a
last layer `= 0` that zeroes the fold). -/
private theorem prodAux_zero (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k + 1 < L + 1) :
    prodAux H (fun _ => 0) (k + 1) hk = 0 := by
  rw [prodAux]; convert Matrix.mul_zero _

private theorem prod_zero (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) : prod H (fun _ => 0) = 0 := by
  unfold prod
  obtain ⟨k, hk⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  subst hk
  exact prodAux_zero H k (Nat.lt_succ_self _)

/-- A rank-0 matrix over ℝ is the zero matrix. -/
private theorem rank_zero_eq_zero {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (hB : B.rank = 0) :
    B = 0 := by
  have hr0 : LinearMap.range B.mulVecLin = ⊥ := by
    rw [← Submodule.finrank_eq_zero (R := ℝ)]; exact hB
  rw [LinearMap.range_eq_bot] at hr0
  ext i j
  have := LinearMap.congr_fun hr0 (Pi.single j 1)
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using congrFun this i

/-! ### Helpers for the `r > 0` case of `deepestPoint_exists` (the rank-`r` layer chain). -/

/-- `[I_r|0]_{r→N}` (projection): `r × N`, ones on the diagonal `(k,k)`. -/
private def projM (r N : ℕ) : Matrix (Fin r) (Fin N) ℝ :=
  Matrix.of (fun (k : Fin r) (j : Fin N) => if (k : ℕ) = (j : ℕ) then (1 : ℝ) else 0)

/-- `[I_r;0]_{N→r}` (embedding): `N × r`, ones on the diagonal `(k,k)`. -/
private def embM (N r : ℕ) : Matrix (Fin N) (Fin r) ℝ :=
  Matrix.of (fun (j : Fin N) (k : Fin r) => if (j : ℕ) = (k : ℕ) then (1 : ℝ) else 0)

/-- The `r×r`-identity-corner block `diag(E_r, 0)`: `m × n`. -/
private def corM (r m n : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of (fun (i : Fin m) (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)

/-- `projM r N * embM N r = I_r` (projection ∘ embedding is the identity on `Fin r`). -/
private theorem projM_embM (N r : ℕ) (hrN : r ≤ N) :
    projM r N * embM N r = (1 : Matrix (Fin r) (Fin r) ℝ) := by
  ext k k'; simp only [projM, embM, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin N)]
  · simp only [if_true, one_mul]
    by_cases h : (k : ℕ) = (k' : ℕ)
    · rw [if_pos h, if_pos (Fin.ext h)]
    · rw [if_neg h, if_neg (fun he => h (by rw [he]))]
  · intro b _ hb; rw [if_neg (fun he => hb (Fin.ext (by simpa using he.symm))), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The telescoping step: `projM r M * corM r M N = projM r N` (a corner block absorbs into a
projection). -/
private theorem projM_corM (r M N : ℕ) (hrM : r ≤ M) : projM r M * corM r M N = projM r N := by
  ext k j; simp only [projM, corM, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin M)]
  · simp only [if_true, one_mul]
    have hk : (k : ℕ) < r := k.isLt
    by_cases h : (k : ℕ) = (j : ℕ)
    · rw [if_pos ⟨h, hk⟩, if_pos h]
    · rw [if_neg (fun hc => h hc.1), if_neg h]
  · intro b _ hb; rw [if_neg (fun he => hb (Fin.ext (by simpa using he.symm))), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `rank (U * projM r N) = rank U` (`projM` is right-invertible by `embM`). -/
private theorem rank_mul_projM {a : ℕ} (r N : ℕ) (hrN : r ≤ N) (U : Matrix (Fin a) (Fin r) ℝ) :
    (U * projM r N).rank = U.rank := by
  apply le_antisymm (Matrix.rank_mul_le_left _ _)
  calc U.rank = (U * projM r N * embM N r).rank := by
        rw [Matrix.mul_assoc, projM_embM N r hrN, Matrix.mul_one]
    _ ≤ (U * projM r N).rank := Matrix.rank_mul_le_left _ _

/-- `rank (embM N r * V) = rank V` (`embM` is left-invertible by `projM`). -/
private theorem rank_embM_mul {c : ℕ} (N r : ℕ) (hrN : r ≤ N) (V : Matrix (Fin r) (Fin c) ℝ) :
    (embM N r * V).rank = V.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  calc V.rank = (projM r N * (embM N r * V)).rank := by
        rw [← Matrix.mul_assoc, projM_embM N r hrN, Matrix.one_mul]
    _ ≤ (embM N r * V).rank := Matrix.rank_mul_le_right _ _

/-- The corner block has rank exactly `r` (when `r ≤ m, n`). -/
private theorem corM_rank {m n r : ℕ} (hrm : r ≤ m) (hrn : r ≤ n) : (corM r m n).rank = r := by
  have hfac : corM r m n = embM m r * projM r n := by
    ext i j; simp only [corM, embM, projM, Matrix.mul_apply, Matrix.of_apply]
    by_cases hi : (i : ℕ) < r
    · rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · simp only [if_true, one_mul]
        by_cases hij : (i : ℕ) = (j : ℕ)
        · rw [if_pos hij, if_pos ⟨hij, hi⟩]
        · rw [if_neg hij, if_neg (fun hc => hij hc.1)]
      · intro b _ hb
        rw [if_neg (by simpa [Fin.ext_iff] using fun h => hb (Fin.ext h.symm)), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg (by tauto)]; symm
      apply Finset.sum_eq_zero; intro k _; rw [if_neg (by intro h; omega), zero_mul]
  rw [hfac]
  apply le_antisymm
  · exact le_trans (Matrix.rank_mul_le_right _ _) (Matrix.rank_le_height _)
  · calc r = (1 : Matrix (Fin r) (Fin r) ℝ).rank := by rw [Matrix.rank_one, Fintype.card_fin]
      _ = (projM r m * embM m r).rank := by rw [projM_embM m r hrm]
      _ ≤ (embM m r).rank := Matrix.rank_mul_le_right _ _
      _ = (embM m r * (projM r n * embM n r)).rank := by rw [projM_embM n r hrn, Matrix.mul_one]
      _ = (embM m r * projM r n * embM n r).rank := by rw [Matrix.mul_assoc]
      _ ≤ (embM m r * projM r n).rank := Matrix.rank_mul_le_left _ _

/-- From `B = U * V` with `B.rank = r` (`U : a×r`): `U.rank = r`. -/
private theorem rank_factor_left {a c r : ℕ} (U : Matrix (Fin a) (Fin r) ℝ)
    (V : Matrix (Fin r) (Fin c) ℝ) (B : Matrix (Fin a) (Fin c) ℝ) (hB : B = U * V)
    (hr : B.rank = r) : U.rank = r := by
  have hle : U.rank ≤ r := le_trans (Matrix.rank_le_card_width _) (by rw [Fintype.card_fin])
  have hge : r ≤ U.rank := by
    have : B.rank ≤ U.rank := by rw [hB]; exact Matrix.rank_mul_le_left _ _
    omega
  omega

/-- From `B = U * V` with `B.rank = r` (`V : r×c`): `V.rank = r`. -/
private theorem rank_factor_right {a c r : ℕ} (U : Matrix (Fin a) (Fin r) ℝ)
    (V : Matrix (Fin r) (Fin c) ℝ) (B : Matrix (Fin a) (Fin c) ℝ) (hB : B = U * V)
    (hr : B.rank = r) : V.rank = r := by
  have hle : V.rank ≤ r := Matrix.rank_le_height V
  have hge : r ≤ V.rank := by
    have : B.rank ≤ V.rank := by rw [hB]; exact Matrix.rank_mul_le_right _ _
    omega
  omega

/-- `B = (P⁻¹ · embM) · (projM · Q⁻¹)` from the block-elimination normal form `P·B·Q = corner`. -/
private theorem factor_from_blockElim {a c r : ℕ} (B : Matrix (Fin a) (Fin c) ℝ)
    (P : Matrix (Fin a) (Fin a) ℝ) (Q : Matrix (Fin c) (Fin c) ℝ) (hP : IsUnit P) (hQ : IsUnit Q)
    (hPBQ : P * B * Q = Matrix.of (fun (i : Fin a) (j : Fin c) =>
        if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)) :
    B = (P⁻¹ * embM a r) * (projM r c * Q⁻¹) := by
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hcorner : Matrix.of (fun (i : Fin a) (j : Fin c) =>
        if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) = embM a r * projM r c := by
    ext i j; simp only [embM, projM, Matrix.mul_apply, Matrix.of_apply]
    by_cases hi : (i : ℕ) < r
    · rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · simp only [if_true, one_mul]
        by_cases hij : (i : ℕ) = (j : ℕ)
        · rw [if_pos hij, if_pos ⟨hij, hi⟩]
        · rw [if_neg hij, if_neg (fun hc => hij hc.1)]
      · intro b _ hb
        rw [if_neg (by simpa [Fin.ext_iff] using fun h => hb (Fin.ext h.symm)), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg (by tauto)]; symm
      apply Finset.sum_eq_zero; intro k _; rw [if_neg (by intro h; omega), zero_mul]
  have key : P⁻¹ * (P * B * Q) * Q⁻¹ = B := by
    rw [Matrix.mul_assoc P B Q, ← Matrix.mul_assoc P⁻¹ P (B * Q),
      Matrix.nonsing_inv_mul P hPd, Matrix.one_mul, Matrix.mul_assoc B Q Q⁻¹,
      Matrix.mul_nonsing_inv Q hQd, Matrix.mul_one]
  calc B = P⁻¹ * (P * B * Q) * Q⁻¹ := key.symm
    _ = P⁻¹ * (embM a r * projM r c) * Q⁻¹ := by rw [hPBQ, hcorner]
    _ = (P⁻¹ * embM a r) * (projM r c * Q⁻¹) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

/-- Casting a layer matrix along value-equal `Fin (L+1)` index changes is entry-wise transparent. -/
private theorem mpr_heq {α β : Sort _} (h : α = β) (x : β) : HEq (Eq.mpr h x) x := by subst h; rfl

/-- HEq with row index fixed: a column-index change of value-equal `Fin (L+1)` indices. -/
private theorem heq_mkCol {T : Type} (H : Fin (L + 1) → ℕ)
    (mk : (q : Fin (L + 1)) → Matrix T (Fin (H q)) ℝ) {b d : Fin (L + 1)} (e : b = d) :
    HEq (mk b) (mk d) := by subst e; rfl

/-- HEq with column index fixed: a row-index change of value-equal `Fin (L+1)` indices. -/
private theorem heq_mkRow {T : Type} (H : Fin (L + 1) → ℕ)
    (mk : (p : Fin (L + 1)) → Matrix (Fin (H p)) T ℝ) {a c : Fin (L + 1)} (e : a = c) :
    HEq (mk a) (mk c) := by subst e; rfl

/-- HEq for both indices changing across value-equal `Fin (L+1)` indices. -/
private theorem heq_mk2 (H : Fin (L + 1) → ℕ)
    (mk : (p q : Fin (L + 1)) → Matrix (Fin (H p)) (Fin (H q)) ℝ)
    {a b c d : Fin (L + 1)} (e1 : a = c) (e2 : b = d) : HEq (mk a b) (mk c d) := by
  subst e1; subst e2; rfl

/-- The `prodAux` recursion-step, with the dependent-`Fin` cast discharged by HEq: if `A ⟨k,_⟩` is
HEq to `Mstep` (typed at the `prodAux` dims), then `prodAux (k+1) = prodAux k * Mstep`. -/
private theorem prodAux_step (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    (Mstep : Matrix (Fin (H ⟨k, Nat.lt_of_succ_lt hk⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)
    (hheq : HEq (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩) Mstep) :
    prodAux H A (k + 1) hk = prodAux H A k (Nat.lt_of_succ_lt hk) * Mstep := by
  rw [prodAux]; congr 1; rw [eq_comm]; apply eq_of_heq
  exact hheq.symm.trans (heq_of_eqRec_eq rfl rfl)

/-- The deep rank-`r` layer chain for `L ≥ 2`: layer `0 = U·[I_r|0]`, middle layers the corner
block, last layer `[I_r;0]·V`. -/
private noncomputable def wLayers (H : Fin (L + 1) → ℕ) (r : ℕ)
    (U : Matrix (Fin (H 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (H (Fin.last L))) ℝ) :
    Params H := fun s =>
  if h0 : (s : ℕ) = 0 then
    (by rw [show s.castSucc = (0 : Fin (L + 1)) from Fin.ext (by simp [Fin.castSucc, h0])]
        exact U * projM r (H s.succ))
  else if hL : (s : ℕ) = L - 1 then
    (by rw [show s.succ = Fin.last L from Fin.ext (by simp [Fin.succ, hL]; omega)]
        exact embM (H s.castSucc) r * V)
  else
    corM r (H s.castSucc) (H s.succ)

section WLayers
variable (H : Fin (L + 1) → ℕ) (r : ℕ)
    (U : Matrix (Fin (H 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (H (Fin.last L))) ℝ)

private theorem heq_layer0 (hk : 0 + 1 < L + 1) :
    HEq (wLayers H r U V ⟨0, Nat.lt_of_succ_lt_succ hk⟩) (U * projM r (H ⟨0 + 1, hk⟩)) := by
  unfold wLayers; rw [dif_pos (by simp)]
  refine HEq.trans ?_ (heq_mkCol H (fun q => U * projM r (H q))
    (b := (⟨0, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ) (d := ⟨0 + 1, hk⟩) (Fin.ext rfl))
  exact mpr_heq _ _

private theorem heq_layerMid (k : ℕ) (hk : k + 1 < L + 1) (hpos : 0 < k) (hlt : k < L - 1) :
    HEq (wLayers H r U V ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
        (corM r (H ⟨k, Nat.lt_of_succ_lt hk⟩) (H ⟨k + 1, hk⟩)) := by
  unfold wLayers
  rw [dif_neg (show ¬ (k = 0) by omega), dif_neg (show ¬ (k = L - 1) by omega)]
  exact heq_mk2 H (fun p q => corM r (H p) (H q))
    (a := (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc) (c := ⟨k, Nat.lt_of_succ_lt hk⟩)
    (b := (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ) (d := ⟨k + 1, hk⟩)
    (Fin.ext rfl) (Fin.ext rfl)

private theorem heq_layerLast (k : ℕ) (hk : k + 1 < L + 1) (hkL : k = L - 1) (hpos : 0 < k) :
    HEq (wLayers H r U V ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
        (embM (H ⟨k, Nat.lt_of_succ_lt hk⟩) r * V) := by
  unfold wLayers
  rw [dif_neg (show ¬ (k = 0) by omega), dif_pos (show k = L - 1 from hkL)]
  refine HEq.trans ?_ (heq_mkRow H (fun p => embM (H p) r * V)
    (a := (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc) (c := ⟨k, Nat.lt_of_succ_lt hk⟩)
    (Fin.ext rfl))
  exact mpr_heq _ _

/-- The partial product up to (but excluding) the last layer: `prodAux m = U · [I_r|0]_{r→H⟨m⟩}`. -/
private theorem prodAux_closed (hrH : ∀ s : Fin (L + 1), r ≤ H s)
    (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L - 1) (hmlt : m < L + 1) :
    prodAux H (wLayers H r U V) m hmlt = U * projM r (H ⟨m, hmlt⟩) := by
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      rw [prodAux_step H (wLayers H r U V) 0 hmlt (U * projM r (H ⟨0 + 1, hmlt⟩))
        (heq_layer0 H r U V hmlt)]
      exact Matrix.one_mul _
    · have hn1 : 1 ≤ n := hnpos
      have hnL : n ≤ L - 1 := by omega
      have hnmid : n < L - 1 := by omega
      rw [prodAux_step H (wLayers H r U V) n hmlt
        (corM r (H ⟨n, Nat.lt_of_succ_lt hmlt⟩) (H ⟨n + 1, hmlt⟩))
        (heq_layerMid H r U V n hmlt hnpos hnmid)]
      rw [ih hn1 hnL (by omega)]
      rw [Matrix.mul_assoc, projM_corM r (H ⟨n, Nat.lt_of_succ_lt hmlt⟩) (H ⟨n + 1, hmlt⟩) (hrH _)]

/-- The full product for `L ≥ 2`: `prod (wLayers) = U · V = B`. -/
private theorem prod_wLayers_ge2 (hrH : ∀ s : Fin (L + 1), r ≤ H s) (hL2 : 2 ≤ L)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hUV : B = U * V) :
    prod H (wLayers H r U V) = B := by
  unfold prod
  obtain ⟨n, hn⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  subst hn
  rw [prodAux_step H (wLayers H r U V) n (Nat.lt_succ_self (n + 1))
    (embM (H ⟨n, Nat.lt_of_succ_lt (Nat.lt_succ_self (n + 1))⟩) r * V)
    (heq_layerLast H r U V n (Nat.lt_succ_self (n + 1)) (by omega) (by omega))]
  rw [prodAux_closed H r U V hrH n (by omega) (by omega)
    (Nat.lt_of_succ_lt (Nat.lt_succ_self (n + 1)))]
  rw [hUV]
  refine Eq.trans (Matrix.mul_assoc U _ _) ?_
  have hPEV : projM r (H ⟨n, Nat.lt_of_succ_lt (Nat.lt_succ_self (n + 1))⟩)
      * (embM (H ⟨n, Nat.lt_of_succ_lt (Nat.lt_succ_self (n + 1))⟩) r * V) = V := by
    rw [← Matrix.mul_assoc,
      projM_embM (H ⟨n, Nat.lt_of_succ_lt (Nat.lt_succ_self (n + 1))⟩) r (hrH _), Matrix.one_mul]
  rw [hPEV]

end WLayers

/-- The single-layer witness for `L = 1`: the sole layer equals `B`. -/
private noncomputable def wSingle (H : Fin (1 + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 1))) ℝ) : Params (L := 1) H := fun s =>
  if h0 : (s : ℕ) = 0 then
    (by rw [show s.castSucc = (0 : Fin (1 + 1)) from Fin.ext (by simp [Fin.castSucc]),
          show s.succ = Fin.last 1 from Fin.ext (by simp [Fin.succ])]
        exact B)
  else 0

private theorem prod_wSingle (H : Fin (1 + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 1))) ℝ) : prod H (wSingle H B) = B := by
  unfold prod
  rw [prodAux_step H (wSingle H B) 0 (Nat.lt_succ_self 1) B (by
    unfold wSingle; rw [dif_pos (by simp)]; exact mpr_heq _ _)]
  exact Matrix.one_mul _

/-- HEq ⟹ equal rank (rank is transported across the value-equal dimension iso). -/
private theorem rank_heq {m1 n1 m2 n2 : ℕ} (A : Matrix (Fin m1) (Fin n1) ℝ)
    (B : Matrix (Fin m2) (Fin n2) ℝ) (hm : m1 = m2) (hn : n1 = n2) (h : HEq A B) :
    A.rank = B.rank := by subst hm; subst hn; rw [eq_of_heq h]



/-- The deepest layers exist for a rank-`r` target (PROVEN). `r = 0` ⟹ the origin / all-zero
tuple; `r > 0` ⟹ factor `B = U·V` (`U, V` rank `r`) via `block_elimination`, then distribute as a
rank-exactly-`r` layer chain — layer `0 = U·[I_r|0]`, the middle layers the `r×r`-identity-corner
block, the last layer `[I_r;0]·V` (single layer `= B` when `L = 1`). The product telescopes to
`U·V = B` (`projM·corM = projM` absorbs the corners, `projM·embM = I_r` at the seam) and each layer
has rank exactly `r`. The hypotheses `hr : ∀ s, r ≤ H s` and `hL : 1 ≤ L` are the well-definedness +
nonemptiness domain: `hr` rules out the middle-width bottleneck (`H=(3,1,3), r=2` caps product rank
at `1 < 2` ⇒ empty fibre) and makes `M⁽ˢ⁾ = H⁽ˢ⁾ − r` non-truncating; `hL` rules out the zero-layer
corner (`L = 0` ⇒ `prod = id` ⇒ fibre needs `B = I`). Verified 484/484, `L ∈ {1,2,3}`. -/
theorem deepestPoint_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Nonempty {w : Params H // IsDeepLayers H r B w} := by
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- r = 0: the all-zero tuple is deep (prod = 0 = B since B.rank = 0).
    subst hr0
    refine ⟨⟨fun _ => 0, ?_, ?_⟩⟩
    · show prod H (fun _ => 0) = B
      rw [prod_zero H hL, rank_zero_eq_zero B hB]
    · intro s; show ((0 : Matrix _ _ ℝ)).rank = 0; exact Matrix.rank_zero
  · -- r > 0: rank factorization B = U·V distributed as rank-exactly-r layers (verified 484/484).
    obtain ⟨P, Q, hP, hQ, hPBQ⟩ := block_elimination H r B hB
    set U : Matrix (Fin (H 0)) (Fin r) ℝ := P⁻¹ * embM (H 0) r with hU
    set V : Matrix (Fin r) (Fin (H (Fin.last L))) ℝ := projM r (H (Fin.last L)) * Q⁻¹ with hV
    have hUV : B = U * V := factor_from_blockElim B P Q hP hQ hPBQ
    have hUr : U.rank = r := rank_factor_left U V B hUV hB
    have hVr : V.rank = r := rank_factor_right U V B hUV hB
    rcases Nat.lt_or_ge L 2 with hL1 | hL2
    · -- L = 1: the sole layer is B itself.
      obtain rfl : L = 1 := by omega
      refine ⟨⟨wSingle H B, prod_wSingle H B, ?_⟩⟩
      rintro ⟨sv, hsvlt⟩
      obtain rfl : sv = 0 := by omega
      have hcast : (⟨0, hsvlt⟩ : Fin 1).castSucc = (0 : Fin (1 + 1)) :=
        Fin.ext (by simp [Fin.castSucc])
      have hsucc : (⟨0, hsvlt⟩ : Fin 1).succ = Fin.last 1 := Fin.ext (by simp [Fin.succ])
      rw [rank_heq (wSingle H B ⟨0, hsvlt⟩) B (congrArg H hcast) (congrArg H hsucc)
        (by unfold wSingle; rw [dif_pos (show ((⟨0, hsvlt⟩ : Fin 1) : ℕ) = 0 from rfl)]
            exact mpr_heq _ _)]
      exact hB
    · -- L ≥ 2: boundary layers (0 and L-1) plus the corner middle chain.
      refine ⟨⟨wLayers H r U V, prod_wLayers_ge2 H r U V hr hL2 B hUV, ?_⟩⟩
      rintro ⟨sv, hsvlt⟩
      have hk : sv + 1 < L + 1 := by omega
      rcases Nat.eq_zero_or_pos sv with hs0 | hspos
      · -- layer 0: rank (U · [I_r|0]) = rank U = r.
        subst hs0
        rw [rank_heq (wLayers H r U V ⟨0, hsvlt⟩) (U * projM r (H ⟨0 + 1, hk⟩))
          rfl rfl (heq_layer0 H r U V hk)]
        rw [rank_mul_projM r (H ⟨0 + 1, hk⟩) (hr _), hUr]
      · rcases Nat.lt_or_ge sv (L - 1) with hslt | hsge
        · -- middle layer: corner block, rank r.
          rw [rank_heq (wLayers H r U V ⟨sv, hsvlt⟩)
            (corM r (H ⟨sv, Nat.lt_of_succ_lt hk⟩) (H ⟨sv + 1, hk⟩))
            rfl rfl (heq_layerMid H r U V sv hk hspos hslt)]
          exact corM_rank (hr _) (hr _)
        · -- last layer (sv = L-1): rank ([I_r;0] · V) = rank V = r.
          have hsL : sv = L - 1 := by omega
          rw [rank_heq (wLayers H r U V ⟨sv, hsvlt⟩) (embM (H ⟨sv, Nat.lt_of_succ_lt hk⟩) r * V)
            rfl (congrArg H (show (⟨sv, hsvlt⟩ : Fin L).succ = Fin.last L from
              Fin.ext (by simp [Fin.succ]; omega)))
            (heq_layerLast H r U V sv hk hsL hspos)]
          rw [rank_embM_mul (H ⟨sv, Nat.lt_of_succ_lt hk⟩) r (hr _), hVr]

/-- **The deepest singular point** of the fibre `mult⁻¹(B)` (Rung-0c FLAG, load-bearing — pp + Codex
adjudicated). A **single constructed** witness: every layer at the minimal rank `r` (the
block-normal rank-`r` chain; `r = 0` ⟹ the origin), residual core `0`. Aoyagi's point. **Why a
constructed point, not a `∀`-predicate** (lessons 2026-06-20): per-partial-product rank-`r` is *too
weak* (reintroduces L2's over-claim — `(2,2,2)`, `(A¹=0, A² invertible)` has all partial products
rank `0` but local RLCT `2 ≠ 3/2`); per-layer rank-exactly-`r` (`IsDeepLayers`) is *sufficient* (a
single GL gauge orbit, RLCT constant) but *not exhaustive* of the λ-attaining set. Keying D1/L2 to
ONE constructed witness gives the lowest proof surface with zero over-claim and no gauge/orbit
lemma. -/
noncomputable def deepestPoint (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : Params H :=
  (Classical.choice (deepestPoint_exists H r B hB hr hL)).1

/-- The constructed `deepestPoint` is a deepest-layers point (in particular, in the fibre). -/
theorem deepestPoint_isDeep (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    IsDeepLayers H r B (deepestPoint H r B hB hr hL) :=
  (Classical.choice (deepestPoint_exists H r B hB hr hL)).2

/-- **L2 (Theorem 3, product reduction).** The local RLCT of the loss **at the deepest point**
as the regular-part shift `[−r²+r(H¹+Hᴸ⁺¹)]/2` plus the singular-core `lambdaCore` over the reduced
widths `M⁽ˢ⁾ = H⁽ˢ⁾ − r`: it equals `aoyagiLambda H r` (cast to `ℝ≥0∞`). (Rung-0c FLAG: keyed to the
single constructed `deepestPoint`, **not** `∀ optimal w` — an over-claim — nor a
`∀`-deepest-predicate — the per-partial-product form was too weak. The local RLCT varies over the
fibre, equalling the closed form at the deepest point.) Non-vacuous: equates the local RLCT at
`deepestPoint` to the closed form. -/
theorem product_reduction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) = ENNReal.ofReal (aoyagiLambda H r) := by
  sorry

/-! ## D1 — reduction to the deepest singular point (Aoyagi 2013, Thm 4; design-spec §7.2) -/

/-- **D1 (Theorem 4).** The global infimum of the local RLCT over the optimal set is **attained at
the deepest singular point** `deepestPoint H r B` (Aoyagi 2013 Thm 2, the monotonicity of the local
RLCT over the fibre). This turns `⨅ w ∈ optimalSet, rlctAt` into the local RLCT at the
one constructed point that L2 evaluates. (Rung-0c FLAG: keyed to the constructed `deepestPoint`,
replacing the under-claiming `∃ wstar ∈ optimalSet` that did not name the attainer.) Non-vacuous:
equates the inf to the local RLCT at `deepestPoint`. **Proof state:** the `≤` direction is PROVEN
(`deepestPoint ∈ optimalSet` ⟹ `iInf₂_le`); the `≥` direction is reduced to the per-point obligation
`rlctAt deepest ≤ rlctAt v` for every optimal `v` (Aoyagi 2013 Thm 2) — the `sorry`. That residual
is L2-gated: its engine is `rlctAt_mono`, but applying it needs the loss-domination of the
HOMOGENEOUS core (the raw `dlnLoss B`, `B≠0`, is not homogeneous), available after the L2 form. -/
theorem deepest_point_reduction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (⨅ v ∈ optimalSet H B, rlctAt H (dlnLoss H B) v)
      = rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) := by
  -- `deepestPoint` is in the fibre (`IsDeepLayers.1`), so the `≤` direction is `iInf₂_le` — PROVEN.
  have hmem : deepestPoint H r B hB hr hL ∈ optimalSet H B :=
    (deepestPoint_isDeep H r B hB hr hL).1
  refine le_antisymm (iInf₂_le (deepestPoint H r B hB hr hL) hmem) ?_
  -- `≥` direction = Aoyagi 2013 Thm 2: the local RLCT at the deepest point is ≤ that at every other
  -- fibre point. The engine is `rlctAt_mono`, but applying it needs the loss-domination near the
  -- deepest point of the HOMOGENEOUS core (raw `dlnLoss B`, `B≠0`, is not homogeneous — thread-04):
  -- that domination is L2-downstream (the homogeneous normal form). Residual obligation, L2-gated.
  refine le_iInf₂ (fun v _ => ?_)
  sorry

/-! ## R1 — the resolution: explicit charts → normal-crossing form (the mountain; design-spec §8) -/

/-- **R1 (the resolution — CORE form).** Aoyagi's recursive blow-up as explicit coordinate charts: a
finite chart family with monomial pullback `core∘φᵢ = unitᵢ·∏|uⱼ|^{2k_{i,j}}` and Jacobian-monomial
`|det Dφᵢ| = posᵢ·∏|uⱼ|^{h_{i,j}}`, whose images cover a nbhd of `0 ∩ {core=0}`, whose monomial
thresholds reconstruct the core RLCT. **The value-match:** the chart family `(ι,d,k,h)` reconstructs
`rlctAtOn(core) 0`; the chart exponents realise `½·min_t Mval(t)`. This is **NOT** a chart↔`Adm`
bijection — the charts (pivot branches × affine-minor choices) outnumber the `Adm` vectors / strata;
the match is purely the VALUE. That value `⨅ monomialThreshold = ofReal(lambdaCore M)` is **A1's**
job (S2 `monomial_rlct` + `lambdaCore_eq_clean`), kept separate from this chart fact.

**Scoped to the CORE** (14th-finding re-scope, pp): the prior full-loss form
`rlctAt(dlnLoss B) wstar = ⨅ monomialThreshold` was FALSE for `r > 0` (the regular shift `n/2` is
ADDITIVE via Fubini, a SUM, not a `min`). R1 is about the singular core `‖∏C‖² = dlnLoss M 0` on the
reduced widths `M = H − r`, at its deepest point (the origin `0 : Params M`); the `n/2` regular term
enters in `product_reduction` via `S1Fubini`, not here. The core is the polynomial R1 is actually
applied to: analyticity automatic, statement `Params`-norm-free. -/
theorem resolution_charts (M : Fin (L + 1) → ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
      rlctAtOn (fun A : Params M =>
          dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A) (fun _ => 0 : Params M)
        = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
  sorry

/-! ## A1 / A2 — the arithmetic minimisation + the order count (design-spec §8) -/

/-- The balanced ℓ-split of `P`: `(P mod ℓ)` parts equal to `⌈P/ℓ⌉ = P/ℓ+1`, the rest
`⌊P/ℓ⌋ = P/ℓ`. -/
def balancedSplit (P ℓ : ℕ) (i : Fin ℓ) : ℕ :=
  if i.val < P % ℓ then P / ℓ + 1 else P / ℓ

/-- The clean core form `¼(Σ qᵢ² − Σ mₖ²)` over ℚ: `m : Fin (ℓ+1) → ℕ` the ℓ+1 chosen widths, `q`
the balanced ℓ-split of `P = Σ mₖ` (design-spec §4.3). -/
def cleanCore (ℓ : ℕ) (m : Fin (ℓ + 1) → ℕ) : ℚ :=
  let P := ∑ k, m k
  (1 / 4 : ℚ) * ((∑ i : Fin ℓ, (balancedSplit P ℓ i : ℚ) ^ 2)
    - (∑ k : Fin (ℓ + 1), (m k : ℚ) ^ 2))

/-- The printed Theorem-2 core expression `a(ℓ−a)/(4ℓ) − [ℓ(ℓ−1)/4](P/ℓ)² + ½ Σ_{i<j} mᵢmⱼ`, with
`a = P − (⌈P/ℓ⌉−1)ℓ = P mod ℓ` (design-spec §4.4). -/
def printedCore (ℓ : ℕ) (m : Fin (ℓ + 1) → ℕ) : ℚ :=
  let P := ∑ k, m k
  let a := P % ℓ
  (a * (ℓ - a) : ℚ) / (4 * ℓ) - (ℓ * (ℓ - 1) : ℚ) / 4 * ((P : ℚ) / ℓ) ^ 2
    + (1 / 2 : ℚ) * ∑ i : Fin (ℓ + 1), ∑ j : Fin (ℓ + 1),
        if i < j then (m i * m j : ℚ) else 0

/-- `T j ≤ tPrev M T j` on the admissible cone (weak-decrease, and `t⁽⁰⁾ = M⁽¹⁾ ≥ t⁽¹⁾`). -/
private theorem T_le_tPrev (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    (T j : ℤ) ≤ tPrev M T j := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨hbound, hdec, _⟩ := hT.2
  unfold tPrev
  split
  · rename_i h0
    have hb : T j ≤ admBound M j := hbound j
    rw [admBound, if_pos h0] at hb
    exact_mod_cast le_trans hb (min_le_left _ _)
  · have hle : (⟨j.val - 1, by omega⟩ : Fin L) ≤ j := by simp only [Fin.le_def]; omega
    exact_mod_cast hdec _ _ hle

/-- `T j ≤ M⁽ʲ⁺¹⁾` on the admissible cone (the block bound). -/
private theorem T_le_Msucc (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    (T j : ℤ) ≤ (M j.succ : ℤ) := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨hbound, _, _⟩ := hT.2
  have hb : T j ≤ admBound M j := hbound j
  unfold admBound at hb
  split at hb
  · rename_i h0
    have hle : T j ≤ M 1 := le_trans hb (min_le_right _ _)
    have hL : 0 < L := j.pos
    have hsucc : j.succ = (1 : Fin (L + 1)) := by
      apply Fin.ext; rw [Fin.val_succ, h0, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rw [hsucc]; exact_mod_cast hle
  · exact_mod_cast hb

/-- `Mval ≥ 0` on the admissible cone: each summand is a product of two nonnegative factors. -/
private theorem Mval_nonneg (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    0 ≤ Mval M T := by
  unfold Mval
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (by linarith [T_le_tPrev M T hT j]) (by linarith [T_le_Msucc M T hT j])

/-- `sortedSmallest M c` (for `c ≤ L`): the `c+1` smallest entries of `M : Fin (L+1) → ℕ`, as a
function `Fin (c+1) → ℕ`, via the ascending sort `Tuple.sort` and the first `c+1` indices. The `m`
argument of `cleanCore` is **pinned** to this (a function of `M`), making A1 the genuine Lemma 3. -/
def sortedSmallest (M : Fin (L + 1) → ℕ) (c : ℕ) (hc : c ≤ L) (k : Fin (c + 1)) : ℕ :=
  M (Tuple.sort M (Fin.castLE (by omega) k))

/-- `cleanCore` depends only on the **multiset** of `m`: permuting `m` leaves it fixed
(it is built from `∑ m` and `∑ m²`, both permutation-invariant). The crux that lets the genuine A1
proof stay local to the achiever — matching `cleanCore` at the minimiser's breakpoint widths to
`cleanCore (sortedSmallest …)` needs only that the two are the same *multiset*, not a global
permutation-transport of the admissible cone. -/
theorem cleanCore_perm (c : ℕ) (m : Fin (c + 1) → ℕ) (σ : Equiv.Perm (Fin (c + 1))) :
    cleanCore c (m ∘ σ) = cleanCore c m := by
  simp only [cleanCore]
  have hsum : (∑ k, (m ∘ σ) k) = ∑ k, m k := Equiv.sum_comp σ m
  have hsq : (∑ k, ((m ∘ σ) k : ℚ) ^ 2) = ∑ k, (m k : ℚ) ^ 2 := by
    have := Equiv.sum_comp σ (fun k => (m k : ℚ) ^ 2); simpa using this
  rw [hsum, hsq]

/-- The strict-descent positions of `T ∈ Adm M`: indices `j` where `u_j > u_{j+1}` (`u = M⁰ ∷ T`),
i.e. `T j < tPrev M T j`. The `Mval` sum collapses to these (the gap factor is `0` elsewhere). -/
noncomputable def descentSet (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Finset (Fin L) :=
  Finset.univ.filter (fun j => (T j : ℤ) < tPrev M T j)

/-- **#19 step-2 entry: `Mval` collapses to the strict descents.** For `T ∈ Adm M`, `Mval M T` sums
over only its `descentSet` (at a non-descent index `tPrev = T j` by admissibility, so the gap factor
`tPrev − T j` is `0`). The reparametrisation that feeds the per-T lower bound. -/
theorem Mval_descent (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    Mval M T = ∑ j ∈ descentSet M T, (tPrev M T j - (T j : ℤ)) * ((M j.succ : ℤ) - (T j : ℤ)) := by
  unfold Mval
  rw [descentSet]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _ hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
  have hge : (T j : ℤ) ≤ tPrev M T j := T_le_tPrev M T hT j
  have hz : tPrev M T j - (T j : ℤ) = 0 := by omega
  rw [hz, zero_mul]

/-- **Karamata for squares (ascending-prefix form, over ℤ).** If `y` is monotone on `[0,n)`, `x` and
`y` have equal total over `range n`, and every prefix sum of `x` is `≤` that of `y`, then
`∑ y² ≤ ∑ x²`. The convexity lower-bound engine: `x²−y² ≥ 2y(x−y)`, and `∑ y(x−y) ≥ 0` by
summation-by-parts (`Finset.sum_range_by_parts`) from prefix-domination + monotonicity. -/
private theorem karamata_sq (n : ℕ) (x y : ℕ → ℤ)
    (hmono : ∀ i, i + 1 < n → y i ≤ y (i + 1))
    (htot : ∑ i ∈ Finset.range n, x i = ∑ i ∈ Finset.range n, y i)
    (hpre : ∀ k, k ≤ n → ∑ i ∈ Finset.range k, x i ≤ ∑ i ∈ Finset.range k, y i) :
    ∑ i ∈ Finset.range n, y i ^ 2 ≤ ∑ i ∈ Finset.range n, x i ^ 2 := by
  have key : 0 ≤ ∑ i ∈ Finset.range n, y i * (x i - y i) := by
    set d : ℕ → ℤ := fun i => x i - y i with hd
    have hsumd : ∀ k, k ≤ n → ∑ i ∈ Finset.range k, d i ≤ 0 := by
      intro k hk; simp only [hd, Finset.sum_sub_distrib]; linarith [hpre k hk]
    have habel := Finset.sum_range_by_parts (fun i => y i) (fun i => d i) n
    simp only [smul_eq_mul] at habel
    rw [habel]
    have e1 : ∑ i ∈ Finset.range n, d i = 0 := by
      simp only [hd, Finset.sum_sub_distrib]; rw [htot]; ring
    rw [e1, mul_zero, zero_sub, neg_nonneg]
    apply Finset.sum_nonpos
    intro i hi
    rw [Finset.mem_range] at hi
    have hy : 0 ≤ y (i + 1) - y i := by linarith [hmono i (by omega)]
    exact mul_nonpos_of_nonneg_of_nonpos hy (hsumd (i + 1) (by omega))
  have hpt : ∀ i ∈ Finset.range n, y i ^ 2 + 2 * (y i * (x i - y i)) ≤ x i ^ 2 := by
    intro i _; nlinarith [sq_nonneg (x i - y i)]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  linarith [hsum, key]

/-! ### A1 keystone: the edge-variable transform (fixed `Fin L` index, no descent reindexing).

Route (verified exhaustively, fm rung0-defs + Codex xhigh): map every admissible `T` to a
fixed-length edge vector `q_j = M_{j+1} + (u_j − u_{j+1})` (`u` the level sequence `[M⁰,T⁰,…]`).
Then `2·Mval = ∑ q² − ∑ M²` (CERTAIN algebra), and the admissible cone maps onto the
prefix-constrained polytope `QFeasible`. The minimum of `∑ q²` over it is the balanced split of the
`c+1` smallest widths' total plus the squares of the `L−c` largest — matched to `cleanCore` via
`balancedSplit_sq_int` + `cleanCore_perm`. The lower bound is `karamata_sq`; the achiever is the
explicit balanced-split placement. -/

/-- The level sequence `u : ℕ → ℤ`, `u 0 = M⁰`, `u (i+1) = Tⁱ` (and `0` past `L`). Total `ℕ→ℤ` to
avoid `Fin` casts in the `range`-sum algebra. -/
noncomputable def Useq (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (i : ℕ) : ℤ :=
  if i = 0 then (M 0 : ℤ) else if h : i - 1 < L then (T ⟨i - 1, h⟩ : ℤ) else 0

/-- The width sequence `Mseq i = M⁽ⁱ⁾` as `ℕ → ℤ` (`0` past `L`), for `range`-sum algebra. -/
noncomputable def Mseq (M : Fin (L + 1) → ℕ) (i : ℕ) : ℤ :=
  if h : i < L + 1 then (M ⟨i, h⟩ : ℤ) else 0

/-- The fixed-length edge vector `q_j = M⁽ʲ⁺¹⁾ + (u_j − u_{j+1})`, `j ∈ range L` (`ℕ → ℤ`). -/
noncomputable def edgeQ (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : ℕ) : ℤ :=
  Mseq M (j + 1) + Useq M T j - Useq M T (j + 1)

private theorem Useq_zero (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Useq M T 0 = (M 0 : ℤ) := rfl

private theorem tPrev_eq_Useq (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) :
    tPrev M T j = Useq M T j.val := by
  unfold tPrev Useq; split
  · rfl
  · rw [dif_pos (show j.val - 1 < L by omega)]

private theorem Tj_eq_Useq (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) :
    (T j : ℤ) = Useq M T (j.val + 1) := by
  unfold Useq; rw [if_neg (by omega), dif_pos (show (j.val + 1) - 1 < L by omega)]; norm_num

private theorem Msucc_eq_Mseq (M : Fin (L + 1) → ℕ) (j : Fin L) :
    (M j.succ : ℤ) = Mseq M (j.val + 1) := by
  unfold Mseq; rw [dif_pos (show j.val + 1 < L + 1 by omega)]; rfl

/-- `Useq` past `L` is `0` when the last exponent vanishes (`T⁽ᴸ⁻¹⁾ = 0`, from admissibility). -/
private theorem Useq_last (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hL : 1 ≤ L)
    (hlast : ∀ j : Fin L, j.val = L - 1 → T j = 0) : Useq M T L = 0 := by
  unfold Useq
  rw [if_neg (by omega), dif_pos (show L - 1 < L by omega)]
  have : T ⟨L - 1, by omega⟩ = 0 := hlast _ rfl
  rw [this]; rfl

/-- `Mval M T` as a `range L` sum in the level sequence. -/
private theorem Mval_eq_range (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) :
    Mval M T = ∑ j ∈ Finset.range L,
      (Useq M T j - Useq M T (j + 1)) * (Mseq M (j + 1) - Useq M T (j + 1)) := by
  unfold Mval
  rw [Finset.sum_range fun j =>
    (Useq M T j - Useq M T (j + 1)) * (Mseq M (j + 1) - Useq M T (j + 1))]
  apply Finset.sum_congr rfl
  intro j _
  rw [tPrev_eq_Useq, Tj_eq_Useq, Msucc_eq_Mseq]

/-- **Edge identity (certain algebra).** `2·Mval M T = ∑_{j<L}(edgeQ j)² − ∑_{i<L+1}(M⁽ⁱ⁾)²`
(level sequence from `M⁰` to `0`, admissibility). The transform sending the admissible cone to a
fixed `Fin L` edge polytope. -/
private theorem edge_identity (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hL : 1 ≤ L)
    (hlast : ∀ j : Fin L, j.val = L - 1 → T j = 0) :
    2 * Mval M T = (∑ j ∈ Finset.range L, edgeQ M T j ^ 2)
      - ∑ i ∈ Finset.range (L + 1), Mseq M i ^ 2 := by
  rw [Mval_eq_range, Finset.mul_sum]
  -- per-term: 2*(u_j - u_{j+1})(M_{j+1} - u_{j+1}) = edgeQ_j^2 - M_{j+1}^2 - (u_j^2 - u_{j+1}^2)
  have hterm : ∀ j ∈ Finset.range L,
      2 * ((Useq M T j - Useq M T (j + 1)) * (Mseq M (j + 1) - Useq M T (j + 1)))
        = edgeQ M T j ^ 2 - Mseq M (j + 1) ^ 2
          - (Useq M T j ^ 2 - Useq M T (j + 1) ^ 2) := by
    intro j _; unfold edgeQ; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  -- ∑_{j<L} M_{j+1}^2 = (∑_{i<L+1} M_i^2) - M_0^2
  have hM : ∑ j ∈ Finset.range L, Mseq M (j + 1) ^ 2
      = (∑ i ∈ Finset.range (L + 1), Mseq M i ^ 2) - Mseq M 0 ^ 2 := by
    rw [Finset.sum_range_succ' (fun i => Mseq M i ^ 2) L]; ring
  -- ∑_{j<L} (u_j^2 - u_{j+1}^2) = u_0^2 - u_L^2 = M_0^2 - 0
  have hU : ∑ j ∈ Finset.range L, (Useq M T j ^ 2 - Useq M T (j + 1) ^ 2)
      = Useq M T 0 ^ 2 - Useq M T L ^ 2 :=
    Finset.sum_range_sub' (fun i => Useq M T i ^ 2) L
  rw [hM, hU, Useq_zero, Useq_last M T hL hlast]
  have hM0 : Mseq M 0 = (M 0 : ℤ) := by unfold Mseq; rw [dif_pos (by omega)]; rfl
  rw [hM0]; ring

/-- `Useq` at a positive index is the corresponding `T` entry. -/
private theorem Useq_pos (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (i : ℕ) (hi : i - 1 < L)
    (hi0 : i ≠ 0) : Useq M T i = (T ⟨i - 1, hi⟩ : ℤ) := by
  unfold Useq; rw [if_neg hi0, dif_pos hi]

/-- The level sequence is antitone on `[0, L]` (admissibility weak-decrease + index-0 bound). -/
private theorem Useq_antitone (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    ∀ i, i + 1 ≤ L → Useq M T (i + 1) ≤ Useq M T i := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨hbound, hdec, _⟩ := hT.2
  intro i hi
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    rw [Useq_pos M T 1 (by omega) (by omega), Useq_zero]
    have hb := hbound ⟨0, by omega⟩
    unfold admBound at hb; rw [if_pos rfl] at hb
    have h0 : T ⟨0, by omega⟩ ≤ M 0 := le_trans hb (min_le_left _ _)
    simpa using (by exact_mod_cast h0 : (T ⟨1 - 1, by omega⟩ : ℤ) ≤ (M 0 : ℤ))
  · rw [Useq_pos M T (i + 1) (by omega) (by omega), Useq_pos M T i (by omega) (by omega)]
    have hle : (⟨i - 1, by omega⟩ : Fin L) ≤ ⟨i + 1 - 1, by omega⟩ := by
      simp only [Fin.le_def]; omega
    exact_mod_cast hdec ⟨i - 1, by omega⟩ ⟨i + 1 - 1, by omega⟩ hle

/-- The level sequence is nonnegative. -/
private theorem Useq_nonneg (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (i : ℕ) : 0 ≤ Useq M T i := by
  unfold Useq; split
  · positivity
  · split
    · positivity
    · rfl

/-- The block bound `admBound j ≤ M⁽ʲ⁺¹⁾` (the index-0 `min(M⁰,M¹) ≤ M¹`). -/
private theorem admBound_le_Msucc (M : Fin (L + 1) → ℕ) (j : Fin L) : admBound M j ≤ M j.succ := by
  unfold admBound; split
  · rename_i h0
    have hs : j.succ = (1 : Fin (L + 1)) := by
      apply Fin.ext; rw [Fin.val_succ, h0, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rw [hs]; exact min_le_right _ _
  · exact le_refl _

/-- The level sequence is bounded by the widths: `u_i ≤ M⁽ⁱ⁾` (the block bound). -/
private theorem Useq_le_M (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (i : ℕ)
    (hi : i < L + 1) : Useq M T i ≤ Mseq M i := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨hbound, _, _⟩ := hT.2
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0; rw [Useq_zero]; unfold Mseq; rw [dif_pos (by omega)]; norm_num
  · rw [Useq_pos M T i (by omega) (by omega)]
    unfold Mseq; rw [dif_pos hi]
    have hb := hbound ⟨i - 1, by omega⟩
    have hbm := admBound_le_Msucc M ⟨i - 1, by omega⟩
    have hsucc : (⟨i - 1, by omega⟩ : Fin L).succ = (⟨i, hi⟩ : Fin (L + 1)) := by
      apply Fin.ext; simp [Fin.succ]; omega
    rw [hsucc] at hbm
    exact_mod_cast le_trans hb hbm

/-- The edge vector's prefix sum telescopes: `∑_{j<n} q_j = (∑_{i<n+1} M⁽ⁱ⁾) − M⁰ + (M⁰ − u_n)`. -/
private theorem prefix_edgeQ (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (n : ℕ) :
    ∑ j ∈ Finset.range n, edgeQ M T j
      = (∑ i ∈ Finset.range (n + 1), Mseq M i) - Mseq M 0 + (Useq M T 0 - Useq M T n) := by
  unfold edgeQ
  rw [show (fun j => Mseq M (j + 1) + Useq M T j - Useq M T (j + 1))
        = (fun j => Mseq M (j + 1) + (Useq M T j - Useq M T (j + 1))) from by funext j; ring,
      Finset.sum_add_distrib, Finset.sum_range_sub' (fun i => Useq M T i) n]
  congr 1
  rw [Finset.sum_range_succ' (fun i => Mseq M i) n]; ring

/-! ### A1 (`lambdaCore_eq_clean`) route notes (the theorem itself is built at the end of the file).

**A1 (Lemma 3, the genuine clean closed form; pp statement card, candidate (d)).** The core
`lambdaCore M = ½·min_T M(T)` equals `cleanCore c (sortedSmallest M c)` for an **achiever**
`c ∈ {1,…,L}` — the `m` argument is **pinned** to `M`'s `c+1` smallest reduced widths (a function of
`M`, not a free choice), so this is the faithful Aoyagi Lemma 3 (`min_{T∈Adm} M(T) = clean form at
the smallest widths), NOT the weak existential. Verified total 1360/1360 (pp). It is **NOT** an
extremum over `c` — both `min_c` and `max_c` are refuted (`M=[1,1,4]`, `[2,2,2]`); the `∃ c` is the
achiever (the `c` whose balanced split on the smallest widths is `Adm`-admissible).

**Verified route (re-derived + numerically pinned, fm rung0-defs).** Write `a` for the entries of
`M` sorted ascending (`a k = sortedSmallest M L`'s prefix). For `1 ≤ c ≤ L` put
`Φ c = 2·cleanCore c (a₀,…,a_c)` (so `lambdaCore M = ½·minMval`, and the target is
`minMval M = Φ c*`). The achiever is `c* = the largest c ∈ {1,…,L}` satisfying the **cumulative
ceiling** predicate `good c := ∀ 1 ≤ i ≤ c, aᵢ ≤ ⌈Sᵢ/i⌉` where `Sᵢ = a₀+⋯+aᵢ` — equivalently in ℕ
`i·aᵢ ≤ Sᵢ + i − 1` (`c = 1` is always good, so `c*` exists; verified `lambdaCore = cleanCore c*`
over **all** `M` with widths `0..3`, `L ≤ 4`, zero failures). NOTE the prior route line ("per-`c`
lower bound", `min_c`) was the *wrong* (refuted) framing, and Codex's single-`a_c ≤ ⌈S_c/c⌉` test is
also wrong (278/3900 fail — needs the **cumulative** ∀i≤c); both corrected here.

**VERIFIED TURNKEY ROUTE (fm rung0-defs; the descent reindex is REPLACED by a fixed-`Fin L` edge
transform — no `Fin c_T`).** Engines now BANKED green in-file:
- `edge_identity`: `2·Mval M T = ∑_{j<L} (edgeQ M T j)² − ∑_{i<L+1} (Mseq M i)²`, the fixed-length
  transform `q_j = M⁽ʲ⁺¹⁾ + u_j − u_{j+1}` (CERTAIN algebra; `Useq`/`Mseq`/`edgeQ` defs above).
- `karamata_sq`: ascending-prefix majorization ⟹ `∑ y² ≤ ∑ x²` (Abel summation). The convexity LB.
- `Useq_antitone`, `Useq_nonneg`, `Useq_le_M`, `admBound_le_Msucc`, `prefix_edgeQ`: give that the
  edge vector of any `T ∈ Adm M` is `QFeasible` — `q_j ≥ M⁽ʲ⁺¹⁾`, total `= ∑M`, positional prefix
  `S_{n-1} ≤ ∑_{j<n} q_j ≤ S_n` (`S_n = M⁰+⋯+Mⁿ`). [Adm ↔ QFeasible bijection verified both ways.]
- `balancedSplit_min`/`balancedSplit_sq_int`: `∑β² = c·b²+a(2b+1)`, the balanced-split value.
- `cleanCore_perm`: `cleanCore` is multiset-only — matches the achiever's edge multiset `Y` to
  `sortedSmallest M c`.

Achiever `c* = largest c∈{1..L}` with cumulative `good c := ∀1≤i≤c, i·aᵢ ≤ Sᵢ+i−1` (`a = sort M`
ascending; `c=1` always good). Target edge multiset `Y = {β₀…β_{c*−1}} ∪ {a_{c*+1}…a_L}`,
`β = balancedSplit P_{c*} c*`, `P_{c*} = ∑_{i≤c*} aᵢ`. Then `minMval = ∑Y² − ∑M²` and
`2·cleanCore c* (sortedSmallest M c*) = ∑Y² − ∑M²` (arithmetic via `balancedSplit_sq_int`).

**THE ONE REMAINING GATE (the genuine hard core; ~150-250 lines of from-scratch combinatorics).**
Lower bound `∑Y² ≤ ∑_{j<L} (edgeQ M T j)²` for every `T ∈ Adm M`. To feed `karamata_sq` one must
sort the (positional) edge vector and show the SMALLEST-`k`-sum majorization
`∀k, ∑(k smallest of edgeQ) ≤ ∑(k smallest of Y)` from the positional QFeasible bounds. This is a
combinatorial majorization Mathlib LACKS (no Karamata/Schur-convexity, no "sum of k smallest" API at
v4.29). Pointwise-after-sorting is FALSE (`q=[1,3]` vs `Y=[2,2]`) and a prefix/tail two-part split
provably undershoots (the leaked prefix mass lands on a strictly larger tail slot — convexity is
irreducible), so the global smallest-`k`-sum majorization is mandatory. Upper bound (achiever) needs
the same order-reconciliation: an explicit `T* ∈ Adm M` (greedy placement of `Y`, or first prove
`lambdaCore M = lambdaCore (sort M)`) with `Mval M T* = ½(∑Y² − ∑M²)`, then `Finset.inf'_le`. All
sub-claims numerically verified 0-failure (L≤4); the gate is purely the Lean majorization build.
The proof is built at the end of the file, after the `balancedSplit_*` arithmetic engines used. -/

/-- The balanced-split sum of squares: `∑ᵢ qᵢ² = (P%ℓ)(P/ℓ+1)² + (ℓ−P%ℓ)(P/ℓ)²` (nat-division
casts). The `a` parts of `⌈P/ℓ⌉` and `ℓ−a` parts of `⌊P/ℓ⌋`, where `a = P%ℓ`. -/
private theorem balancedSplit_sq (P ℓ : ℕ) (hℓ : 0 < ℓ) :
    (∑ i : Fin ℓ, (balancedSplit P ℓ i : ℚ) ^ 2)
      = ((P % ℓ : ℕ) : ℚ) * (((P / ℓ : ℕ) : ℚ) + 1) ^ 2
        + ((ℓ : ℚ) - ((P % ℓ : ℕ) : ℚ)) * ((P / ℓ : ℕ) : ℚ) ^ 2 := by
  have hmod : P % ℓ ≤ ℓ := le_of_lt (Nat.mod_lt _ hℓ)
  have hcard : (Finset.univ.filter (fun i : Fin ℓ => (i : ℕ) < P % ℓ)).card = P % ℓ := by
    have := @Fin.card_filter_val_lt ℓ (P % ℓ)
    rw [this]; omega
  rw [show (∑ i : Fin ℓ, (balancedSplit P ℓ i : ℚ) ^ 2)
        = ∑ i : Fin ℓ, (if (i : ℕ) < P % ℓ then ((P / ℓ + 1 : ℕ) : ℚ) ^ 2
            else ((P / ℓ : ℕ) : ℚ) ^ 2) from ?_]
  · rw [Finset.sum_ite]; simp only [Finset.sum_const, nsmul_eq_mul]; rw [hcard]
    have hcompl : (Finset.univ.filter (fun i : Fin ℓ => ¬ (i : ℕ) < P % ℓ)).card = ℓ - P % ℓ := by
      have := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin ℓ)))
        (p := fun i : Fin ℓ => (i : ℕ) < P % ℓ)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      rw [hcard] at this; omega
    rw [hcompl]; push_cast [Nat.cast_sub hmod]; ring
  · apply Finset.sum_congr rfl
    intro i _; unfold balancedSplit; split <;> push_cast <;> ring

/-- The balanced-split sum of squares as a closed integer expression `ℓ·b² + a·(2b+1)` with
`b = P/ℓ`, `a = P%ℓ`. (ℤ companion of `balancedSplit_sq`, used by `balancedSplit_min`.) -/
private theorem balancedSplit_sq_int (P ℓ : ℕ) (hℓ : 0 < ℓ) :
    (∑ i : Fin ℓ, ((balancedSplit P ℓ i : ℕ) : ℤ) ^ 2)
      = (ℓ : ℤ) * ((P / ℓ : ℕ) : ℤ) ^ 2
        + ((P % ℓ : ℕ) : ℤ) * (2 * ((P / ℓ : ℕ) : ℤ) + 1) := by
  have hmod : P % ℓ ≤ ℓ := le_of_lt (Nat.mod_lt _ hℓ)
  have hcard : (Finset.univ.filter (fun i : Fin ℓ => (i : ℕ) < P % ℓ)).card = P % ℓ := by
    have := @Fin.card_filter_val_lt ℓ (P % ℓ); rw [this]; omega
  rw [show (∑ i : Fin ℓ, ((balancedSplit P ℓ i : ℕ) : ℤ) ^ 2)
        = ∑ i : Fin ℓ, (if (i : ℕ) < P % ℓ then ((P / ℓ + 1 : ℕ) : ℤ) ^ 2
            else ((P / ℓ : ℕ) : ℤ) ^ 2) from ?_]
  · rw [Finset.sum_ite]; simp only [Finset.sum_const, nsmul_eq_mul]; rw [hcard]
    have hcompl : (Finset.univ.filter (fun i : Fin ℓ => ¬ (i : ℕ) < P % ℓ)).card = ℓ - P % ℓ := by
      have := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin ℓ)))
        (p := fun i : Fin ℓ => (i : ℕ) < P % ℓ)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      rw [hcard] at this; omega
    rw [hcompl]; push_cast [Nat.cast_sub hmod]; ring
  · apply Finset.sum_congr rfl
    intro i _; unfold balancedSplit; split <;> push_cast <;> ring

/-- **A1 Step 1 (balanced-split minimises `Σq²`).** Among integer vectors `q : Fin ℓ → ℕ` of fixed
sum `P`, the balanced ℓ-split minimises `∑ qᵢ²`. The proof is elementary: with `b = P/ℓ`, the
deficit `∑qᵢ² − ∑balancedᵢ² = ∑(qᵢ−b)² − (P%ℓ)`, and `∑(qᵢ−b) = P%ℓ`, so the claim reduces to
`∑(qᵢ−b)² ≥ ∑(qᵢ−b)` — true since `d² ≥ d` for every integer `d`. The lower-bound engine for A1. -/
theorem balancedSplit_min (P ℓ : ℕ) (hℓ : 0 < ℓ) (q : Fin ℓ → ℕ) (hq : ∑ i, q i = P) :
    (∑ i : Fin ℓ, ((balancedSplit P ℓ i : ℕ) : ℤ) ^ 2) ≤ ∑ i : Fin ℓ, ((q i : ℕ) : ℤ) ^ 2 := by
  set b : ℤ := ((P / ℓ : ℕ) : ℤ) with hb
  set a : ℤ := ((P % ℓ : ℕ) : ℤ) with ha
  have hP : (P : ℤ) = (ℓ : ℤ) * b + a := by
    rw [hb, ha]
    have := Nat.div_add_mod P ℓ
    omega
  have hsumq : ∑ i : Fin ℓ, ((q i : ℕ) : ℤ) = (P : ℤ) := by
    rw [← hq]; push_cast; ring
  -- ∑ (q i - b) = a
  have hsumd : ∑ i : Fin ℓ, (((q i : ℕ) : ℤ) - b) = a := by
    rw [Finset.sum_sub_distrib, hsumq, hP]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- ∑ (q i - b)² ≥ ∑ (q i - b) = a  (since d² ≥ d for every integer d)
  have hdsq : ∑ i : Fin ℓ, (((q i : ℕ) : ℤ) - b) ≤ ∑ i : Fin ℓ, (((q i : ℕ) : ℤ) - b) ^ 2 := by
    apply Finset.sum_le_sum; intro i _; nlinarith [sq_nonneg (((q i : ℕ) : ℤ) - b - 1)]
  -- expand ∑ (q i - b)² = ∑ q i² - 2 b P + ℓ b²
  have hexpand : ∑ i : Fin ℓ, (((q i : ℕ) : ℤ) - b) ^ 2
      = (∑ i : Fin ℓ, ((q i : ℕ) : ℤ) ^ 2) - 2 * b * (P : ℤ) + (ℓ : ℤ) * b ^ 2 := by
    have : ∀ i : Fin ℓ, (((q i : ℕ) : ℤ) - b) ^ 2
        = ((q i : ℕ) : ℤ) ^ 2 - 2 * b * ((q i : ℕ) : ℤ) + b ^ 2 := by intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [balancedSplit_sq_int P ℓ hℓ]
  rw [hsumd] at hdsq
  rw [hexpand] at hdsq
  -- now a ≤ ∑q² - 2bP + ℓb²  ⟹  ℓb² + a(2b+1) ≤ ∑q²  (using P = ℓb + a)
  rw [hP] at hdsq
  nlinarith [hdsq]

/-- Expanding `(∑ mₖ)²`: `(∑ mₖ)² = ∑ mₖ² + 2 ∑_{i<j} mᵢmⱼ` (the off-diagonal is symmetric). -/
private theorem sum_sq_eq (ℓ : ℕ) (m : Fin (ℓ + 1) → ℕ) :
    ((∑ k, (m k : ℚ))) ^ 2
      = (∑ k, (m k : ℚ) ^ 2)
        + 2 * (∑ i : Fin (ℓ + 1), ∑ j : Fin (ℓ + 1), if i < j then (m i * m j : ℚ) else 0) := by
  rw [sq, Finset.sum_mul_sum]
  have key : ∀ i : Fin (ℓ + 1), (∑ j, (m i : ℚ) * (m j))
      = (∑ j, if i < j then (m i * m j : ℚ) else 0)
        + (∑ j, if i = j then (m i * m j : ℚ) else 0)
        + (∑ j, if j < i then (m i * m j : ℚ) else 0) := by
    intro i; rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.2 (le_of_lt h), Fin.ne_of_lt h]
    · subst h; simp
    · simp [h, not_lt.2 (le_of_lt h), Fin.ne_of_gt h]
  have hdiag : ∀ i : Fin (ℓ + 1), (∑ j, if i = j then (m i * m j : ℚ) else 0) = (m i : ℚ) ^ 2 := by
    intro i; simp [Finset.sum_ite_eq, sq]
  simp_rw [key, hdiag]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hswap : (∑ i : Fin (ℓ + 1), ∑ j, if j < i then (m i * m j : ℚ) else 0)
             = (∑ i : Fin (ℓ + 1), ∑ j, if i < j then (m i * m j : ℚ) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    by_cases h : i < j <;> simp [h] <;> ring
  rw [hswap]; ring

/-- **A1 (clean = printed).** The clean core form equals the printed Theorem-2 expression — a finite
arithmetic identity in `m, ℓ` (`a = P mod ℓ`), holding for **every** `m` and every `ℓ > 0`. (Rung-0c
nit: the docstring formerly called this "Def-3 regime"-scoped, but the identity is **universal** in
`(m, ℓ)` with `0 < ℓ` — it does not depend on any Def-3 selection; rv-2 verified 9324 cases.
Docstring corrected.) Not part of the headline. Non-vacuous: it equates the two forms. -/
theorem clean_eq_printed (ℓ : ℕ) (m : Fin (ℓ + 1) → ℕ) (hℓ : 0 < ℓ) :
    cleanCore ℓ m = printedCore ℓ m := by
  simp only [cleanCore, printedCore]
  rw [balancedSplit_sq (∑ k, m k) ℓ hℓ]
  have hm := sum_sq_eq ℓ m
  set cross := ∑ i : Fin (ℓ + 1), ∑ j : Fin (ℓ + 1), if i < j then (m i * m j : ℚ) else 0
  have hsq : (∑ k, (m k : ℚ) ^ 2) = (∑ k, (m k : ℚ)) ^ 2 - 2 * cross := by linarith [hm]
  rw [hsq]
  set P := ∑ k, m k with hP
  have hsumP : (∑ k, (m k : ℚ)) = (P : ℚ) := by rw [hP]; push_cast; ring
  rw [hsumP]
  have hdm : P = ℓ * (P / ℓ) + P % ℓ := (Nat.div_add_mod P ℓ).symm
  have hℓQ : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  set b := P / ℓ
  set a := P % ℓ
  have hPQ : (P : ℚ) = (ℓ : ℚ) * (b : ℚ) + (a : ℚ) := by rw [hdm]; push_cast; ring
  rw [hPQ]; field_simp; ring

/-- **A2 (Lemmas 4–5, the order count).** The combinatorial chart-count identity: for the
resolution's weighted-monomial data `(d, k, h)` realising the deepest-point geometry, the
chart-count order `monomialOrder d k h` equals `aoyagiTheta ℓ a = a(ℓ−a)+1` for the Def-3 data
`(ℓ, a)` (design-spec §3, §9: θ is **not** the naive minimiser count). Stated existentially over the
realising data; the **secondary**, seam-flagged deliverable (standing decision 6). Non-vacuous: it
equates an explicit `monomialOrder` to `aoyagiTheta`. -/
theorem aoyagiTheta_eq (M : Fin (L + 1) → ℕ) :
    ∃ (ℓ a d : ℕ) (k h : Fin d → ℕ), monomialOrder d k h = aoyagiTheta ℓ a := by
  sorry

/-! ## T — the headline (the GOAL; design-spec §8) -/

/-- **T (Theorem 2, the headline).** The global learning coefficient — the infimum of the local RLCT
over the optimal set (fibre `mult⁻¹(B)`) — equals Aoyagi's closed form `aoyagiLambda H r`, for any
target `B` of rank `r` with every width `≥ r` (`hr`, the well-definedness + nonemptiness domain:
`hr` makes the reduced widths `M⁽ˢ⁾ = H⁽ˢ⁾ − r` non-truncating and the fibre nonempty, so the `⨅` is
not the degenerate `⊤` over an empty set). Assembled: D1 (→ deepest point) ▸ L2 (→ reg + core) ▸ R1
(→ charts) ▸ S2 (→ min ratio) ▸ A1 (→ clean form = `aoyagiLambda`). -/
theorem aoyagi_learning_coefficient (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  -- assemble: D1 (⨅ = rlctAt at the constructed deepestPoint) ▸ L2 (= closed form there).
  rw [deepest_point_reduction H r B hB hr hL]
  exact product_reduction H r B hB hr hL

/-! ## A1 (`lambdaCore_eq_clean`) — the genuine clean closed form, built here.

The route is in the `lambdaCore_eq_clean` docstring above. The hard core is a from-scratch Karamata
(majorization) inequality: Mathlib v4.29 has no Schur-convexity / "sum of `k` smallest" API. We
build the sorted-prefix-domination bridge to the `karamata_sq` engine, the `smallestK ≤ k-subset`
fact, the QFeasible-edge majorization, and the explicit achiever. -/

/-- The ascending-sorted sequence of `q : Fin n → ℤ` as a total `ℕ → ℤ` (padded `0` past `n`), built
from `Tuple.sort` so that prefix `range`-sums are sums of the `k` smallest entries. -/
noncomputable def srt (n : ℕ) (q : Fin n → ℤ) (i : ℕ) : ℤ :=
  if h : i < n then q (Tuple.sort q ⟨i, h⟩) else 0

/-- **Karamata via sort (the convexity lower bound, sorted form).** If `q, Y : Fin n → ℤ` have equal
total and every sorted prefix of `q` is `≤` the corresponding sorted prefix of `Y` (`Y` more
balanced), then `∑ Y² ≤ ∑ q²`. Bridges sorted-prefix domination to the `karamata_sq` engine. -/
private theorem sq_sum_le_of_sorted_prefix (n : ℕ) (q Y : Fin n → ℤ)
    (htot : ∑ i, q i = ∑ i, Y i)
    (hpre : ∀ k, k ≤ n → ∑ i ∈ Finset.range k, srt n q i ≤ ∑ i ∈ Finset.range k, srt n Y i) :
    ∑ i, (Y i) ^ 2 ≤ ∑ i, (q i) ^ 2 := by
  have hYsq : ∑ i ∈ Finset.range n, (srt n Y i) ^ 2 = ∑ i, (Y i) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (srt n Y i) ^ 2) n]
    rw [show (∑ i : Fin n, (srt n Y (i : ℕ)) ^ 2) = ∑ i : Fin n, (Y (Tuple.sort Y i)) ^ 2 from
      Finset.sum_congr rfl (fun i _ => by simp only [srt, dif_pos i.isLt])]
    exact Equiv.sum_comp (Tuple.sort Y) (fun i => (Y i) ^ 2)
  have hqsq : ∑ i ∈ Finset.range n, (srt n q i) ^ 2 = ∑ i, (q i) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (srt n q i) ^ 2) n]
    rw [show (∑ i : Fin n, (srt n q (i : ℕ)) ^ 2) = ∑ i : Fin n, (q (Tuple.sort q i)) ^ 2 from
      Finset.sum_congr rfl (fun i _ => by simp only [srt, dif_pos i.isLt])]
    exact Equiv.sum_comp (Tuple.sort q) (fun i => (q i) ^ 2)
  have htot' : ∑ i ∈ Finset.range n, srt n q i = ∑ i ∈ Finset.range n, srt n Y i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => srt n q i) n,
        ← Fin.sum_univ_eq_sum_range (fun i => srt n Y i) n]
    rw [show (∑ i : Fin n, srt n q (i : ℕ)) = ∑ i : Fin n, q (Tuple.sort q i) from
          Finset.sum_congr rfl (fun i _ => by simp only [srt, dif_pos i.isLt]),
        show (∑ i : Fin n, srt n Y (i : ℕ)) = ∑ i : Fin n, Y (Tuple.sort Y i) from
          Finset.sum_congr rfl (fun i _ => by simp only [srt, dif_pos i.isLt])]
    rw [Equiv.sum_comp (Tuple.sort q) q, Equiv.sum_comp (Tuple.sort Y) Y]; exact htot
  have hmono : ∀ i, i + 1 < n → srt n Y i ≤ srt n Y (i + 1) := by
    intro i hi
    simp only [srt, dif_pos (show i < n by omega), dif_pos hi]
    apply Tuple.monotone_sort Y; simp [Fin.le_def]
  have := karamata_sq n (srt n q) (srt n Y) hmono htot' hpre
  rw [hqsq, hYsq] at this; exact this

/-- **Subset-min (the `k`-smallest minimises among `k`-subsets).** If every entry of `B` is `≤` each
entry outside `B`, then `∑_B g ≤ ∑_A g` for any `A` of the same cardinality (swap `B∖A ↔ A∖B`). -/
private theorem sum_le_sum_of_compl_ge {m : ℕ} (g : Fin m → ℤ) (A B : Finset (Fin m))
    (hcard : A.card = B.card) (hval : ∀ j ∈ B, ∀ j' ∉ B, g j ≤ g j') :
    ∑ j ∈ B, g j ≤ ∑ j ∈ A, g j := by
  have hB : ∑ j ∈ B, g j = ∑ j ∈ B ∩ A, g j + ∑ j ∈ B \ A, g j := by
    rw [← Finset.sum_inter_add_sum_diff B A g]
  have hA : ∑ j ∈ A, g j = ∑ j ∈ A ∩ B, g j + ∑ j ∈ A \ B, g j := by
    rw [← Finset.sum_inter_add_sum_diff A B g]
  rw [hB, hA, Finset.inter_comm B A]
  have hcd : (B \ A).card = (A \ B).card := Finset.card_sdiff_comm hcard.symm
  obtain e := Finset.equivOfCardEq hcd
  have h1 : ∑ j ∈ B \ A, g j = ∑ x : ↥(B \ A), g (x : Fin m) := (Finset.sum_attach (B \ A) g).symm
  have h2 : ∑ j ∈ A \ B, g j = ∑ x : ↥(A \ B), g (x : Fin m) := (Finset.sum_attach (A \ B) g).symm
  have hsum : ∑ j ∈ B \ A, g j ≤ ∑ j ∈ A \ B, g j := by
    rw [h1, h2, ← Equiv.sum_comp e (fun x => g (x : Fin m))]
    exact Finset.sum_le_sum fun x _ =>
      hval _ (Finset.mem_sdiff.mp x.2).1 _ (Finset.mem_sdiff.mp (e x).2).2
  linarith

/-- For a monotone `g : Fin m → ℤ`, the prefix `∑_{i<k} g` (its `k` smallest values) is `≤` the sum
over any `k`-element subset. -/
private theorem mono_prefix_le_subset {m : ℕ} (g : Fin m → ℤ) (hg : Monotone g) (k : ℕ) (hk : k ≤ m)
    (A : Finset (Fin m)) (hA : A.card = k) :
    ∑ j ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < k), g j ≤ ∑ j ∈ A, g j := by
  refine sum_le_sum_of_compl_ge g A _ ?_ ?_
  · rw [hA, Fin.card_filter_val_lt]; omega
  · intro j hj j' hj'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    apply hg; rw [Fin.le_def]; omega

/-- The sorted prefix `∑_{i<k} srt n q i` as a sum over `{i : Fin n | i < k}` of `q ∘ sort q`. -/
private theorem srt_prefix_eq_filter (n k : ℕ) (hk : k ≤ n) (q : Fin n → ℤ) :
    ∑ i ∈ Finset.range k, srt n q i
      = ∑ j ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), (q ∘ Tuple.sort q) j := by
  symm
  apply Finset.sum_bij (i := fun (a : Fin n) _ => (a : ℕ))
  · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact Finset.mem_range.mpr ha
  · intro a _ b _ hab; exact Fin.ext hab
  · intro b hb; refine ⟨⟨b, lt_of_lt_of_le (Finset.mem_range.mp hb) hk⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Finset.mem_range.mp hb
  · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [srt, dif_pos (lt_of_lt_of_le ha hk), Function.comp_apply]

/-- **`k`-smallest-sum is `≤` any `k`-subset sum.** The sorted prefix of `q` (its `k` smallest
entries) is `≤` the sum of `q` over any `k`-element subset of indices. -/
private theorem smallestK_le_subset (n k : ℕ) (hk : k ≤ n) (q : Fin n → ℤ)
    (A : Finset (Fin n)) (hA : A.card = k) :
    ∑ i ∈ Finset.range k, srt n q i ≤ ∑ j ∈ A, q j := by
  rw [srt_prefix_eq_filter n k hk q]
  set A' := A.image (Tuple.sort q).symm with hA'
  have hreindex : ∑ j ∈ A, q j = ∑ j ∈ A', (q ∘ Tuple.sort q) j := by
    rw [hA', Finset.sum_image (fun a _ b _ h => (Tuple.sort q).symm.injective h)]
    apply Finset.sum_congr rfl; intro a _; simp
  rw [hreindex]
  refine mono_prefix_le_subset (q ∘ Tuple.sort q) (Tuple.monotone_sort q) k hk A' ?_
  rw [hA', Finset.card_image_of_injective _ (Tuple.sort q).symm.injective, hA]

/-- The sum of the `k` smallest entries of `q : Fin n → ℤ` (the sorted prefix `∑_{i<k} srt q i`). -/
noncomputable def smallestK (n k : ℕ) (q : Fin n → ℤ) : ℤ := ∑ i ∈ Finset.range k, srt n q i

/-- The index set of the `k` smallest entries of `w` (image of the first `k` sorted slots). Its
cardinality is `k` (for `k ≤ n`) and its `w`-sum is `smallestK n k w`. -/
noncomputable def leastSet (n k : ℕ) (w : Fin n → ℤ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)).image (Tuple.sort w)

/-- `leastSet n k w` has cardinality `min k n` and `w`-sum `smallestK n k w` (for `k ≤ n`). -/
private theorem leastSet_card_sum (n k : ℕ) (hk : k ≤ n) (w : Fin n → ℤ) :
    (leastSet n k w).card = k ∧ ∑ j ∈ leastSet n k w, w j = smallestK n k w := by
  have hcard : (leastSet n k w).card = k := by
    rw [leastSet, Finset.card_image_of_injective _ (Tuple.sort w).injective,
      Fin.card_filter_val_lt]; omega
  refine ⟨hcard, ?_⟩
  rw [smallestK, srt_prefix_eq_filter n k hk w, leastSet,
    Finset.sum_image (fun a _ b _ h => (Tuple.sort w).injective h)]
  exact Finset.sum_congr rfl (fun a _ => rfl)

/-- **Elementary transfer ⟹ `smallestK` weakly decreases.** If `w'` is `w` with the value at `lo`
pushed down (below both `w lo` and `w hi`) and `hi` pushed up by the same amount (total preserved),
all other entries fixed, then every `k`-smallest sum of `w'` is `≤` that of `w`. The single Karamata
elementary-transfer step (proved via the `k`-smallest-subset engine, no induction). -/
private theorem smallestK_pair_spread {n k : ℕ} (hk : k ≤ n) {w w' : Fin n → ℤ}
    {lo hi : Fin n} (hne : lo ≠ hi) (hlo₁ : w' lo ≤ w lo) (hlo₂ : w' lo ≤ w hi)
    (hsum : w' lo + w' hi = w lo + w hi) (hfixed : ∀ r, r ≠ lo → r ≠ hi → w' r = w r) :
    smallestK n k w' ≤ smallestK n k w := by
  obtain ⟨hScard, hSsum⟩ := leastSet_card_sum n k hk w
  set S := leastSet n k w with hSdef
  by_cases hcase : hi ∈ S ∧ lo ∉ S
  · -- swap hi for lo in S; the lifted lo is bounded by the (now-gone) hi
    obtain ⟨hhiS, hloS⟩ := hcase
    set A := insert lo (S.erase hi) with hAdef
    have hloErase : lo ∉ S.erase hi := fun h => hloS (Finset.mem_of_mem_erase h)
    have hkpos : 1 ≤ k := by
      rw [← hScard]; exact Finset.card_pos.mpr ⟨hi, hhiS⟩
    have hAcard : A.card = k := by
      rw [hAdef, Finset.card_insert_of_notMem hloErase, Finset.card_erase_of_mem hhiS, hScard]
      omega
    have hstep : smallestK n k w' ≤ ∑ j ∈ A, w' j := by
      rw [smallestK]; exact smallestK_le_subset n k hk w' A hAcard
    refine le_trans hstep ?_
    -- ∑_A w' = ∑_{S.erase hi} w + w' lo ≤ ∑_{S.erase hi} w + w hi = ∑_S w
    rw [hAdef, Finset.sum_insert hloErase]
    have heq : ∑ j ∈ S.erase hi, w' j = ∑ j ∈ S.erase hi, w j := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrhi : r ≠ hi := Finset.ne_of_mem_erase hr
      have hrlo : r ≠ lo := fun h => hloErase (h ▸ hr)
      exact hfixed r hrlo hrhi
    rw [heq]
    have hSsplit : ∑ j ∈ S.erase hi, w j + w hi = ∑ j ∈ S, w j := Finset.sum_erase_add S w hhiS
    rw [← hSsum]; linarith [hSsplit]
  · -- A = S works: the changed indices' sum over S only drops (or is fixed)
    have hstep : smallestK n k w' ≤ ∑ j ∈ S, w' j := by
      rw [smallestK]; exact smallestK_le_subset n k hk w' S hScard
    refine le_trans hstep ?_
    rw [← hSsum]
    -- compare ∑_S w' to ∑_S w pointwise-after-isolating lo,hi
    push_neg at hcase
    by_cases hloS : lo ∈ S
    · by_cases hhiS : hi ∈ S
      · -- both in S: sums equal by hsum
        have hsplit' : ∑ j ∈ S, w' j
            = ∑ j ∈ (S.erase lo).erase hi, w' j + w' lo + w' hi := by
          rw [add_right_comm, Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨(Ne.symm hne), hhiS⟩),
            Finset.sum_erase_add _ _ hloS]
        have hsplit : ∑ j ∈ S, w j
            = ∑ j ∈ (S.erase lo).erase hi, w j + w lo + w hi := by
          rw [add_right_comm, Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨(Ne.symm hne), hhiS⟩),
            Finset.sum_erase_add _ _ hloS]
        have hmid : ∑ j ∈ (S.erase lo).erase hi, w' j = ∑ j ∈ (S.erase lo).erase hi, w j := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrhi : r ≠ hi := Finset.ne_of_mem_erase hr
          have hrlo : r ≠ lo := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)
          exact hfixed r hrlo hrhi
        rw [hsplit', hsplit, hmid]; linarith
      · -- lo in S, hi not: drop at lo by hlo₁
        have hsplit' : ∑ j ∈ S, w' j = ∑ j ∈ S.erase lo, w' j + w' lo :=
          (Finset.sum_erase_add _ _ hloS).symm
        have hsplit : ∑ j ∈ S, w j = ∑ j ∈ S.erase lo, w j + w lo :=
          (Finset.sum_erase_add _ _ hloS).symm
        have hmid : ∑ j ∈ S.erase lo, w' j = ∑ j ∈ S.erase lo, w j := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrlo : r ≠ lo := Finset.ne_of_mem_erase hr
          have hrhi : r ≠ hi := fun h => hhiS (h ▸ Finset.mem_of_mem_erase hr)
          exact hfixed r hrlo hrhi
        rw [hsplit', hsplit, hmid]; linarith
    · -- lo not in S: then hi not in S either (else the by_cases branch); all fixed
      have hhiS : hi ∉ S := fun h => hloS (hcase h)
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro r hr
      have hrlo : r ≠ lo := fun h => hloS (h ▸ hr)
      have hrhi : r ≠ hi := fun h => hhiS (h ▸ hr)
      exact hfixed r hrlo hrhi

/-- `Mvec M : Fin (L+1) → ℤ`, the width sequence as a `Fin (L+1)` vector (for `smallestK`). -/
noncomputable def Mvec (M : Fin (L + 1) → ℕ) (i : Fin (L + 1)) : ℤ := (M i : ℤ)

/-- `eqPad M T : Fin (L+1) → ℤ`, the edge vector padded with `0` at the last index (so it and `Mvec`
are both `Fin (L+1)` vectors, for the corridor majorization). -/
noncomputable def eqPad (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (i : Fin (L + 1)) : ℤ :=
  if h : (i : ℕ) < L then edgeQ M T (i : ℕ) else 0

/-- The interpolating sequence `Vseq M T t`: edges on `[0,t)`, the level `u_t` at index `t`, and
widths past `t`. `Vseq M T 0 = Mvec`, `Vseq M T L = eqPad`; each step is
one Karamata elementary transfer (pushing `u_t` down to `u_{t+1}`, `M⁽ᵗ⁺¹⁾` up to `edgeQ_t`). -/
noncomputable def Vseq (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (t : ℕ) (i : Fin (L + 1)) : ℤ :=
  if (i : ℕ) < t then eqPad M T i
  else if (i : ℕ) = t then Useq M T t
  else Mvec M i

private theorem Vseq_zero (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Vseq M T 0 = Mvec M := by
  funext i; unfold Vseq
  rw [if_neg (by omega)]
  by_cases h : (i : ℕ) = 0
  · rw [if_pos h]
    have : i = (0 : Fin (L + 1)) := Fin.ext (by rw [h]; rfl)
    rw [this, Useq_zero]; unfold Mvec; rfl
  · rw [if_neg h]

private theorem Vseq_last (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hL : 1 ≤ L)
    (hlast : ∀ j : Fin L, j.val = L - 1 → T j = 0) : Vseq M T L = eqPad M T := by
  funext i; unfold Vseq
  by_cases h : (i : ℕ) < L
  · rw [if_pos h]
  · have hiL : (i : ℕ) = L := by omega
    rw [if_neg h, if_pos hiL]
    unfold eqPad; rw [dif_neg h]
    exact Useq_last M T hL hlast

/-- One step of the interpolation `Vseq M T t → Vseq M T (t+1)` weakly decreases every `smallestK`
(the Karamata elementary transfer `(u_t, M⁽ᵗ⁺¹⁾) ↦ (u_{t+1}, edgeQ_t)`). -/
private theorem Vseq_step (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (t : ℕ)
    (ht : t < L) (k : ℕ) (hk : k ≤ L + 1) :
    smallestK (L + 1) k (Vseq M T (t + 1)) ≤ smallestK (L + 1) k (Vseq M T t) := by
  let lo : Fin (L + 1) := ⟨t + 1, by omega⟩
  let hi : Fin (L + 1) := ⟨t, by omega⟩
  have hloval : (lo : ℕ) = t + 1 := rfl
  have hhival : (hi : ℕ) = t := rfl
  have hne : lo ≠ hi := fun h => absurd (congrArg Fin.val h) (by rw [hloval, hhival]; omega)
  -- values of Vseq (t+1) and Vseq t at lo, hi
  have hwlo : Vseq M T t lo = Mvec M lo := by
    unfold Vseq
    rw [if_neg (show ¬((lo : ℕ) < t) by rw [hloval]; omega),
        if_neg (show ¬((lo : ℕ) = t) by rw [hloval]; omega)]
  have hwhi : Vseq M T t hi = Useq M T t := by
    unfold Vseq
    rw [if_neg (show ¬((hi : ℕ) < t) by rw [hhival]; omega), if_pos hhival]
  have hw'lo : Vseq M T (t + 1) lo = Useq M T (t + 1) := by
    unfold Vseq
    rw [if_neg (show ¬((lo : ℕ) < t + 1) by rw [hloval]; omega), if_pos hloval]
  have hw'hi : Vseq M T (t + 1) hi = eqPad M T hi := by
    unfold Vseq; rw [if_pos (show (hi : ℕ) < t + 1 by rw [hhival]; omega)]
  have heqhi : eqPad M T hi = edgeQ M T t := by
    unfold eqPad; rw [dif_pos (show (hi : ℕ) < L by rw [hhival]; omega), hhival]
  have hMlo : Mvec M lo = Mseq M (t + 1) := by
    unfold Mvec Mseq; rw [dif_pos (show t + 1 < L + 1 by omega)]
  -- corridor facts
  have hu_anti : Useq M T (t + 1) ≤ Useq M T t := Useq_antitone M T hT t (by omega)
  have hu_le_M : Useq M T (t + 1) ≤ Mseq M (t + 1) := by
    have := Useq_le_M M T hT (t + 1) (by omega); exact this
  have hedge : edgeQ M T t = Mseq M (t + 1) + Useq M T t - Useq M T (t + 1) := by
    unfold edgeQ; ring
  refine smallestK_pair_spread (n := L + 1) (k := k) hk hne ?_ ?_ ?_ ?_
  · -- w' lo ≤ w lo : Useq (t+1) ≤ Mvec lo = Mseq (t+1)
    rw [hw'lo, hwlo, hMlo]; exact hu_le_M
  · -- w' lo ≤ w hi : Useq (t+1) ≤ Useq t
    rw [hw'lo, hwhi]; exact hu_anti
  · -- w' lo + w' hi = w lo + w hi
    rw [hw'lo, hw'hi, hwlo, hwhi, heqhi, hMlo, hedge]; ring
  · -- fixed elsewhere
    intro r hrlo hrhi
    have hrne1 : (r : ℕ) ≠ t + 1 := fun h => hrlo (Fin.ext (by rw [hloval]; exact h))
    have hrne0 : (r : ℕ) ≠ t := fun h => hrhi (Fin.ext (by rw [hhival]; exact h))
    unfold Vseq
    by_cases h1 : (r : ℕ) < t
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg (by omega), if_neg hrne1, if_neg (by omega), if_neg hrne0]

/-- **Corridor majorization (the key A1 lower-bound bridge).** For `T ∈ Adm M`, the `0`-padded edge
vector `eqPad` is majorized by the widths `Mvec`: every `k`-smallest sum of `eqPad` is `≤` that of
`Mvec`. Proved by folding `L` Karamata elementary transfers (`Vseq` interpolation). -/
private theorem smallestK_eqPad_le (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M)
    (hL : 1 ≤ L) (k : ℕ) (hk : k ≤ L + 1) :
    smallestK (L + 1) k (eqPad M T) ≤ smallestK (L + 1) k (Mvec M) := by
  have hlast : ∀ j : Fin L, j.val = L - 1 → T j = 0 := by
    rw [Adm, Finset.mem_filter] at hT; exact hT.2.2.2
  have hchain : ∀ t, t ≤ L → smallestK (L + 1) k (Vseq M T t) ≤ smallestK (L + 1) k (Mvec M) := by
    intro t ht
    induction t with
    | zero => rw [Vseq_zero]
    | succ s ih =>
      refine le_trans (Vseq_step M T hT s (by omega) k hk) (ih (by omega))
  have := hchain L (le_refl L)
  rwa [Vseq_last M T hL hlast] at this

/-- The bridge: the `k` smallest edges sum equals the `(k+1)` smallest of the `0`-padded edge vector
(the appended `0` is the minimum, so it joins the smallest slot for free). Lets the corridor
majorization (`Fin (L+1)`) feed the `Fin L` edge majorization. -/
private theorem edgeQ_nonneg (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    0 ≤ edgeQ M T (j : ℕ) := by
  unfold edgeQ
  have h1 : (0 : ℤ) ≤ Mseq M ((j : ℕ) + 1) := by
    unfold Mseq; split
    · positivity
    · exact le_refl 0
  have h2 : Useq M T ((j : ℕ) + 1) ≤ Useq M T (j : ℕ) := Useq_antitone M T hT (j : ℕ) (by omega)
  linarith

private theorem smallestK_edge_eq_pad (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M)
    (k : ℕ) (hk : k ≤ L) :
    smallestK L k (fun j : Fin L => edgeQ M T (j : ℕ))
      ≤ smallestK (L + 1) (k + 1) (eqPad M T) := by
  -- B = the (k+1) smallest positions of eqPad; A = its members that lie in Fin L (drop index L)
  obtain ⟨hBcard, hBsum⟩ := leastSet_card_sum (L + 1) (k + 1) (by omega) (eqPad M T)
  set B := leastSet (L + 1) (k + 1) (eqPad M T) with hBdef
  set lastI : Fin (L + 1) := ⟨L, by omega⟩ with hlastdef
  set A : Finset (Fin L) :=
    Finset.univ.filter (fun j : Fin L => (⟨(j : ℕ), by omega⟩ : Fin (L + 1)) ∈ B) with hAdef
  have hinjOn : Set.InjOn (fun j : Fin L => (⟨(j : ℕ), by omega⟩ : Fin (L + 1))) A :=
    fun a _ b _ h => Fin.ext (Fin.mk.inj h)
  have himg : A.image (fun j : Fin L => (⟨(j : ℕ), by omega⟩ : Fin (L + 1))) = B.erase lastI := by
    apply Finset.ext; intro i
    simp only [Finset.mem_image, hAdef, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, hlastdef]
    constructor
    · rintro ⟨j, hjB, rfl⟩
      exact ⟨fun h => absurd (Fin.mk.inj h) (by omega), hjB⟩
    · rintro ⟨hine, hiB⟩
      have hiL : (i : ℕ) < L := by
        rcases Nat.lt_or_ge (i : ℕ) L with h | h
        · exact h
        · exact absurd (Fin.ext (show (i : ℕ) = L by omega)) hine
      exact ⟨⟨(i : ℕ), hiL⟩, by simpa using hiB, Fin.ext rfl⟩
  -- ∑_A edgeQ = ∑_{B.erase lastI} eqPad  (eqPad = edgeQ on indices < L)
  have hAsum : ∑ j ∈ A, edgeQ M T (j : ℕ) = ∑ i ∈ B.erase lastI, eqPad M T i := by
    rw [← himg, Finset.sum_image hinjOn]
    apply Finset.sum_congr rfl; intro j _
    unfold eqPad
    rw [dif_pos (show ((⟨(j : ℕ), by omega⟩ : Fin (L + 1)) : ℕ) < L by simpa using j.isLt)]
  -- ∑_{B.erase lastI} eqPad ≤ ∑_B eqPad  (drop the nonneg entry at lastI)
  have heqPad_nonneg : ∀ i, 0 ≤ eqPad M T i := by
    intro i; unfold eqPad; split
    · rename_i h
      exact edgeQ_nonneg M T hT ⟨(i : ℕ), h⟩
    · exact le_refl 0
  have hdrop : ∑ i ∈ B.erase lastI, eqPad M T i ≤ ∑ i ∈ B, eqPad M T i := by
    by_cases h : lastI ∈ B
    · rw [← Finset.sum_erase_add B _ h]; linarith [heqPad_nonneg lastI]
    · rw [Finset.erase_eq_of_notMem h]
  have hAcard : k ≤ A.card := by
    have hcardeq : A.card = (B.erase lastI).card := by
      rw [← himg, Finset.card_image_of_injOn hinjOn]
    rw [hcardeq]
    have hple : B.card ≤ (B.erase lastI).card + 1 := by
      rw [Finset.card_erase_eq_ite]; split <;> omega
    omega
  -- extract a k-subset A'' ⊆ A; smallestK ≤ its sum ≤ ∑_A edgeQ ≤ ∑_{B.erase} eqPad ≤ ∑_B eqPad
  obtain ⟨A'', hA''sub, hA''card⟩ := Finset.le_card_iff_exists_subset_card.mp hAcard
  have hstep1 : smallestK L k (fun j : Fin L => edgeQ M T (j : ℕ)) ≤ ∑ j ∈ A'', edgeQ M T (j : ℕ) :=
    smallestK_le_subset L k hk _ A'' hA''card
  have hstep2 : ∑ j ∈ A'', edgeQ M T (j : ℕ) ≤ ∑ j ∈ A, edgeQ M T (j : ℕ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hA''sub
    intro j _ _; exact edgeQ_nonneg M T hT j
  rw [← hBsum]
  calc smallestK L k (fun j : Fin L => edgeQ M T (j : ℕ))
      ≤ ∑ j ∈ A'', edgeQ M T (j : ℕ) := hstep1
    _ ≤ ∑ j ∈ A, edgeQ M T (j : ℕ) := hstep2
    _ = ∑ i ∈ B.erase lastI, eqPad M T i := hAsum
    _ ≤ ∑ i ∈ B, eqPad M T i := hdrop

/-- The `k`-smallest of the edges is `≤` the `(k+1)`-smallest of the widths (`H4`/`F1` unified, via
corridor majorization + the padding bridge). -/
private theorem smallestK_edge_le_width (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M)
    (hL : 1 ≤ L) (k : ℕ) (hk : k ≤ L) :
    smallestK L k (fun j : Fin L => edgeQ M T (j : ℕ)) ≤ smallestK (L + 1) (k + 1) (Mvec M) := by
  refine le_trans (smallestK_edge_eq_pad M T hT k hk) ?_
  exact smallestK_eqPad_le M T hT hL (k + 1) (by omega)

/-- `srt`-prefix sum equals `smallestK` (unfolding). -/
private theorem smallestK_eq_srt (n k : ℕ) (q : Fin n → ℤ) :
    smallestK n k q = ∑ i ∈ Finset.range k, srt n q i := rfl

/-- The total of `srt n q` over `range n` equals `∑ q` (sorting is a permutation). -/
private theorem sum_srt_range (n : ℕ) (q : Fin n → ℤ) :
    ∑ i ∈ Finset.range n, srt n q i = ∑ i, q i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => srt n q i) n]
  rw [show (∑ i : Fin n, srt n q (i : ℕ)) = ∑ i : Fin n, q (Tuple.sort q i) from
    Finset.sum_congr rfl (fun i _ => by simp only [srt, dif_pos i.isLt])]
  exact Equiv.sum_comp (Tuple.sort q) q

/-- `srt n q` is monotone in the `ℕ` index (within range). -/
private theorem srt_mono (n : ℕ) (q : Fin n → ℤ) {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    srt n q i ≤ srt n q j := by
  simp only [srt, dif_pos (show i < n by omega), dif_pos hj]
  exact Tuple.monotone_sort q (by simp only [Fin.le_def]; omega)

/-- `srt n q` is nonnegative when `q` is. -/
private theorem srt_nonneg (n : ℕ) (q : Fin n → ℤ) (hq : ∀ i, 0 ≤ q i) (i : ℕ) : 0 ≤ srt n q i := by
  unfold srt; split
  · exact hq _
  · exact le_refl 0

/-- **A1 Step B (the one novel arithmetic sub-lemma; verified 0/11219).** The balanced split of `P`
into `c` parts maximises every `k`-smallest sum among nonneg integer `c`-vectors of total `≤ P`. The
convexity-irreducible piece: the average bound `m·smallestK ≤ k·∑` undershoots, balanced is needed
exactly. Proven by the water-filling contradiction: a too-big `k`-smallest forces a too-big tail. -/
private theorem stepB (P c k : ℕ) (hc : 0 < c) (hk : k ≤ c) (q : Fin c → ℤ)
    (hq : ∀ i, 0 ≤ q i) (hsum : (∑ i, q i) ≤ (P : ℤ)) :
    smallestK c k q ≤ (k : ℤ) * ((P / c : ℕ) : ℤ)
      + (max 0 ((k : ℤ) + ((P % c : ℕ) : ℤ) - (c : ℤ))) := by
  set b : ℤ := ((P / c : ℕ) : ℤ) with hb
  set r : ℤ := ((P % c : ℕ) : ℤ) with hr
  set e : ℤ := max 0 ((k : ℤ) + r - (c : ℤ)) with he
  have hPeq : (P : ℤ) = (c : ℤ) * b + r := by
    rw [hb, hr, ← Nat.cast_mul, ← Nat.cast_add]
    exact_mod_cast (Nat.div_add_mod P c).symm
  by_contra hcon
  push_neg at hcon
  -- hcon : k*b + e < smallestK c k q
  set x : ℕ → ℤ := srt c q with hx
  have hsmall : smallestK c k q = ∑ i ∈ Finset.range k, x i := rfl
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have hz : smallestK c k q = 0 := by rw [hsmall, hk0, Finset.range_zero, Finset.sum_empty]
    have he0 : (0 : ℤ) ≤ e := le_max_left _ _
    rw [hz, hk0] at hcon; push_cast at hcon; linarith
  -- k ≥ 1: x(k-1) is the largest of the first k; ∑_{<k} x ≤ k·x(k-1)
  have hxmono : ∀ i j, i ≤ j → j < c → x i ≤ x j := fun i j hij hj => srt_mono c q hij hj
  have hkm1 : k - 1 < c := by omega
  have hprefix_le : (∑ i ∈ Finset.range k, x i) ≤ (k : ℤ) * x (k - 1) := by
    calc (∑ i ∈ Finset.range k, x i) ≤ ∑ i ∈ Finset.range k, x (k - 1) := by
          apply Finset.sum_le_sum; intro i hi; rw [Finset.mem_range] at hi
          exact hxmono i (k - 1) (by omega) hkm1
      _ = (k : ℤ) * x (k - 1) := by rw [Finset.sum_const, Finset.card_range]; ring
  -- x(k-1) ≥ b+1 (else prefix ≤ k·b contradicts hcon, since e ≥ 0)
  have hxk_ge : b + 1 ≤ x (k - 1) := by
    by_contra hlt; push_neg at hlt
    have : x (k - 1) ≤ b := by omega
    have hpre : (∑ i ∈ Finset.range k, x i) ≤ (k : ℤ) * b := by
      refine le_trans hprefix_le ?_; nlinarith [Nat.cast_nonneg (α := ℤ) k]
    have : (0 : ℤ) ≤ e := le_max_left _ _
    rw [hsmall] at hcon; linarith
  -- tail ∑_{k≤i<c} x ≥ (c-k)·x(k-1) ≥ (c-k)(b+1); total ∑x ≥ (kb+e+1)+(c-k)(b+1) > P
  have htail : ((c : ℤ) - (k : ℤ)) * x (k - 1) ≤ ∑ i ∈ Finset.Ico k c, x i := by
    calc ((c : ℤ) - (k : ℤ)) * x (k - 1)
        = ∑ _i ∈ Finset.Ico k c, x (k - 1) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hk]
      _ ≤ ∑ i ∈ Finset.Ico k c, x i := by
          apply Finset.sum_le_sum; intro i hi; rw [Finset.mem_Ico] at hi
          exact hxmono (k - 1) i (by omega) (by omega)
  have hsplit : (∑ i, q i) = (∑ i ∈ Finset.range k, x i) + ∑ i ∈ Finset.Ico k c, x i := by
    rw [← sum_srt_range c q, ← hx, ← Finset.sum_range_add_sum_Ico x hk]
  -- combine
  have hcon' : (k : ℤ) * b + e + 1 ≤ ∑ i ∈ Finset.range k, x i := by rw [hsmall] at hcon; omega
  have htail' : ((c : ℤ) - (k : ℤ)) * (b + 1) ≤ ∑ i ∈ Finset.Ico k c, x i := by
    refine le_trans ?_ htail
    apply mul_le_mul_of_nonneg_left hxk_ge (by push_cast; omega)
  have he_ge : (k : ℤ) + r - (c : ℤ) ≤ e := le_max_right _ _
  have : (P : ℤ) + 1 ≤ ∑ i, q i := by
    rw [hsplit, hPeq]; nlinarith [hcon', htail', he_ge]
  linarith

/-- The `k`-smallest sum of the balanced split (closed form `k·b + max(0, k+r−c)`, `b = P/c`,
`r = P%c`). Proved by the same `srt`-monotone water-filling argument bounding it both ways. -/
private theorem smallestK_balancedSplit (P c k : ℕ) (hc : 0 < c) (hk : k ≤ c) :
    smallestK c k (fun i => ((balancedSplit P c i : ℕ) : ℤ))
      = (k : ℤ) * ((P / c : ℕ) : ℤ) + max 0 ((k : ℤ) + ((P % c : ℕ) : ℤ) - (c : ℤ)) := by
  set b : ℤ := ((P / c : ℕ) : ℤ) with hb
  set r : ℤ := ((P % c : ℕ) : ℤ) with hr
  have hrlt : P % c < c := Nat.mod_lt _ hc
  have hrnn : (0 : ℤ) ≤ r := by rw [hr]; positivity
  -- ∑ balancedSplit = P (closed-form sum)
  have hmod : P % c ≤ c := le_of_lt hrlt
  have hcard : (Finset.univ.filter (fun i : Fin c => (i : ℕ) < P % c)).card = P % c := by
    rw [Fin.card_filter_val_lt]; omega
  have hcompl : (Finset.univ.filter (fun i : Fin c => ¬ (i : ℕ) < P % c)).card = c - P % c := by
    have := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin c)))
      (p := fun i : Fin c => (i : ℕ) < P % c)
    simp only [Finset.card_univ, Fintype.card_fin] at this; rw [hcard] at this; omega
  have hbsterm : ∀ i : Fin c, ((balancedSplit P c i : ℕ) : ℤ)
      = if (i : ℕ) < P % c then ((P / c + 1 : ℕ) : ℤ) else ((P / c : ℕ) : ℤ) := by
    intro i; unfold balancedSplit; split_ifs <;> rfl
  have hP : (P : ℤ) = (c : ℤ) * ((P / c : ℕ) : ℤ) + ((P % c : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← Nat.cast_add]; exact_mod_cast (Nat.div_add_mod P c).symm
  have hbsumeq : (∑ i, ((balancedSplit P c i : ℕ) : ℤ)) = (P : ℤ) := by
    rw [Finset.sum_congr rfl (fun i _ => hbsterm i)]
    rw [Finset.sum_ite]; simp only [Finset.sum_const, nsmul_eq_mul]; rw [hcard, hcompl]
    rw [Nat.cast_sub hmod, Nat.cast_add, Nat.cast_one]
    rw [hP]; ring
  -- ≤ : stepB applied to balancedSplit itself (total = P)
  have hle := stepB P c k hc hk (fun i => ((balancedSplit P c i : ℕ) : ℤ))
    (fun i => by positivity) (le_of_eq hbsumeq)
  -- ≥ : smallestK = ∑ over leastSet S (|S|=k); ∑_S balancedSplit = k·b + bcount(S), bcount ≥ max
  obtain ⟨hScard, hSsum⟩ := leastSet_card_sum c k hk (fun i => ((balancedSplit P c i : ℕ) : ℤ))
  set S := leastSet c k (fun i => ((balancedSplit P c i : ℕ) : ℤ)) with hSdef
  -- ∑_S balancedSplit = ∑_S (if i<r then b+1 else b) = k·b + (count of i<r in S)
  set Sb1 := S.filter (fun i : Fin c => (i : ℕ) < P % c) with hSb1
  have hsumS : ∑ i ∈ S, ((balancedSplit P c i : ℕ) : ℤ)
      = (k : ℤ) * b + (Sb1.card : ℤ) := by
    have hterm2 : ∀ i : Fin c, ((balancedSplit P c i : ℕ) : ℤ)
        = if (i : ℕ) < P % c then b + 1 else b := by
      intro i; unfold balancedSplit; rw [hb]; split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl (fun i _ => hterm2 i)]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp only [nsmul_eq_mul, ← hSb1]
    have hcompl : (S.filter (fun i : Fin c => ¬ (i : ℕ) < P % c)).card = k - Sb1.card := by
      have := Finset.filter_card_add_filter_neg_card_eq_card (s := S)
        (p := fun i : Fin c => (i : ℕ) < P % c)
      rw [hScard] at this; rw [hSb1]; omega
    have hle' : Sb1.card ≤ k := by rw [hSb1, ← hScard]; exact Finset.card_filter_le _ _
    rw [hcompl, Nat.cast_sub hle']; ring
  -- bcount(S) ≥ max(0, k+r-c): S has k elements; non-(<r) ones live in {i ≥ r}, only c-r of them
  have hScompl : (S.filter (fun i : Fin c => ¬ (i : ℕ) < P % c)).card ≤ c - P % c := by
    rw [← hcompl]
    exact Finset.card_le_card
      (Finset.filter_subset_filter (fun i : Fin c => ¬ (i : ℕ) < P % c) (Finset.subset_univ S))
  have hsumcard := Finset.filter_card_add_filter_neg_card_eq_card (s := S)
    (p := fun i : Fin c => (i : ℕ) < P % c)
  rw [hScard, ← hSb1] at hsumcard
  -- ℕ fact: Sb1.card ≥ k + P%c - c (and ≥ 0)
  have hbcount_nat : (max 0 (k + P % c - c) : ℕ) ≤ Sb1.card := by omega
  have hbcount_ge : max 0 ((k : ℤ) + r - (c : ℤ)) ≤ (Sb1.card : ℤ) := by
    rw [hr]
    have hcast : ((max 0 (k + P % c - c) : ℕ) : ℤ) ≤ (Sb1.card : ℤ) := by exact_mod_cast hbcount_nat
    have : max 0 ((k : ℤ) + ((P % c : ℕ) : ℤ) - (c : ℤ)) ≤ ((max 0 (k + P % c - c) : ℕ) : ℤ) := by
      rw [Nat.cast_max]; push_cast; omega
    linarith
  have hge : (k : ℤ) * b + max 0 ((k : ℤ) + r - (c : ℤ))
      ≤ smallestK c k (fun i => ((balancedSplit P c i : ℕ) : ℤ)) := by
    rw [← hSsum, hsumS]; linarith [hbcount_ge]
  exact le_antisymm hle hge

/-- `aSort M : Fin (L+1) → ℕ`, the widths of `M` sorted ascending (`i`-th value = `i`-smallest). -/
noncomputable def aSort (M : Fin (L + 1) → ℕ) (i : Fin (L + 1)) : ℕ := M (Tuple.sort M i)

/-- `aSort` is monotone (ascending). -/
private theorem aSort_mono (M : Fin (L + 1) → ℕ) : Monotone (aSort M) := Tuple.monotone_sort M

/-- Total `n`-th smallest width `aS M n` (`= aₙ` for `n < L+1`, else `0`). -/
noncomputable def aS (M : Fin (L + 1) → ℕ) (n : ℕ) : ℕ :=
  if h : n < L + 1 then aSort M ⟨n, h⟩ else 0

/-- The sorted-prefix sum `Sprefix M n = a₀+⋯+a_{n-1}` (`n` smallest widths), as `ℕ`. -/
noncomputable def Sprefix (M : Fin (L + 1) → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, aS M i

/-- The achiever predicate `good M c`: the cumulative ceiling test `∀ 1 ≤ i ≤ c, i·aᵢ ≤ Sᵢ + i − 1`
(`Sᵢ = a₀+⋯+aᵢ`). `c = 1` always holds, and the achiever is the largest good `c ≤ L`. -/
def goodAch (M : Fin (L + 1) → ℕ) (c : ℕ) : Prop :=
  ∀ i : ℕ, i < c + 1 → 1 ≤ i → i * aS M i ≤ Sprefix M (i + 1) + i - 1

noncomputable instance (M : Fin (L + 1) → ℕ) (c : ℕ) : Decidable (goodAch M c) :=
  Classical.dec _

/-- `Sprefix M (n+1) = Sprefix M n + aₙ`. -/
private theorem Sprefix_succ (M : Fin (L + 1) → ℕ) (n : ℕ) :
    Sprefix M (n + 1) = Sprefix M n + aS M n := by
  unfold Sprefix; rw [Finset.sum_range_succ]

/-- `goodAch M 1` always holds (the base case making the achiever well-defined). -/
private theorem goodAch_one (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) : goodAch M 1 := by
  intro i hi1 hi
  interval_cases i
  · rw [Sprefix_succ M 1, Sprefix_succ M 0]
    simp only [Sprefix, Finset.range_zero, Finset.sum_empty, one_mul, zero_add]
    have h0 : (0 : ℕ) < L + 1 := by omega
    have h1 : (1 : ℕ) < L + 1 := by omega
    have : aS M 0 ≤ aS M 1 := by
      unfold aS; rw [dif_pos h0, dif_pos h1]; exact aSort_mono M (by simp [Fin.le_def])
    omega

/-- The achiever `cAch M`: the largest `c ≤ L` with `goodAch M c` (`goodAch 1` holds, so `≥ 1`). -/
noncomputable def cAch (M : Fin (L + 1) → ℕ) : ℕ := Nat.findGreatest (goodAch M) L

/-- The achiever lies in `{1,…,L}` and is `goodAch` (given `1 ≤ L`). -/
private theorem cAch_spec (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    1 ≤ cAch M ∧ cAch M ≤ L ∧ goodAch M (cAch M) :=
  ⟨Nat.le_findGreatest hL (goodAch_one M hL), Nat.findGreatest_le L,
    Nat.findGreatest_spec hL (goodAch_one M hL)⟩

/-- For a monotone `q`, `srt n q` is `q` (read at the `ℕ` index); sorting fixes a sorted tuple. -/
private theorem srt_of_monotone (n : ℕ) (q : Fin n → ℤ) (hq : Monotone q) (i : ℕ) (hi : i < n) :
    srt n q i = q ⟨i, hi⟩ := by
  simp only [srt, dif_pos hi]
  rw [(Tuple.sort_eq_refl_iff_monotone).mpr hq, Equiv.refl_apply]

/-- For monotone `q`, `smallestK n k q` is the direct prefix sum `∑_{i<k} q i`. -/
private theorem smallestK_of_monotone (n k : ℕ) (q : Fin n → ℤ) (hq : Monotone q) (hk : k ≤ n) :
    smallestK n k q = ∑ i ∈ Finset.range k, (if h : i < n then q ⟨i, h⟩ else 0) := by
  rw [smallestK]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [srt_of_monotone n q hq i (by omega), dif_pos (by omega)]

/-- `Mvec`'s sorted value at `j` equals `aSort M j` (both the `j`-th smallest width; the two sort
permutations may differ on ties but their value-sequences — the unique monotone form — agree). -/
private theorem Mvec_sort_eq_aSort (M : Fin (L + 1) → ℕ) (j : Fin (L + 1)) :
    Mvec M (Tuple.sort (Mvec M) j) = (aSort M j : ℤ) := by
  -- `Mvec M ∘ sort M` is monotone, so by uniqueness it equals `Mvec M ∘ sort (Mvec M)`
  have hmono : Monotone (Mvec M ∘ Tuple.sort M) := by
    intro a b hab
    simp only [Function.comp_apply, Mvec]
    exact_mod_cast Tuple.monotone_sort M hab
  have h1 : Mvec M ∘ Tuple.sort M = Mvec M ∘ Tuple.sort (Mvec M) :=
    Tuple.comp_sort_eq_comp_iff_monotone.mpr hmono
  have := congrArg (fun f => f j) h1
  simp only [Function.comp_apply] at this
  rw [← this]; rfl

/-- `smallestK (L+1) n (Mvec M) = Sprefix M n`: the `n`-smallest widths sum to the sorted prefix. -/
private theorem smallestK_Mvec (M : Fin (L + 1) → ℕ) (n : ℕ) (hn : n ≤ L + 1) :
    smallestK (L + 1) n (Mvec M) = (Sprefix M n : ℤ) := by
  rw [smallestK, Sprefix, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hi' : i < L + 1 := by omega
  rw [srt, dif_pos hi', aS, dif_pos hi']
  exact Mvec_sort_eq_aSort M ⟨i, hi'⟩

/-- `aS` is monotone in the `ℕ` index (the sorted widths ascend). -/
private theorem aS_mono (M : Fin (L + 1) → ℕ) {i j : ℕ} (hij : i ≤ j) (hj : j < L + 1) :
    aS M i ≤ aS M j := by
  unfold aS; rw [dif_pos (show i < L + 1 by omega), dif_pos hj]
  exact aSort_mono M (by simp only [Fin.le_def]; omega)

/-- When the achiever `c = cAch M < L`, `c+1` is not `goodAch` (`c` is the largest good index). -/
private theorem not_goodAch_cAch_succ (M : Fin (L + 1) → ℕ) (hcL : cAch M < L) :
    ¬ goodAch M (cAch M + 1) := by
  have h : Nat.findGreatest (goodAch M) L < cAch M + 1 := by rw [← cAch]; omega
  exact Nat.findGreatest_is_greatest h (by omega)

/-- **Junction bound** `⌊P/c⌋ + 1 ≤ a_{c+1}` (`P = Sprefix M (c+1)`, `c = cAch M < L`): the smallest
tail width dominates the balanced split's max. From `¬goodAch (c+1)` (violation lands at `c+1`). -/
private theorem junction_bound (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) (hcL : cAch M < L) :
    (Sprefix M (cAch M + 1)) / (cAch M) + 1 ≤ aS M (cAch M + 1) := by
  set c := cAch M with hc
  obtain ⟨hc1, hcleL, _⟩ := cAch_spec M hL
  have hng := not_goodAch_cAch_succ M hcL
  -- ¬goodAch (c+1): the violating index is c+1 (all i≤c are good)
  rw [goodAch] at hng; push_neg at hng
  obtain ⟨i, hilt, hi1, hviol⟩ := hng
  -- i ≤ c is good (goodAch c), so the violation forces i = c+1
  have hic : i = c + 1 := by
    by_contra hne
    have hic : i ≤ c := by omega
    have := (cAch_spec M hL).2.2 i (by omega) hi1
    omega
  subst hic
  -- (c+1)·a_{c+1} > Sprefix(c+2) + (c+1) − 1 = Sprefix(c+1) + a_{c+1} + c
  rw [Sprefix_succ M (c + 1)] at hviol
  -- Sprefix(c+2) = Sprefix(c+1) + aS(c+1); goal arithmetic
  have hPc : c * aS M (c + 1) > Sprefix M (c + 1) + c := by
    have : (c + 1) * aS M (c + 1) > Sprefix M (c + 1) + aS M (c + 1) + c := by omega
    nlinarith [this]
  -- c·a_{c+1} > P + c ≥ P ⟹ a_{c+1} > P/c ⟹ a_{c+1} ≥ P/c + 1
  have hdiv : Sprefix M (c + 1) / c * c ≤ Sprefix M (c + 1) := Nat.div_mul_le_self _ _
  -- P/c * c ≤ P < c·A ⟹ P/c * c < c·A ⟹ P/c < A
  have hlt : Sprefix M (c + 1) / c * c < c * aS M (c + 1) := by omega
  have : Sprefix M (c + 1) / c < aS M (c + 1) := by
    rw [mul_comm] at hlt; exact lt_of_mul_lt_mul_left hlt (Nat.zero_le c)
  omega

/-- The target edge multiset `Yvec`, arranged **monotone** (so its `srt` is itself): the sorted
balanced split of `P = Sprefix M (c+1)` into `c` parts on positions `[0,c)`, then the tail widths
`a_{c+1},…,a_L` on `[c,L)`. The lower bound's comparison vector and the achiever's edge image. -/
noncomputable def Yvec (M : Fin (L + 1) → ℕ) (c : ℕ) (j : Fin L) : ℤ :=
  if (j : ℕ) < c then
    (if (j : ℕ) < c - (Sprefix M (c + 1)) % c then ((Sprefix M (c + 1) / c : ℕ) : ℤ)
      else ((Sprefix M (c + 1) / c : ℕ) : ℤ) + 1)
  else (aS M (j + 1) : ℤ)

/-- `Yvec M (cAch M)` is monotone: balanced block `b ≤ b+1`, then the tail `aS` ascends, and at the
junction `b+1 ≤ a_{c+1}` (`junction_bound`). -/
private theorem Yvec_monotone (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    Monotone (Yvec M (cAch M)) := by
  set c := cAch M with hc
  obtain ⟨hc1, hcleL, _⟩ := cAch_spec M hL
  set b : ℤ := ((Sprefix M (c + 1) / c : ℕ) : ℤ) with hb
  -- the value of Yvec as a function of the nat index, monotone in it
  have hval : ∀ j : Fin L, Yvec M c j =
      (if (j : ℕ) < c then (if (j : ℕ) < c - Sprefix M (c + 1) % c then b else b + 1)
        else (aS M ((j : ℕ) + 1) : ℤ)) := fun j => rfl
  intro x y hxy
  rw [hval, hval]
  have hxyN : (x : ℕ) ≤ (y : ℕ) := hxy
  by_cases hxc : (x : ℕ) < c
  · by_cases hyc : (y : ℕ) < c
    · -- both in balanced block
      split_ifs with h1 h2 h2 <;> first | rfl | (try omega) | linarith
    · -- x in balanced, y in tail: b or b+1 ≤ aS(y+1); use junction b+1 ≤ aS(c+1) ≤ aS(y+1)
      rw [if_pos hxc, if_neg hyc]
      have hcL : c < L := by
        rcases lt_or_eq_of_le hcleL with h | h
        · exact h
        · exact absurd (by omega : (y : ℕ) < c) (by omega)
      have hj := junction_bound M hL hcL
      have hmono : aS M (c + 1) ≤ aS M ((y : ℕ) + 1) :=
        aS_mono M (by omega) (by omega)
      have hbb : (if (x : ℕ) < c - Sprefix M (c + 1) % c then b else b + 1) ≤ b + 1 := by
        split_ifs <;> [linarith; rfl]
      have : b + 1 ≤ (aS M (c + 1) : ℤ) := by rw [hb]; exact_mod_cast hj
      calc (if (x : ℕ) < c - Sprefix M (c + 1) % c then b else b + 1) ≤ b + 1 := hbb
        _ ≤ (aS M (c + 1) : ℤ) := this
        _ ≤ (aS M ((y : ℕ) + 1) : ℤ) := by exact_mod_cast hmono
  · -- x in tail ⟹ y in tail
    rw [if_neg hxc, if_neg (by omega : ¬ (y : ℕ) < c)]
    exact_mod_cast aS_mono M (by omega) (by omega)

/-- `(range c).filter (· < m) = range m` for `m ≤ c`. -/
private theorem filter_range_lt (c m : ℕ) (hm : m ≤ c) :
    (Finset.range c).filter (fun j => j < m) = Finset.range m := by
  ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega

/-- The balanced block of `Yvec` (sorted form `b…b,b+1…b+1`) has the same sum-of-squares as
`balancedSplit P c` (same multiset: `c−r` copies of `b`, `r` of `b+1`). -/
private theorem Yvec_balanced_sq (M : Fin (L + 1) → ℕ) (c : ℕ) (hc : 0 < c) :
    ∑ j ∈ Finset.range c,
        (if j < c - Sprefix M (c + 1) % c then ((Sprefix M (c + 1) / c : ℕ) : ℤ)
          else ((Sprefix M (c + 1) / c : ℕ) : ℤ) + 1) ^ 2
      = ∑ i : Fin c, ((balancedSplit (Sprefix M (c + 1)) c i : ℕ) : ℤ) ^ 2 := by
  set P := Sprefix M (c + 1) with hP
  set b : ℤ := ((P / c : ℕ) : ℤ) with hb
  set rr : ℤ := ((P % c : ℕ) : ℤ) with hrr
  rw [balancedSplit_sq_int P c hc]
  have hr : P % c ≤ c := le_of_lt (Nat.mod_lt _ hc)
  -- push the square inside the if, then split the sum
  have hterm : ∀ j, ((if j < c - P % c then b else b + 1) ^ 2)
      = (if j < c - P % c then b ^ 2 else (b + 1) ^ 2) := fun j => by split_ifs <;> rfl
  simp only [hterm]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have hcard1 : (Finset.range c |>.filter (fun j => j < c - P % c)).card = c - P % c := by
    rw [filter_range_lt c (c - P % c) (by omega), Finset.card_range]
  have hcard2 : (Finset.range c |>.filter (fun j => ¬ j < c - P % c)).card = P % c := by
    have := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.range c)
      (p := fun j => j < c - P % c)
    rw [hcard1, Finset.card_range] at this; omega
  rw [hcard1, hcard2, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hr]
  ring

/-- `∑ (M i)² = ∑ (aS M i)²` (sum of squares is invariant under the sorting permutation). -/
private theorem sum_sq_M_eq_aS (M : Fin (L + 1) → ℕ) :
    ∑ i : Fin (L + 1), ((M i : ℤ)) ^ 2 = ∑ i ∈ Finset.range (L + 1), (aS M i : ℤ) ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => (aS M i : ℤ) ^ 2) (L + 1)]
  rw [show (∑ i : Fin (L + 1), (aS M (i : ℕ) : ℤ) ^ 2)
        = ∑ i : Fin (L + 1), ((M (Tuple.sort M i) : ℤ)) ^ 2 from
      Finset.sum_congr rfl (fun i _ => by rw [aS, dif_pos i.isLt]; rfl)]
  exact (Equiv.sum_comp (Tuple.sort M) (fun i => ((M i : ℤ)) ^ 2)).symm

/-- `∑ Yvec²` over `Fin L`, written as a `range L` sum (for splitting at `c`). -/
private theorem sum_Yvec_sq_range (M : Fin (L + 1) → ℕ) (c : ℕ) :
    (∑ j : Fin L, (Yvec M c j) ^ 2)
      = ∑ j ∈ Finset.range L,
          (if j < c then (if j < c - Sprefix M (c + 1) % c then ((Sprefix M (c + 1) / c : ℕ) : ℤ)
              else ((Sprefix M (c + 1) / c : ℕ) : ℤ) + 1)
            else (aS M (j + 1) : ℤ)) ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => _) L]
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-- **A1 value identity (E).** `∑ Yvec² − ∑ M² = ∑(balancedSplit P c)² − ∑(sortedSmallest)²`: the
tail (the `L−c` largest widths) appears in both `∑Yvec²` and `∑M²` and cancels. -/
private theorem Yvec_value (M : Fin (L + 1) → ℕ) (c : ℕ) (hc : c ≤ L) (hc1 : 1 ≤ c) :
    (∑ j : Fin L, (Yvec M c j) ^ 2) - ∑ i : Fin (L + 1), ((M i : ℤ)) ^ 2
      = (∑ i : Fin c, ((balancedSplit (Sprefix M (c + 1)) c i : ℕ) : ℤ) ^ 2)
        - ∑ k : Fin (c + 1), ((sortedSmallest M c hc k : ℕ) : ℤ) ^ 2 := by
  set P := Sprefix M (c + 1) with hP
  set bform := fun j => (if j < c - P % c then ((P / c : ℕ) : ℤ) else ((P / c : ℕ) : ℤ) + 1)
    with hbf
  -- ∑ Yvec² = balanced-block² + tail²  (split range L at c)
  have hYsplit : (∑ j : Fin L, (Yvec M c j) ^ 2)
      = (∑ j ∈ Finset.range c, (bform j) ^ 2)
        + ∑ j ∈ Finset.Ico c L, (aS M (j + 1) : ℤ) ^ 2 := by
    rw [sum_Yvec_sq_range M c, ← Finset.sum_range_add_sum_Ico _ hc]
    congr 1
    · exact Finset.sum_congr rfl (fun j hj => by
        rw [Finset.mem_range] at hj; rw [if_pos hj])
    · exact Finset.sum_congr rfl (fun j hj => by
        rw [Finset.mem_Ico] at hj; rw [if_neg (by omega)])
  -- ∑ M² = ∑ aS² = sortedSmallest² + tail²  (split range (L+1) at c+1)
  have hMsplit : ∑ i : Fin (L + 1), ((M i : ℤ)) ^ 2
      = (∑ k : Fin (c + 1), ((sortedSmallest M c hc k : ℕ) : ℤ) ^ 2)
        + ∑ i ∈ Finset.Ico (c + 1) (L + 1), (aS M i : ℤ) ^ 2 := by
    rw [sum_sq_M_eq_aS M, ← Finset.sum_range_add_sum_Ico _ (by omega : c + 1 ≤ L + 1)]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => (aS M i : ℤ) ^ 2) (c + 1)]
    exact Finset.sum_congr rfl (fun k _ => by
      rw [aS, dif_pos (by omega), sortedSmallest]; rfl)
  -- the two tails are equal (reindex Ico c L by +1 ↦ Ico (c+1) (L+1))
  have htail : ∑ j ∈ Finset.Ico c L, (aS M (j + 1) : ℤ) ^ 2
      = ∑ i ∈ Finset.Ico (c + 1) (L + 1), (aS M i : ℤ) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr (by congr 1; omega)
    intro k _
    have : c + k + 1 = c + 1 + k := by omega
    rw [this]
  rw [hYsplit, hMsplit, htail, Yvec_balanced_sq M c hc1]
  ring

/-- The `k`-smallest of `edgeQ` restricted to its `c` smallest equals the `k`-smallest of `edgeQ`
(`k ≤ c`); the first `c` sorted values, re-sorted, are unchanged. -/
private theorem smallestK_restrict (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (c k : ℕ) (hk : k ≤ c)
    (hcL : c ≤ L) :
    smallestK c k (fun i : Fin c => srt L (fun j : Fin L => edgeQ M T (j : ℕ)) (i : ℕ))
      = smallestK L k (fun j : Fin L => edgeQ M T (j : ℕ)) := by
  set q := fun j : Fin L => edgeQ M T (j : ℕ) with hq
  set xc := fun i : Fin c => srt L q (i : ℕ) with hxc
  have hxcmono : Monotone xc := by
    intro a b hab; rw [hxc]; exact srt_mono L q hab (by omega)
  rw [smallestK, smallestK]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [srt_of_monotone c xc hxcmono i (by omega)]

/-- **k ≤ c regime.** `smallestK L k edgeQ ≤ smallestK c k (balancedSplit P c)` for `T ∈ Adm M`,
`k ≤ c = cAch M`: F1 (`smallestK_edge_le_width` at `c`, giving `∑(c smallest) ≤ P`) + Step B. -/
private theorem edge_le_balanced (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (hL : 1 ≤ L)
    (k : ℕ) (hkc : k ≤ cAch M) :
    smallestK L k (fun j : Fin L => edgeQ M T (j : ℕ))
      ≤ smallestK (cAch M) k
          (fun i => ((balancedSplit (Sprefix M (cAch M + 1)) (cAch M) i : ℕ) : ℤ)) := by
  set c := cAch M with hc
  obtain ⟨hc1, hcleL, _⟩ := cAch_spec M hL
  set q := fun j : Fin L => edgeQ M T (j : ℕ) with hq
  set xc := fun i : Fin c => srt L q (i : ℕ) with hxc
  -- F1: ∑ xc = smallestK L c edgeQ ≤ smallestK (L+1)(c+1) Mvec = Sprefix M (c+1)
  have hF1 : (∑ i, xc i) ≤ (Sprefix M (c + 1) : ℤ) := by
    have hle := smallestK_edge_le_width M T hT hL c hcleL
    rw [smallestK_Mvec M (c + 1) (by omega)] at hle
    have hsum : (∑ i, xc i) = smallestK L c q := by
      rw [smallestK, hxc, ← Fin.sum_univ_eq_sum_range (fun i => srt L q i) c]
    rw [hsum]; exact hle
  -- xc nonneg
  have hxcnn : ∀ i, 0 ≤ xc i := fun i => srt_nonneg L q (fun j => edgeQ_nonneg M T hT j) (i : ℕ)
  -- Step B on xc
  have hstepB := stepB (Sprefix M (c + 1)) c k hc1 hkc xc hxcnn hF1
  rw [smallestK_balancedSplit (Sprefix M (c + 1)) c k hc1 hkc]
  rw [smallestK_restrict M T c k hkc hcleL] at hstepB
  exact hstepB

/-- The monotone-`Yvec` prefix sum `∑_{i<k} Yvec`, in two regimes: `k·b + max(0,k+r−c)` for `k≤c`
(the balanced block), `Sprefix M (k+1)` for `c<k≤L` (balanced total + the `k−c` smallest tail). -/
private theorem Yvec_prefix (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) (k : ℕ) (hk : k ≤ L) :
    ∑ i ∈ Finset.range k, (if h : i < L then Yvec M (cAch M) ⟨i, h⟩ else 0)
      = if k ≤ cAch M then
          (k : ℤ) * ((Sprefix M (cAch M + 1) / cAch M : ℕ) : ℤ)
            + max 0 ((k : ℤ) + ((Sprefix M (cAch M + 1) % cAch M : ℕ) : ℤ) - (cAch M : ℤ))
        else (Sprefix M (k + 1) : ℤ) := by
  set c := cAch M with hc
  obtain ⟨hc1, hcleL, _⟩ := cAch_spec M hL
  set P := Sprefix M (c + 1) with hP
  set b : ℤ := ((P / c : ℕ) : ℤ) with hb
  set r : ℤ := ((P % c : ℕ) : ℤ) with hr
  have hrlt : P % c < c := Nat.mod_lt _ hc1
  -- the balanced-block prefix sum `∑_{i<m} bform = m·b + max(0, m+r−c)` for `m ≤ c`
  have hbalpre : ∀ m, m ≤ c →
      ∑ i ∈ Finset.range m, (if i < c - P % c then b else b + 1)
        = (m : ℤ) * b + max 0 ((m : ℤ) + r - (c : ℤ)) := by
    intro m hm
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    have hcard1 : ((Finset.range m).filter (fun i => i < c - P % c)).card = min m (c - P % c) := by
      rw [show ((Finset.range m).filter (fun i => i < c - P % c))
            = Finset.range (min m (c - P % c)) from by
          ext i; simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]]
      rw [Finset.card_range]
    have hcard2 : ((Finset.range m).filter (fun i => ¬ i < c - P % c)).card = m - (c - P % c) := by
      have := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.range m)
        (p := fun i => i < c - P % c)
      rw [hcard1, Finset.card_range] at this; omega
    rw [hcard1, hcard2, nsmul_eq_mul, nsmul_eq_mul, hr]
    -- ↑(m-(c-r')) = max 0 (m+r'-c); ↑(min m (c-r')) = m - that
    have hmaxcast : ((m - (c - P % c) : ℕ) : ℤ)
        = max 0 ((m : ℤ) + ((P % c : ℕ) : ℤ) - (c : ℤ)) := by
      rcases Nat.lt_or_ge (m + P % c) c with h | h
      · rw [show m - (c - P % c) = 0 by omega, max_eq_left (by push_cast; omega)]; rfl
      · rw [max_eq_right (by push_cast; omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast; ring
    have hmincast : ((min m (c - P % c) : ℕ) : ℤ) = (m : ℤ) - ((m - (c - P % c) : ℕ) : ℤ) := by
      rw [← Nat.cast_sub (by omega)]; congr 1; omega
    rw [hmincast, hmaxcast]; ring
  by_cases hkc : k ≤ c
  · rw [if_pos hkc]
    rw [show (∑ i ∈ Finset.range k, (if h : i < L then Yvec M c ⟨i, h⟩ else 0))
          = ∑ i ∈ Finset.range k, (if i < c - P % c then b else b + 1) from ?_]
    · exact hbalpre k hkc
    · apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_pos (show i < L by omega), Yvec, if_pos (show ((⟨i, by omega⟩ : Fin L) : ℕ) < c by
        simp only [Fin.val_mk]; omega)]
  · rw [if_neg hkc]
    -- split range k = range c ⊎ Ico c k; balanced total P + tail = Sprefix(k+1)
    rw [← Finset.sum_range_add_sum_Ico _ (not_le.mp hkc).le]
    have hbal : ∑ i ∈ Finset.range c, (if h : i < L then Yvec M c ⟨i, h⟩ else 0)
        = (P : ℤ) := by
      rw [show (∑ i ∈ Finset.range c, (if h : i < L then Yvec M c ⟨i, h⟩ else 0))
            = ∑ i ∈ Finset.range c, (if i < c - P % c then b else b + 1) from ?_]
      · rw [hbalpre c (le_refl c)]
        have hrnn : (0 : ℤ) ≤ ((P % c : ℕ) : ℤ) := by positivity
        rw [max_eq_right (show (0 : ℤ) ≤ (c : ℤ) + r - (c : ℤ) by rw [hr]; linarith)]
        have hPeq : (P : ℤ) = (c : ℤ) * b + r := by
          rw [hb, hr, ← Nat.cast_mul, ← Nat.cast_add]; exact_mod_cast (Nat.div_add_mod P c).symm
        rw [hPeq]; ring
      · apply Finset.sum_congr rfl; intro i hi
        rw [Finset.mem_range] at hi
        rw [dif_pos (show i < L by omega), Yvec, if_pos (show ((⟨i, by omega⟩ : Fin L) : ℕ) < c by
          simp only [Fin.val_mk]; omega)]
    have htail : ∑ i ∈ Finset.Ico c k, (if h : i < L then Yvec M c ⟨i, h⟩ else 0)
        = ∑ i ∈ Finset.Ico c k, (aS M (i + 1) : ℤ) := by
      apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mem_Ico] at hi
      rw [dif_pos (show i < L by omega), Yvec, if_neg (show ¬ ((⟨i, by omega⟩ : Fin L) : ℕ) < c by
        simp only [Fin.val_mk]; omega)]
    rw [hbal, htail]
    -- P + ∑_{Ico c k} aS(i+1) = Sprefix(k+1) = ∑_{i<k+1} aS i
    have hPeq : (P : ℤ) = ∑ i ∈ Finset.range (c + 1), (aS M i : ℤ) := by
      rw [hP, Sprefix, Nat.cast_sum]
    have hSk : (Sprefix M (k + 1) : ℤ) = ∑ i ∈ Finset.range (k + 1), (aS M i : ℤ) := by
      rw [Sprefix, Nat.cast_sum]
    rw [hPeq, hSk, ← Finset.sum_range_add_sum_Ico _ (by omega : c + 1 ≤ k + 1)]
    congr 1
    -- ∑_{Ico c k} aS(i+1) = ∑_{Ico (c+1) (k+1)} aS i  (reindex i ↦ i+1)
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr (by congr 1; omega)
    intro i _
    have : c + i + 1 = c + 1 + i := by omega
    rw [this]

/-- **The per-`T` domination** `∀k, smallestK L k edgeQ ≤ smallestK L k (Yvec M cAch)`, `T ∈ Adm M`
— the input to `sq_sum_le_of_sorted_prefix`. `k ≤ c`: `edge_le_balanced` + balanced closed form;
`k > c`: `smallestK_edge_le_width` (`≤ Sprefix`). -/
private theorem edge_le_Yvec (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (hL : 1 ≤ L)
    (k : ℕ) (hk : k ≤ L) :
    smallestK L k (fun j : Fin L => edgeQ M T (j : ℕ)) ≤ smallestK L k (Yvec M (cAch M)) := by
  set c := cAch M with hc
  obtain ⟨hc1, hcleL, _⟩ := cAch_spec M hL
  rw [smallestK_of_monotone L k (Yvec M c) (Yvec_monotone M hL) hk, Yvec_prefix M hL k hk]
  by_cases hkc : k ≤ c
  · rw [if_pos hkc]
    have := edge_le_balanced M T hT hL k hkc
    rwa [smallestK_balancedSplit (Sprefix M (c + 1)) c k hc1 hkc] at this
  · rw [if_neg hkc]
    have := smallestK_edge_le_width M T hT hL k hk
    rwa [smallestK_Mvec M (k + 1) (by omega)] at this

/-- `∑ edgeQ = ∑ M` (the edge total telescopes to the full width sum, using `u_L = 0`). -/
private theorem sum_edgeQ (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (hL : 1 ≤ L) :
    ∑ j : Fin L, edgeQ M T (j : ℕ) = ∑ i : Fin (L + 1), (M i : ℤ) := by
  have hlast : ∀ j : Fin L, j.val = L - 1 → T j = 0 := by
    rw [Adm, Finset.mem_filter] at hT; exact hT.2.2.2
  rw [Fin.sum_univ_eq_sum_range (fun j => edgeQ M T j) L]
  rw [prefix_edgeQ M T L, Useq_zero, Useq_last M T hL hlast]
  have hM0 : Mseq M 0 = (M 0 : ℤ) := by unfold Mseq; rw [dif_pos (by omega)]; rfl
  have hMseqsum : ∑ i ∈ Finset.range (L + 1), Mseq M i = ∑ i : Fin (L + 1), (M i : ℤ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => Mseq M i) (L + 1)]
    exact Finset.sum_congr rfl (fun i _ => by unfold Mseq; rw [dif_pos i.isLt])
  rw [hM0, hMseqsum]
  ring

/-- `Sprefix M (L+1) = ∑ M i` (the full sorted prefix equals the total). -/
private theorem Sprefix_total (M : Fin (L + 1) → ℕ) :
    (Sprefix M (L + 1) : ℤ) = ∑ i : Fin (L + 1), (M i : ℤ) := by
  rw [Sprefix, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (aS M i : ℤ)) (L + 1)]
  rw [show (∑ i : Fin (L + 1), (aS M (i : ℕ) : ℤ)) = ∑ i : Fin (L + 1), ((M (Tuple.sort M i)) : ℤ)
      from Finset.sum_congr rfl (fun i _ => by rw [aS, dif_pos i.isLt]; rfl)]
  exact Equiv.sum_comp (Tuple.sort M) (fun i => (M i : ℤ))

/-- `∑ Yvec = ∑ M` (total preserved). -/
private theorem sum_Yvec (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    ∑ j : Fin L, Yvec M (cAch M) j = ∑ i : Fin (L + 1), (M i : ℤ) := by
  set c := cAch M with hc
  obtain ⟨hc1, hcleL, _⟩ := cAch_spec M hL
  have hpre := Yvec_prefix M hL L (le_refl L)
  rw [← hc] at hpre
  rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < L then Yvec M c ⟨i, h⟩ else 0)) L] at hpre
  rw [show (∑ i : Fin L, (if h : (i : ℕ) < L then Yvec M c ⟨i, h⟩ else 0))
        = ∑ i : Fin L, Yvec M c i from
      Finset.sum_congr rfl (fun i _ => by rw [dif_pos i.isLt])] at hpre
  rw [hpre, ← Sprefix_total M]
  by_cases hcL : L ≤ c
  · have hcLeq : c = L := le_antisymm hcleL hcL
    rw [if_pos hcL, hcLeq]
    have hrnn : (0 : ℤ) ≤ ((Sprefix M (L + 1) % L : ℕ) : ℤ) := by positivity
    rw [max_eq_right (show (0:ℤ) ≤ (L:ℤ) + ((Sprefix M (L+1) % L : ℕ):ℤ) - (L:ℤ) by linarith)]
    have hLpos : 0 < L := by omega
    have hPeq : (Sprefix M (L + 1) : ℤ)
        = (L : ℤ) * ((Sprefix M (L + 1) / L : ℕ) : ℤ) + ((Sprefix M (L + 1) % L : ℕ) : ℤ) := by
      rw [← Nat.cast_mul, ← Nat.cast_add]; exact_mod_cast (Nat.div_add_mod _ L).symm
    rw [hPeq]; ring
  · rw [if_neg hcL]

/-- **A1 lower bound (C).** For `T ∈ Adm M`, `∑Yvec² − ∑M² ≤ 2·Mval M T` — the convexity bound from
the `Yvec`-domination via `sq_sum_le_of_sorted_prefix` + `edge_identity`. -/
private theorem two_Mval_ge (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (hL : 1 ≤ L) :
    (∑ j : Fin L, (Yvec M (cAch M) j) ^ 2) - ∑ i : Fin (L + 1), ((M i : ℤ)) ^ 2
      ≤ 2 * Mval M T := by
  set c := cAch M with hc
  set q := fun j : Fin L => edgeQ M T (j : ℕ) with hq
  have hlast : ∀ j : Fin L, j.val = L - 1 → T j = 0 := by
    rw [Adm, Finset.mem_filter] at hT; exact hT.2.2.2
  -- ∑ Yvec² ≤ ∑ q²  via sq_sum_le_of_sorted_prefix (total + domination)
  have htot : ∑ j, q j = ∑ j, Yvec M c j := by
    rw [sum_edgeQ M T hT hL, sum_Yvec M hL]
  have hdom : ∀ k, k ≤ L → ∑ i ∈ Finset.range k, srt L q i
      ≤ ∑ i ∈ Finset.range k, srt L (Yvec M c) i := fun k hk => edge_le_Yvec M T hT hL k hk
  have hsq : ∑ j, (Yvec M c j) ^ 2 ≤ ∑ j, (q j) ^ 2 :=
    sq_sum_le_of_sorted_prefix L q (Yvec M c) htot hdom
  -- edge_identity: 2·Mval = ∑ q² − ∑ Mseq²; relate the two sums to the Fin-univ forms
  have hedge := edge_identity M T hL hlast
  have hqsq : ∑ j ∈ Finset.range L, edgeQ M T j ^ 2 = ∑ j : Fin L, (q j) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => edgeQ M T j ^ 2) L]
  have hMsq : ∑ i ∈ Finset.range (L + 1), Mseq M i ^ 2 = ∑ i : Fin (L + 1), ((M i : ℤ)) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => Mseq M i ^ 2) (L + 1)]
    exact Finset.sum_congr rfl (fun i _ => by unfold Mseq; rw [dif_pos i.isLt])
  rw [hqsq, hMsq] at hedge
  linarith [hsq, hedge]

/-- The telescoped level sequence `uTel M q : ℕ → ℤ` for a target edge sequence `q`: `u₀ = M⁰`,
`u_{j+1} = M⁽ʲ⁺¹⁾ + u_j − q_j`. Inverse to `edgeQ` (D1). -/
noncomputable def uTel (M : Fin (L + 1) → ℕ) (q : ℕ → ℤ) : ℕ → ℤ
  | 0 => (M 0 : ℤ)
  | (j + 1) => Mseq M (j + 1) + uTel M q j - q j

/-- **(D1) telescope is `edgeQ`-inverse.** If the telescoped `uTel` stays nonneg and ends at `0`,
the admissible `T*_j := (uTel M q (j+1)).toNat` has `edgeQ M T* j = q j` identically (the clamps are
inactive). The achiever's edge image equals its target by construction. -/
private theorem edgeQ_telescope (M : Fin (L + 1) → ℕ) (q : ℕ → ℤ)
    (hnn : ∀ j, 0 ≤ uTel M q j) (hlast : uTel M q L = 0)
    (T : Fin L → ℕ) (hT : ∀ j : Fin L, (T j : ℤ) = uTel M q (j.val + 1)) (j : Fin L) :
    edgeQ M T (j : ℕ) = q (j : ℕ) := by
  unfold edgeQ
  have hu0 : Useq M T (j : ℕ) = uTel M q (j : ℕ) := by
    rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
    · rw [h, Useq_zero, uTel]
    · rw [Useq_pos M T (j : ℕ) (by omega) (by omega)]
      have hh := hT ⟨(j : ℕ) - 1, by omega⟩
      rw [show ((j : ℕ) - 1) + 1 = (j : ℕ) by omega] at hh
      exact hh
  have hu1 : Useq M T ((j : ℕ) + 1) = uTel M q ((j : ℕ) + 1) := by
    rw [Useq_pos M T ((j : ℕ) + 1) (by omega) (by omega)]
    have hh := hT ⟨(j : ℕ), by omega⟩
    simp only [Nat.add_sub_cancel]
    exact hh
  rw [hu0, hu1]
  show Mseq M ((j : ℕ) + 1) + uTel M q (j : ℕ) - uTel M q ((j : ℕ) + 1) = q (j : ℕ)
  rw [uTel]; ring

/-- `aS M i ≤ b+1` for `1 ≤ i ≤ c` (`b = ⌊Sprefix(c+1)/c⌋`), from `good c` at `i=c` + sortedness. -/
private theorem aS_le_bp1 (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) {i : ℕ} (hi1 : 1 ≤ i)
    (hic : i ≤ cAch M) :
    aS M i ≤ Sprefix M (cAch M + 1) / cAch M + 1 := by
  set c := cAch M with hc
  obtain ⟨hc1, hcleL, hgood⟩ := cAch_spec M hL
  set P := Sprefix M (c + 1) with hP
  -- good c at i=c: c·a_c ≤ Sprefix(c+1) + c − 1 = P + c − 1
  have hgc := hgood c (by omega) hc1
  rw [← hP] at hgc
  -- a_c ≤ b+1: c·a_c ≤ P+c−1 = c·b+r+c−1 < c(b+2), so a_c < b+2
  have hPdm : P = c * (P / c) + P % c := (Nat.div_add_mod P c).symm
  have hrlt : P % c < c := Nat.mod_lt _ hc1
  -- c·a_c ≤ P+c−1 = c·(P/c) + (P%c + c − 1) < c·(P/c+2), so a_c ≤ P/c+1
  have hac : aS M c ≤ P / c + 1 := by
    by_contra hgt; push_neg at hgt
    have hge2 : P / c + 2 ≤ aS M c := by omega
    have hbig : c * (P / c + 2) ≤ c * aS M c := Nat.mul_le_mul_left c hge2
    have hexp : c * (P / c + 2) = c * (P / c) + 2 * c := by ring
    omega
  exact le_trans (aS_mono M hic (by omega)) hac

/-- **Count bound (the achiever Hall content).** At most `r = P%c` of `aS 1,…,aS c` equal `b+1`
(`b = ⌊P/c⌋`): from `good i₀` at the least such index (sortedness ⟹ they form a suffix). -/
private theorem count_bp1_le (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    ((Finset.Icc 1 (cAch M)).filter
        (fun i => aS M i = Sprefix M (cAch M + 1) / cAch M + 1)).card
      ≤ Sprefix M (cAch M + 1) % cAch M := by
  set c := cAch M with hc
  obtain ⟨hc1, hcleL, hgood⟩ := cAch_spec M hL
  set P := Sprefix M (c + 1) with hP
  set b := P / c with hb
  set S := (Finset.Icc 1 c).filter (fun i => aS M i = b + 1) with hSdef
  rcases S.eq_empty_or_nonempty with hemp | hne
  · rw [hemp]; simp
  · -- least element i0 of S
    set i0 := S.min' hne with hi0def
    have hi0S : i0 ∈ S := S.min'_mem hne
    have hi0mem : 1 ≤ i0 ∧ i0 ≤ c := by
      have := Finset.mem_filter.mp hi0S; exact Finset.mem_Icc.mp this.1
    have hi0val : aS M i0 = b + 1 := (Finset.mem_filter.mp hi0S).2
    -- sortedness: every i in [i0, c] is in S (aS i = b+1)
    have hsuffix : ∀ i, i0 ≤ i → i ≤ c → aS M i = b + 1 := by
      intro i hi0i hic
      have hge : aS M i0 ≤ aS M i := aS_mono M hi0i (by omega)
      rw [hi0val] at hge
      have hle : aS M i ≤ b + 1 := aS_le_bp1 M hL (by omega) hic
      omega
    -- so S = Icc i0 c, card = c − i0 + 1
    have hScard : S.card = c - i0 + 1 := by
      rw [show S = Finset.Icc i0 c from ?_, Nat.card_Icc]
      · omega
      · apply Finset.ext; intro i
        simp only [hSdef, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hi1, hic⟩, hival⟩
          refine ⟨S.min'_le i ?_, hic⟩
          rw [hSdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi1, hic⟩, hival⟩
        · rintro ⟨hi0i, hic⟩
          exact ⟨⟨by omega, hic⟩, hsuffix i hi0i hic⟩
    -- good i0: i0·(b+1) ≤ Sprefix(i0+1) + i0 − 1 ⟹ Sprefix(i0+1) ≥ i0·b + 1
    have hgi0 := hgood i0 (by omega) hi0mem.1
    rw [hi0val] at hgi0
    have hexpi0 : i0 * (b + 1) = i0 * b + i0 := by ring
    have hSi0 : i0 * b + 1 ≤ Sprefix M (i0 + 1) := by omega
    -- Sprefix(i0+1) = P − ∑_{i0+1}^c aS = P − (c−i0)(b+1) [suffix all b+1]
    have htailsum : ∑ i ∈ Finset.Ico (i0 + 1) (c + 1), aS M i = (c - i0) * (b + 1) := by
      rw [show (∑ i ∈ Finset.Ico (i0 + 1) (c + 1), aS M i)
            = ∑ _i ∈ Finset.Ico (i0 + 1) (c + 1), (b + 1) from
          Finset.sum_congr rfl (fun i hi => by
            rw [Finset.mem_Ico] at hi; exact hsuffix i (by omega) (by omega))]
      rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, show c + 1 - (i0 + 1) = c - i0 by omega]
    have hPsplit : P = Sprefix M (i0 + 1) + (c - i0) * (b + 1) := by
      rw [← htailsum, hP, Sprefix, Sprefix,
        ← Finset.sum_range_add_sum_Ico (fun i => aS M i) (by omega : i0 + 1 ≤ c + 1)]
    -- combine: P ≥ i0·b+1 + (c−i0)(b+1); P = cb + r ⟹ r ≥ c−i0+1 = card
    have hPdm : P = c * b + P % c := (Nat.div_add_mod P c).symm
    rw [hScard]
    -- (c−i0)(b+1) = (c−i0)·b + (c−i0); i0·b + (c−i0)·b = c·b (i0 ≤ c)
    have hexp : (c - i0) * (b + 1) = (c - i0) * b + (c - i0) := by ring
    have hcb : i0 * b + (c - i0) * b = c * b := by
      rw [← Nat.add_mul]; congr 1; omega
    omega

/-- `Sprefix M (c+1) ≥ Sprefix M (i+1) + (c−i)·aS M i` for `i ≤ c ≤ L`: the tail widths `a_{i+1..c}`
each dominate `a_i` (aS monotone). -/
private theorem Sprefix_tail_ge (M : Fin (L + 1) → ℕ) (i c : ℕ) (hic : i ≤ c) (hcL : c ≤ L) :
    Sprefix M (i + 1) + (c - i) * aS M i ≤ Sprefix M (c + 1) := by
  have hsplit : Sprefix M (c + 1)
      = Sprefix M (i + 1) + ∑ k ∈ Finset.Ico (i + 1) (c + 1), aS M k := by
    rw [Sprefix, Sprefix, ← Finset.sum_range_add_sum_Ico (fun k => aS M k) (by omega : i + 1 ≤ c + 1)]
  have htail : (c - i) * aS M i ≤ ∑ k ∈ Finset.Ico (i + 1) (c + 1), aS M k := by
    rw [show (c - i) * aS M i = ∑ _k ∈ Finset.Ico (i + 1) (c + 1), aS M i from by
      rw [Finset.sum_const, Nat.card_Ico]; ring_nf; rw [Nat.mul_comm]; congr 1; omega]
    apply Finset.sum_le_sum; intro k hk; rw [Finset.mem_Ico] at hk
    exact aS_mono M (by omega) (by omega)
  omega

/-- **Shared good-`c` core** (used by both the band `qFM_band` and the Dom precondition's `B2`):
`c·aS M i ≤ Sprefix M (c+1) + (i−1)` for `1 ≤ i ≤ c = cAch M`. From `goodAch i` + `Sprefix_tail_ge`;
the same `goodAch`-family as `count_bp1_le`. -/
private theorem good_floor_core (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) {i : ℕ} (hi1 : 1 ≤ i)
    (hic : i ≤ cAch M) :
    cAch M * aS M i ≤ Sprefix M (cAch M + 1) + (i - 1) := by
  set c := cAch M with hc
  obtain ⟨hc1, hcleL, hgood⟩ := cAch_spec M hL
  -- goodAch i: i·aS_i ≤ Sprefix(i+1) + i − 1
  have hgi := hgood i (by omega) hi1
  -- tail: Sprefix(c+1) ≥ Sprefix(i+1) + (c−i)·aS_i
  have htail := Sprefix_tail_ge M i c hic hcleL
  -- combine: c·aS_i = i·aS_i + (c−i)·aS_i ≤ [Sprefix(i+1)+i−1] + [Sprefix(c+1)−Sprefix(i+1)]
  have hexp : c * aS M i = i * aS M i + (c - i) * aS M i := by
    rw [← Nat.add_mul]; congr 1; omega
  omega

/-- **Lower-fit guard** `smallestK m (Yvec) ≤ Sprefix M (m+1)` (`m ≤ L`). `m > c`: equality
(`Yvec_prefix`); `m ≤ c`: the complement `∑ tail ≤ (c−m)b +
min(r,c−m)` from `aS_le_bp1` + `count_bp1_le`. The greedy non-emptiness' lower-fit. -/
private theorem Yvec_lowerfit (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) (m : ℕ) (hm : m ≤ L) :
    smallestK L m (Yvec M (cAch M)) ≤ (Sprefix M (m + 1) : ℤ) := by
  set c := cAch M with hc
  obtain ⟨hc1, hcleL, hgood⟩ := cAch_spec M hL
  set P := Sprefix M (c + 1) with hP
  set b := P / c with hb
  set r := P % c with hr
  rw [smallestK_of_monotone L m (Yvec M c) (Yvec_monotone M hL) hm]
  have hpre := Yvec_prefix M hL m hm
  rw [← hc] at hpre
  rw [hpre]
  by_cases hmc : m ≤ c
  · rw [if_pos hmc]
    -- complement: tail = ∑_{i=m+1}^c aS i ≤ (c−m)b + min(r,c−m); Sprefix(m+1) = P − tail
    have hrlt : r < c := Nat.mod_lt _ hc1
    -- count of b+1 in [m+1,c] ≤ min(r, c−m)
    set cnt := ((Finset.Icc (m + 1) c).filter (fun i => aS M i = b + 1)).card with hcnt
    have hcnt_le_cm : cnt ≤ c - m := by
      rw [hcnt]
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Nat.card_Icc]; omega
    have hcnt_le_r : cnt ≤ r := by
      refine le_trans ?_ (count_bp1_le M hL)
      rw [hcnt]
      apply Finset.card_le_card
      apply Finset.filter_subset_filter
      intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
    -- tail ≤ (c−m)·b + cnt  (each aS i ≤ b+1 = b + [aS i = b+1])
    have htail_le : ∑ i ∈ Finset.Icc (m + 1) c, aS M i ≤ (c - m) * b + cnt := by
      have hpoint : ∀ i ∈ Finset.Icc (m + 1) c, aS M i ≤ b + (if aS M i = b + 1 then 1 else 0) := by
        intro i hi; rw [Finset.mem_Icc] at hi
        have hb1 : aS M i ≤ b + 1 := by
          have := aS_le_bp1 M hL (show 1 ≤ i by omega) hi.2; rw [← hP, ← hb] at this; exact this
        split_ifs with h <;> omega
      refine le_trans (Finset.sum_le_sum hpoint) ?_
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul,
        show c + 1 - (m + 1) = c - m by omega]
      have hboole : ∑ i ∈ Finset.Icc (m + 1) c, (if aS M i = b + 1 then 1 else 0) = cnt := by
        rw [hcnt, Finset.card_filter]
      omega
    -- Sprefix(m+1) = P − tail
    have hSpre : Sprefix M (m + 1) + ∑ i ∈ Finset.Icc (m + 1) c, aS M i = P := by
      rw [hP, Sprefix, Sprefix]
      rw [show Finset.Icc (m + 1) c = Finset.Ico (m + 1) (c + 1) from by
        ext i; rw [Finset.mem_Icc, Finset.mem_Ico]; omega]
      rw [← Finset.sum_range_add_sum_Ico (fun i => aS M i) (by omega : m + 1 ≤ c + 1)]
    -- assemble: target balanced-prefix ≤ Sprefix(m+1), as ℤ
    have hPdm : P = c * b + r := (Nat.div_add_mod P c).symm
    have hmb : m * b + (c - m) * b = c * b := by rw [← Nat.add_mul]; congr 1; omega
    have hcast : (m : ℤ) * (b : ℤ) + max 0 ((m : ℤ) + (r : ℤ) - (c : ℤ))
        ≤ ((Sprefix M (m + 1) : ℕ) : ℤ) := by
      rcases Nat.lt_or_ge (m + r) c with hlt | hge
      · -- m+r<c ⟹ max=0; mb ≤ Sprefix(m+1) (cnt ≤ r)
        rw [max_eq_left (by push_cast; omega)]
        have hnat : m * b ≤ Sprefix M (m + 1) := by omega
        have : ((m * b : ℕ) : ℤ) ≤ ((Sprefix M (m + 1) : ℕ) : ℤ) := by exact_mod_cast hnat
        push_cast at this; linarith
      · -- m+r≥c ⟹ max=m+r−c; cnt ≤ c−m; mb+(m+r−c) ≤ Sprefix(m+1)
        rw [max_eq_right (by push_cast; omega)]
        have hnat : m * b + (m + r - c) ≤ Sprefix M (m + 1) := by omega
        have hgec : c ≤ m + r := by omega
        have : ((m * b + (m + r - c) : ℕ) : ℤ) ≤ ((Sprefix M (m + 1) : ℕ) : ℤ) := by
          exact_mod_cast hnat
        rw [Nat.cast_add, Nat.cast_sub hgec] at this; push_cast at this; linarith
    exact hcast
  · rw [if_neg hmc]

/-- Corridor-feasibility of an ordering `q : ℕ → ℤ`: the telescoped `uTel` is nonneg, ends at `0`,
weakly-decreasing, and within `admBound`. Exactly `telescope M q ∈ Adm M` (D2). -/
def QFeas (M : Fin (L + 1) → ℕ) (q : ℕ → ℤ) : Prop :=
  (∀ j, 0 ≤ uTel M q j) ∧ uTel M q L = 0 ∧
    (∀ j : Fin L, uTel M q ((j : ℕ) + 1) ≤ uTel M q (j : ℕ)) ∧
    (∀ j : Fin L, uTel M q ((j : ℕ) + 1) ≤ (admBound M j : ℤ))

/-- `Tstar M q : Fin L → ℕ`, the admissible point telescoped from a feasible ordering `q`
(`Tstar j = uTel(j+1)`, faithful since `uTel ≥ 0`). -/
noncomputable def Tstar (M : Fin (L + 1) → ℕ) (q : ℕ → ℤ) (j : Fin L) : ℕ :=
  (uTel M q ((j : ℕ) + 1)).toNat

/-- A feasible ordering's `Tstar` is admissible. -/
private theorem Tstar_mem_Adm (M : Fin (L + 1) → ℕ) (q : ℕ → ℤ) (hL : 1 ≤ L) (hq : QFeas M q) :
    Tstar M q ∈ Adm M := by
  obtain ⟨hnn, hlast, hanti, hbound⟩ := hq
  have hTval : ∀ j : Fin L, (Tstar M q j : ℤ) = uTel M q ((j : ℕ) + 1) := fun j => by
    rw [Tstar, Int.toNat_of_nonneg (hnn _)]
  rw [Adm, Finset.mem_filter]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]; intro j; rw [Finset.mem_range]
    have := hbound j; rw [← hTval j] at this
    have : (Tstar M q j : ℤ) ≤ (admBound M j : ℤ) := this
    have h2 : Tstar M q j ≤ admBound M j := by exact_mod_cast this
    omega
  · intro j; have := hbound j; rw [← hTval j] at this; exact_mod_cast this
  · intro i j hij
    -- weakly decreasing T_j ≤ T_i : uTel is antitone (from hanti, chained)
    have key : ∀ a b : ℕ, a ≤ b → b < L + 1 → uTel M q b ≤ uTel M q a := by
      intro a b hab hbL
      induction b with
      | zero => rw [show a = 0 by omega]
      | succ n ih =>
        rcases Nat.lt_or_ge a (n + 1) with h | h
        · have hstep : uTel M q (n + 1) ≤ uTel M q n := hanti ⟨n, by omega⟩
          exact le_trans hstep (ih (by omega) (by omega))
        · rw [show a = n + 1 by omega]
    have hle : uTel M q ((j : ℕ) + 1) ≤ uTel M q ((i : ℕ) + 1) :=
      key ((i : ℕ) + 1) ((j : ℕ) + 1) (by exact Nat.add_le_add_right hij 1) (by omega)
    rw [← hTval i, ← hTval j] at hle; exact_mod_cast hle
  · intro j hj
    have : (Tstar M q j : ℤ) = uTel M q ((j : ℕ) + 1) := hTval j
    rw [show ((j : ℕ) + 1) = L by omega] at this
    rw [hlast] at this
    have : Tstar M q j = 0 := by exact_mod_cast this
    exact this

/-- **A1 upper bound (D, value at achiever).** Given a feasible ordering `q` whose `Fin L` values
permute `Yvec`, `2·Mval M (Tstar M q) = ∑Yvec² − ∑M²` (via D1 `edgeQ_telescope` +
`edge_identity` + multiset-symmetry of `∑·²`). The upper-bound witness value. -/
private theorem Mval_Tstar (M : Fin (L + 1) → ℕ) (q : ℕ → ℤ) (hL : 1 ≤ L) (hq : QFeas M q)
    (σ : Equiv.Perm (Fin L)) (hperm : ∀ j : Fin L, q (j : ℕ) = Yvec M (cAch M) (σ j)) :
    2 * Mval M (Tstar M q) = (∑ j : Fin L, (Yvec M (cAch M) j) ^ 2)
      - ∑ i : Fin (L + 1), ((M i : ℤ)) ^ 2 := by
  obtain ⟨hnn, hlast, hanti, hbd⟩ := hq
  have hTmem := Tstar_mem_Adm M q hL ⟨hnn, hlast, hanti, hbd⟩
  have hlastT : ∀ j : Fin L, j.val = L - 1 → Tstar M q j = 0 := by
    rw [Adm, Finset.mem_filter] at hTmem; exact hTmem.2.2.2
  have hTval : ∀ j : Fin L, (Tstar M q j : ℤ) = uTel M q ((j : ℕ) + 1) := fun j => by
    rw [Tstar, Int.toNat_of_nonneg (hnn _)]
  have hedgeQ : ∀ j : Fin L, edgeQ M (Tstar M q) (j : ℕ) = q (j : ℕ) :=
    fun j => edgeQ_telescope M q hnn hlast (Tstar M q) hTval j
  have hid := edge_identity M (Tstar M q) hL hlastT
  have hqsq : ∑ j ∈ Finset.range L, edgeQ M (Tstar M q) j ^ 2
      = ∑ j : Fin L, (q (j : ℕ)) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => edgeQ M (Tstar M q) j ^ 2) L]
    exact Finset.sum_congr rfl (fun j _ => by rw [hedgeQ j])
  have hMsq : ∑ i ∈ Finset.range (L + 1), Mseq M i ^ 2 = ∑ i : Fin (L + 1), ((M i : ℤ)) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => Mseq M i ^ 2) (L + 1)]
    exact Finset.sum_congr rfl (fun i _ => by unfold Mseq; rw [dif_pos i.isLt])
  -- ∑ q² = ∑ (Yvec ∘ σ)² = ∑ Yvec²  (Equiv.sum_comp)
  have hpermsq : ∑ j : Fin L, (q (j : ℕ)) ^ 2 = ∑ j : Fin L, (Yvec M (cAch M) j) ^ 2 := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [hperm j])]
    exact Equiv.sum_comp σ (fun j => (Yvec M (cAch M) j) ^ 2)
  rw [hid, hqsq, hMsq, hpermsq]

/-! ## A1 closing machinery (Route B: Rado–Gale achiever) + `lambdaCore_eq_clean`

**A1 (Lemma 3): `lambdaCore M = cleanCore` at the achiever `c`.** Statement frozen (rv-2). The
`∃ c` is the **achiever** (largest `c ∈ {1,…,L}` whose balanced split on the `c+1` smallest widths
is admissible), NOT a min/max over `c` (both `min_c`/`max_c` refuted: `[1,1,4]`, `[2,2,2]`).

**Banked machinery (green, axiom-clean, above).** The two novel lower-bound pieces are proven:
`smallestK_eqPad_le` (the corridor majorization, via `L` Karamata elementary transfers
`smallestK_pair_spread` + `Vseq`) and `stepB` (the balanced split maximises every `k`-smallest;
`smallestK_balancedSplit` gives its closed form `k·b + max(0,k+r−c)`). The padding bridge
`smallestK_edge_le_width` turns the majorization into the `Fin L` edge bound. The achiever
`cAch M` (largest `goodAch` index, `cAch_spec`) is banked. Engines: `sq_sum_le_of_sorted_prefix`,
`edge_identity`, `balancedSplit_sq_int`, `cleanCore_perm`.

**Remaining assembly (routed; expedition card `a1-achiever-design.md`).** `a = aSort M`,
`Sₙ = Sprefix M n`, `c = cAch M`, target `Y = balancedSplit(S_c,c) ⊕ (a_{c+1}…a_L)`:
- LOWER `lambdaCore ≥ cleanCore`: feed the per-`k` edge bound (`smallestK_edge_le_width` for `k>c`;
  F1 + `stepB` for `k≤c`) to `sq_sum_le_of_sorted_prefix` + `edge_identity`. Needs `Y`-sort facts.
- UPPER `lambdaCore ≤ cleanCore`: telescope `T*` for a corridor-feasible ordering `q*` of `Y` — then
  `edgeQ(M,T*) = q*` by construction, `T*∈Adm` by corridor↔Adm, and `2·Mval(T*) = ∑Y² − ∑M²`.
- VALUE `4·cleanCore c (sortedSmallest M c) = ∑Y² − ∑M²` closes the equality with both bounds. -/
/-- `uTel` as a telescoped prefix sum: `u_n = M⁰ + ∑_{j<n}(M⁽ʲ⁺¹⁾ − q_j)`. -/
private theorem uTel_eq_prefix (M : Fin (L + 1) → ℕ) (q : ℕ → ℤ) (n : ℕ) :
    uTel M q n = (M 0 : ℤ) + ∑ j ∈ Finset.range n, (Mseq M (j + 1) - q j) := by
  induction n with
  | zero => simp [uTel]
  | succ k ih => rw [uTel, ih, Finset.sum_range_succ]; ring

/-- `∑_{i<n+1} Mseq = M⁰ + ∑_{j<n} Mseq(j+1)` (split off the `0` term). -/
private theorem Mseq_prefix_succ (M : Fin (L + 1) → ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), Mseq M i = (M 0 : ℤ) + ∑ j ∈ Finset.range n, Mseq M (j + 1) := by
  rw [Finset.sum_range_succ' (fun i => Mseq M i) n]
  have hM0 : Mseq M 0 = (M 0 : ℤ) := by unfold Mseq; rw [dif_pos (by omega)]; rfl
  rw [hM0]; ring

/-- **QFeasible from a corridor-feasible assignment (the clause-algebra bridge).** A bijection
`q` of `Y` (extended by `0` past `L`) with the polymatroid prefix/per-position/suffix bounds yields
`QFeas M q`: prefix `⟹ uⁿ≥0`, total `⟹ uᴸ=0`, per-position `qⁿ≥M⁽ⁿ⁺¹⁾ ⟹ antitone`, suffix `⟹
uⁿ⁺¹≤admBound`. (All pp-verified 0/1360.) -/
private theorem QFeas_of_assignment (M : Fin (L + 1) → ℕ) (q : ℕ → ℤ)
    (hext : ∀ j, L ≤ j → q j = 0)
    (htot : ∑ j ∈ Finset.range L, q j = ∑ i ∈ Finset.range (L + 1), Mseq M i)
    (hpre : ∀ n, n ≤ L → ∑ j ∈ Finset.range n, q j ≤ ∑ i ∈ Finset.range (n + 1), Mseq M i)
    (hge : ∀ j : Fin L, Mseq M ((j : ℕ) + 1) ≤ q (j : ℕ))
    (hadm : ∀ j : Fin L, (∑ i ∈ Finset.range ((j : ℕ) + 2), Mseq M i) - (admBound M j : ℤ)
        ≤ ∑ i ∈ Finset.range ((j : ℕ) + 1), q i) :
    QFeas M q := by
  have hpast : ∀ i, L + 1 ≤ i → Mseq M i = 0 := by
    intro i hi; unfold Mseq; rw [dif_neg (by omega)]
  -- u_L = 0 first (used by the n>L nonneg case)
  have huL : uTel M q L = 0 := by
    rw [uTel_eq_prefix, Finset.sum_sub_distrib]
    have h := htot; rw [Mseq_prefix_succ] at h; linarith
  refine ⟨?_, huL, ?_, ?_⟩
  · -- u_n ≥ 0
    intro n
    rcases Nat.lt_or_ge n (L + 1) with hn | hn
    · rw [uTel_eq_prefix, Finset.sum_sub_distrib]
      have hp := hpre n (by omega); rw [Mseq_prefix_succ] at hp; linarith
    · -- n ≥ L+1: uTel n = uTel L = 0 (Mseq and q both 0 on [L, n))
      rw [uTel_eq_prefix]
      have hsplit : ∑ j ∈ Finset.range n, (Mseq M (j + 1) - q j)
          = ∑ j ∈ Finset.range L, (Mseq M (j + 1) - q j) := by
        rw [← Finset.sum_range_add_sum_Ico _ (show L ≤ n by omega)]
        have hz : ∑ j ∈ Finset.Ico L n, (Mseq M (j + 1) - q j) = 0 := by
          apply Finset.sum_eq_zero; intro j hj; rw [Finset.mem_Ico] at hj
          rw [hpast (j + 1) (by omega), hext j (by omega)]; ring
        rw [hz, add_zero]
      rw [hsplit]
      have h := huL; rw [uTel_eq_prefix] at h; linarith
  · -- antitone: u_{j+1} ≤ u_j ⟺ q_j ≥ M^{j+1}
    intro j
    rw [uTel_eq_prefix, uTel_eq_prefix, Finset.sum_range_succ]
    have := hge j; linarith
  · -- Ladm: u_{j+1} ≤ admBound j
    intro j
    rw [uTel_eq_prefix, Finset.sum_sub_distrib]
    have hp := hadm j
    rw [show (j : ℕ) + 2 = ((j : ℕ) + 1) + 1 by omega, Mseq_prefix_succ] at hp
    linarith

/-- `∑ sortedSmallest M c = Sprefix M (c+1)` (the `c+1` smallest widths sum to the prefix). -/
private theorem sum_sortedSmallest (M : Fin (L + 1) → ℕ) (c : ℕ) (hc : c ≤ L) :
    ∑ k : Fin (c + 1), sortedSmallest M c hc k = Sprefix M (c + 1) := by
  rw [Sprefix, ← Fin.sum_univ_eq_sum_range (fun i => aS M i) (c + 1)]
  apply Finset.sum_congr rfl
  intro k _
  rw [aS, dif_pos (by omega), sortedSmallest]
  congr 1

/-- **A1 close, given a corridor-feasible achiever ordering.** With `c = cAch M`, a `QFeas` ordering
`q` permuting `Yvec` closes the equality: upper bound via `Tstar`/`Mval_Tstar` + `Finset.inf'_le`,
lower bound via `two_Mval_ge` + `Finset.le_inf'`, value via `Yvec_value`. The engine (∃ such `q`)
is the only remaining piece. -/
private theorem close_of_feasible (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) (q : ℕ → ℤ) (hq : QFeas M q)
    (σ : Equiv.Perm (Fin L)) (hperm : ∀ j : Fin L, q (j : ℕ) = Yvec M (cAch M) (σ j)) :
    ∃ (c : ℕ) (hc : c ≤ L), 1 ≤ c ∧ lambdaCore M = cleanCore c (sortedSmallest M c hc) := by
  obtain ⟨hc1, hcleL, _⟩ := cAch_spec M hL
  set c := cAch M with hc
  refine ⟨c, hcleL, hc1, ?_⟩
  set D : ℤ := (∑ j : Fin L, (Yvec M c j) ^ 2) - ∑ i : Fin (L + 1), ((M i : ℤ)) ^ 2 with hD
  set I : ℤ := (Adm M).inf' (Adm_nonempty M) (Mval M) with hI
  -- T* achieves the value 2·Mval = D; the inf' is achieved at some T₀
  have hTadm : Tstar M q ∈ Adm M := Tstar_mem_Adm M q hL hq
  have hTval : 2 * Mval M (Tstar M q) = D := Mval_Tstar M q hL hq σ hperm
  obtain ⟨T₀, hT₀mem, hT₀eq⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
  -- upper: I ≤ Mval(Tstar) ⟹ 2I ≤ D ; lower: D ≤ 2·Mval T₀ = 2I
  have hub : 2 * I ≤ D := by
    have : I ≤ Mval M (Tstar M q) := Finset.inf'_le _ hTadm
    nlinarith [this, hTval]
  have hlb : D ≤ 2 * I := by
    have h0 := two_Mval_ge M T₀ hT₀mem hL
    rw [← hT₀eq] at h0; linarith [h0]
  have hID : 2 * I = D := le_antisymm hub hlb
  -- lambdaCore = ½·I ; cleanCore = ¼·D ; with 2I = D ⟹ equal
  have hlam : lambdaCore M = (1 / 2 : ℚ) * (I : ℤ) := by rw [lambdaCore, hI]
  -- cleanCore c (sortedSmallest) = ¼·D
  have hclean : cleanCore c (sortedSmallest M c hcleL) = (1 / 4 : ℚ) * (D : ℚ) := by
    rw [cleanCore]
    have hsum : ∑ k, sortedSmallest M c hcleL k = Sprefix M (c + 1) := sum_sortedSmallest M c hcleL
    simp only [hsum]
    rw [Yvec_value M c hcleL hc1] at hD
    rw [hD]; push_cast; ring
  rw [hlam, hclean]
  have : (2 : ℚ) * (I : ℚ) = (D : ℚ) := by exact_mod_cast hID
  rw [hc] at *
  linarith [this]

/-- The achiever-width list `[M¹,…,Mᴸ]` and pool `Y`-multiset feeding the BG engine. -/
noncomputable def Mwidths (M : Fin (L + 1) → ℕ) : List ℤ :=
  List.ofFn (fun j : Fin L => (M j.succ : ℤ))

/-- The achiever target multiset `Yvec` as a `Multiset ℤ` (the engine's pool). -/
noncomputable def Ymulti (M : Fin (L + 1) → ℕ) : Multiset ℤ :=
  (List.ofFn (Yvec M (cAch M)) : Multiset ℤ)

/-- The achiever ordering `q* = backwardGreedy Mwidths Y`, extended by junk `0` past `L`. -/
noncomputable def qStar (M : Fin (L + 1) → ℕ) : ℕ → ℤ :=
  fun i ↦ (BGEngine.backwardGreedy (Mwidths M) (Ymulti M)).getD i 0

/-- `Mwidths` has length `L`. -/
private theorem Mwidths_len (M : Fin (L + 1) → ℕ) : (Mwidths M).length = L := by
  rw [Mwidths, List.length_ofFn]

/-- `Mwidths[j] = M⁽ʲ⁺¹⁾ = Mseq M (j+1)`. -/
private theorem Mwidths_get (M : Fin (L + 1) → ℕ) (j : ℕ) (hj : j < L) :
    (Mwidths M)[j]'(by rw [Mwidths_len]; exact hj) = Mseq M (j + 1) := by
  simp only [Mwidths, List.getElem_ofFn]; unfold Mseq; rw [dif_pos (by omega)]; rfl

/-- The pool `Ymulti` has card `L`. -/
private theorem Ymulti_card (M : Fin (L + 1) → ℕ) : (Ymulti M).card = L := by
  rw [Ymulti, Multiset.coe_card, List.length_ofFn]

/-- **The achiever ordering is QFeasible + permutes `Yvec`** — given the engine precondition `Dom`
and the band. The easy clauses (`hext`/`htot`/`hpre`/`hge`) are discharged from the engine's perm +
`_ge`; the band `hadm` is the supplied achiever-structural input. -/
private theorem QFeas_qStar (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (hDom : BGEngine.Dom (Mwidths M) (Ymulti M))
    (hband : ∀ j : Fin L, (∑ i ∈ Finset.range ((j : ℕ) + 2), Mseq M i) - (admBound M j : ℤ)
        ≤ ∑ i ∈ Finset.range ((j : ℕ) + 1), qStar M i) :
    QFeas M (qStar M) ∧
      ∃ σ : Equiv.Perm (Fin L), ∀ j : Fin L, qStar M (j : ℕ) = Yvec M (cAch M) (σ j) := by
  set c := cAch M with hc
  set qList := BGEngine.backwardGreedy (Mwidths M) (Ymulti M) with hqL
  have hqlen : qList.length = L := by
    rw [hqL, BGEngine.backwardGreedy_length hDom, Mwidths_len]
  have hperm : (qList : Multiset ℤ) = Ymulti M := BGEngine.backwardGreedy_perm hDom
  -- qStar at j<L is the list element
  have hqget : ∀ j (hj : j < L), qStar M j = qList[j]'(by rw [hqlen]; exact hj) := by
    intro j hj; rw [qStar, ← hqL, List.getD_eq_getElem _ _ (by rw [hqlen]; exact hj)]
  -- hge: Mseq M (j+1) ≤ qStar M j  (engine _ge + Mwidths_get)
  have hge : ∀ j : Fin L, Mseq M ((j : ℕ) + 1) ≤ qStar M (j : ℕ) := by
    intro j
    have hjL : (j : ℕ) < L := j.isLt
    have hg := BGEngine.backwardGreedy_ge hDom (j : ℕ) (by rw [Mwidths_len]; exact hjL)
    rw [Mwidths_get M (j : ℕ) hjL] at hg
    rw [hqget (j : ℕ) hjL]; exact hg
  -- hext: qStar = 0 past L
  have hext : ∀ j, L ≤ j → qStar M j = 0 := by
    intro j hj; rw [qStar, ← hqL, List.getD_eq_default _ _ (by rw [hqlen]; exact hj)]
  -- htot: ∑_{j<L} qStar = ∑ M  (perm: ∑qList = ∑Ymulti = ∑Yvec = ∑M)
  have hYsum : (Ymulti M).sum = ∑ i : Fin (L + 1), (M i : ℤ) := by
    rw [Ymulti, Multiset.sum_coe, ← hc, List.sum_ofFn]
    exact sum_Yvec M hL
  have htot : ∑ j ∈ Finset.range L, qStar M j = ∑ i ∈ Finset.range (L + 1), Mseq M i := by
    have hqsum : ∑ j ∈ Finset.range L, qStar M j = qList.sum := by
      rw [← Fin.sum_univ_eq_sum_range (fun j ↦ qStar M j) L]
      rw [show (∑ j : Fin L, qStar M (j : ℕ))
            = ∑ j : Fin L, qList[(j : ℕ)]'(by rw [hqlen]; exact j.isLt) from
          Finset.sum_congr rfl (fun j _ ↦ hqget (j : ℕ) j.isLt)]
      rw [← List.sum_ofFn]; congr 1
      apply List.ext_getElem (by rw [List.length_ofFn]; exact hqlen.symm)
      intro n h1 h2; rw [List.getElem_ofFn]
    rw [hqsum, ← Multiset.sum_coe, hperm, hYsum]
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ Mseq M i) (L + 1)]
    exact (Finset.sum_congr rfl (fun i _ ↦ by unfold Mseq; rw [dif_pos i.isLt])).symm
  -- hpre: prefix_n ≤ S'_n  via suffix-complement (hge + htot)
  have hpre : ∀ n, n ≤ L → ∑ j ∈ Finset.range n, qStar M j
      ≤ ∑ i ∈ Finset.range (n + 1), Mseq M i := by
    intro n hn
    -- ∑_{j<n} q = ∑M − ∑_{n≤j<L} q ≤ ∑M − ∑_{n≤j<L} Mseq(j+1) = ∑_{i<n+1} Mseq
    have hsplit : ∑ j ∈ Finset.range L, qStar M j
        = (∑ j ∈ Finset.range n, qStar M j) + ∑ j ∈ Finset.Ico n L, qStar M j :=
      (Finset.sum_range_add_sum_Ico _ hn).symm
    have htail : ∑ j ∈ Finset.Ico n L, Mseq M (j + 1) ≤ ∑ j ∈ Finset.Ico n L, qStar M j := by
      apply Finset.sum_le_sum; intro j hj; rw [Finset.mem_Ico] at hj
      exact hge ⟨j, by omega⟩
    have hMtail : ∑ i ∈ Finset.range (L + 1), Mseq M i
        = (∑ i ∈ Finset.range (n + 1), Mseq M i) + ∑ j ∈ Finset.Ico n L, Mseq M (j + 1) := by
      rw [← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ L + 1 by omega)]
      congr 1
      rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr (by congr 1; omega)
      intro i _; congr 1; omega
    rw [htot] at hsplit
    linarith [hsplit, htail, hMtail]
  -- σ: qF and Yvec are perms of the same multiset ⟹ related by a permutation
  set qF : Fin L → ℤ := fun j ↦ qStar M (j : ℕ) with hqF
  have hqFmulti : (List.ofFn qF : Multiset ℤ) = (List.ofFn (Yvec M c) : Multiset ℤ) := by
    have hqFlist : List.ofFn qF = qList := by
      apply List.ext_getElem (by rw [List.length_ofFn]; exact hqlen.symm)
      intro n h1 h2
      rw [List.getElem_ofFn]
      exact hqget n (by rw [List.length_ofFn] at h1; exact h1)
    rw [hqFlist, hperm, Ymulti]
  -- equal multisets ⟹ equal sorted forms (the monotone arrangement is multiset-determined)
  have hmulti_sort : ∀ (f : Fin L → ℤ),
      (List.ofFn (f ∘ Tuple.sort f) : Multiset ℤ) = (List.ofFn f : Multiset ℤ) := by
    intro f
    rw [← Fin.univ_val_map, ← Fin.univ_val_map]
    conv_rhs => rw [← Multiset.map_univ_val_equiv (Tuple.sort f), Multiset.map_map]
  have hmono_eq : qF ∘ Tuple.sort qF = Yvec M c ∘ Tuple.sort (Yvec M c) := by
    rw [← List.ofFn_inj]
    have hs1 : (List.ofFn (qF ∘ Tuple.sort qF)).SortedLE :=
      List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort qF)
    have hs2 : (List.ofFn (Yvec M c ∘ Tuple.sort (Yvec M c))).SortedLE :=
      List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort (Yvec M c))
    have hp : List.Perm (List.ofFn (qF ∘ Tuple.sort qF))
        (List.ofFn (Yvec M c ∘ Tuple.sort (Yvec M c))) := by
      rw [← Multiset.coe_eq_coe, hmulti_sort qF, hmulti_sort (Yvec M c), hqFmulti]
    exact List.Perm.eq_of_sortedLE hs1 hs2 hp
  set σ : Equiv.Perm (Fin L) := (Tuple.sort qF).symm.trans (Tuple.sort (Yvec M c)) with hσ
  have hqFσ : ∀ j : Fin L, qF j = Yvec M c (σ j) := by
    intro j
    have := congrArg (fun f ↦ f ((Tuple.sort qF).symm j)) hmono_eq
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
    rw [hσ]; simp only [Equiv.trans_apply]; rw [← this]
  exact ⟨QFeas_of_assignment M (qStar M) hext htot hpre hge hband, σ,
    fun j ↦ by rw [hqF] at hqFσ; exact hqFσ j⟩

/-- **A1 (Lemma 3, the headline arithmetic).** `lambdaCore M = cleanCore` at the achiever `cAch M`.
The proof is fully assembled: the achiever ordering `qStar` is corridor-feasible and permutes `Yvec`
(`QFeas_qStar`), which feeds `close_of_feasible`. Three inputs remain open:
* `hL : 1 ≤ L` — **STATEMENT-FIDELITY HOLE, not a pp-hall certificate.** The conclusion
  `∃ c, c ≤ L ∧ 1 ≤ c ∧ …` is *unsatisfiable at `L = 0`* (no `c` with `c ≤ 0 ∧ 1 ≤ c`), so the
  statement is false there; `1 ≤ L` is genuinely required and is *not* a hypothesis. Fix: add
  `(hL : 1 ≤ L)` to the signature (the whole engine — `close_of_feasible`, `cAch_spec` — already
  assumes it). Flagged for the controller — do not discharge from nothing.
* `hDom` — the BG-engine precondition (`Dom`), a pp-hall certificate (pending).
* `hband` — the admissibility band on `qStar`'s prefix sums, a pp-hall certificate (pending). -/
theorem lambdaCore_eq_clean (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    ∃ (c : ℕ) (hc : c ≤ L), 1 ≤ c ∧ lambdaCore M = cleanCore c (sortedSmallest M c hc) := by
  -- pp-hall certificate (pending): the BG-engine domination precondition.
  have hDom : BGEngine.Dom (Mwidths M) (Ymulti M) := by sorry
  -- pp-hall certificate (pending): the admissibility band on qStar's prefix sums.
  have hband : ∀ j : Fin L, (∑ i ∈ Finset.range ((j : ℕ) + 2), Mseq M i) - (admBound M j : ℤ)
      ≤ ∑ i ∈ Finset.range ((j : ℕ) + 1), qStar M i := by sorry
  obtain ⟨hq, σ, hperm⟩ := QFeas_qStar M hL hDom hband
  exact close_of_feasible M hL (qStar M) hq σ hperm

end DLNFibre.DLN.RLCT
