import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.Lambda
import Mathlib.MeasureTheory.Function.Jacobian

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
    (hderiv : ∀ m ∈ Eᶜ, HasFDerivAt π (Dπ m) m) :
    weightedThreshold F φ {wstar}
      = weightedThreshold (F ∘ π) (fun m => φ (π m) * |(Dπ m).det|) (π ⁻¹' {wstar}) := by
  sorry

/-- **S1.3 (Lemma 1, ideal invariance core).** The RLCT is invariant under multiplying `F` by a unit
`u` bounded away from `0` near `w*` (`0 < a ≤ |u| ≤ b` on a neighbourhood) — the operative content
of "depends only on the ideal" (and what reduces `λ(⟨Fᵢ⟩)` to `λ(∑Fᵢ²)`, and removes the bump and
`Σ_X`). Non-vacuous: it equates the RLCT of `u·F` to that of `F`. -/
theorem rlct_unit_invariant (H : Fin (L + 1) → ℕ) (F u : Params H → ℝ) (wstar : Params H)
    (a b : ℝ) (ha : 0 < a)
    (hu : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, a ≤ |u w| ∧ |u w| ≤ b) :
    rlctAt H (fun w => u w * F w) wstar = rlctAt H F wstar := by
  sorry

/-- **S1.4 (germ-locality / φ-independence).** The RLCT depends only on the germ of `F` at `w*`: if
`F` and `G` agree on a neighbourhood of `w*`, their RLCTs are equal. This is the bump-independence
content (the threshold is determined by the local behaviour near `w*`) and is what lets S2's
bump-free monomial conclusion connect to the bumped resolution. Non-vacuous: it equates `rlctAt F`
and `rlctAt G` from a local-agreement hypothesis. -/
theorem rlct_germ_local (H : Fin (L + 1) → ℕ) (F G : Params H → ℝ) (wstar : Params H)
    (hFG : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, F w = G w) :
    rlctAt H F wstar = rlctAt H G wstar := by
  sorry

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
Non-vacuous: equates the joint RLCT to `n/2` plus the block RLCT. -/
theorem rlct_additive_smooth_block {n : ℕ}
    {Y : Type*} [MeasureSpace Y] [TopologicalSpace Y] (G : Y → ℝ) (y0 : Y) :
    rlctAtOn (fun p : (Fin n → ℝ) × Y => (∑ i, p.1 i ^ 2) + G p.2 ^ 2) (0, y0)
      = (n : ENNReal) / 2 + rlctAtOn (fun y => G y ^ 2) y0 := by
  sorry

/-! ## L1 / L2 — block elimination + product reduction (design-spec §8) -/

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
  sorry

/-- **The deepest singular point** (Aoyagi 2013, the inf-achiever; Rung-0c FLAG, load-bearing).
`w` is *deepest* when it lies in the fibre **and** every **partial product**
`∏_{s<k} A⁽ˢ⁾ = prodAux H w k` sits at the **minimal rank consistent with the fibre** —
`rank (prodAux H w k) = min r (min_{i ≤ k} H⁽ⁱ⁾)` — i.e. each prefix is collapsed as far as the path
widths and the rank-`r` target allow (Aoyagi's "all layers at the minimal rank `r`", expressed on
the partial products so it pins the *whole* product chain, not just per-layer ranks). This is the
point whose local RLCT is **maximal** over the fibre — so the global infimum of the *learning
coefficient* `λ` is attained there (smaller `λ` ⇔ more singular ⇔ deeper). The local RLCT genuinely
varies over the fibre (rv-2's witness: for `(2,2,2)` a milder optimal point gives `2 ≠ 3/2`), so L2
must be keyed to *this* point, not every optimal one — that is exactly why D1 exists. This
partial-product
characterization is the one under which **both** D1 (deepest attains the inf) and L2 (`rlctAt =
aoyagiLambda`) hold. -/
def IsDeepest (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (w : Params H) : Prop :=
  w ∈ optimalSet H B ∧
    ∀ (k : ℕ) (hk : k < L + 1),
      (prodAux H w k hk).rank = min r ((Finset.Iic (⟨k, hk⟩ : Fin (L + 1))).inf'
        ⟨⟨k, hk⟩, Finset.mem_Iic.2 le_rfl⟩ H)

/-- **L2 (Theorem 3, product reduction).** The local RLCT of the loss **at a deepest point** splits
as the regular-part shift `[−r²+r(H¹+Hᴸ⁺¹)]/2` plus the singular-core `lambdaCore` over the reduced
widths `M⁽ˢ⁾ = H⁽ˢ⁾ − r`: it equals `aoyagiLambda H r` (cast to `ℝ≥0∞`). (Rung-0c FLAG: the old
statement quantified over *every* optimal `wstar` — an **over-claim**; the local RLCT varies over
the fibre, equalling the closed form only at the deepest point. Re-keyed to `IsDeepest`.)
Non-vacuous: it equates the local RLCT at a deepest point to the closed form. -/
theorem product_reduction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (w : Params H)
    (hw : IsDeepest H r B w) :
    rlctAt H (dlnLoss H B) w = ENNReal.ofReal (aoyagiLambda H r) := by
  sorry

/-! ## D1 — reduction to the deepest singular point (Aoyagi 2013, Thm 4; design-spec §7.2) -/

/-- **D1 (Theorem 4).** The global infimum of the local RLCT over the optimal set is **attained at a
deepest singular point** (`IsDeepest`): there exists a deepest `w` that is optimal and whose local
RLCT realises the infimum. This turns the headline's `⨅ w ∈ optimalSet, rlctAt` into the local RLCT
at one identified point. (Rung-0c FLAG: the old statement asserted only `∃ wstar ∈ optimalSet`
attaining the inf — an **under-claim** that did not identify the attainer as *deepest*, so it could
not feed the re-keyed L2; now it certifies `IsDeepest`.) Non-vacuous: it both exhibits a deepest
attainer and equates the inf to its local RLCT. -/
theorem deepest_point_reduction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r) :
    ∃ w, IsDeepest H r B w ∧
      (⨅ v ∈ optimalSet H B, rlctAt H (dlnLoss H B) v) = rlctAt H (dlnLoss H B) w := by
  sorry

/-! ## R1 — the resolution: explicit charts → normal-crossing form (the mountain; design-spec §8) -/

/-- **R1 (the resolution).** Aoyagi's recursive blow-up as explicit coordinate charts: a finite
chart family with monomial pullback `F∘φᵢ = unitᵢ·∏|uⱼ|^{2k_{i,j}}` and Jacobian-monomial
`|det Dφᵢ|·(bump∘φᵢ) = posᵢ·∏|uⱼ|^{h_{i,j}}`, whose images cover a nbhd of `w* ∩ {F=0}`, and whose
exponents `(k_{i,j}, h_{i,j})` range over exactly the admissible cone `Adm` (so the chart minima
realise `min_T M(T)`). Stated as the existence of chart-exponent data whose monomial thresholds
reconstruct `rlctAt F`; the explicit charts are R1's obligation (design-spec §9 item 3: the R1↔Adm
match).

Rung-0c FLAG (precondition): the value-match `rlctAt F = ⨅ monomialThreshold` is the **standard
RLCT** only for `F` real-analytic and `≢ 0` near `w*` (design-spec §2); without it the
`⨅`-existential fails for pathological `F`. We add the stateable, load-bearing `≢ 0 near w*` half
(`hFne`). The real-analyticity half is **automatic for every instantiation** — R1 is applied only to
`dlnLoss H B`, a polynomial — and is *not* added as an `AnalyticAt` hypothesis because `Params H`
carries no `NormedSpace ℝ` instance (a `def` over `Matrix`, which has no canonical norm), so
`AnalyticAt ℝ F` is not Mathlib-stateable here; pinning it as an unsatisfiable instance hypothesis
would re-vacuate the theorem. Flagged for the controller (see report). -/
theorem resolution_charts (H : Fin (L + 1) → ℕ) (F : Params H → ℝ) (wstar : Params H)
    (hFne : ∀ U ∈ 𝓝 wstar, ∃ w ∈ U, F w ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
      rlctAt H F wstar = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
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

/-- **A1 (Lemma 3, the clean closed form).** The core `lambdaCore M = ½·min_T M(T)` admits a
clean-form representation: there exist `ℓ` and reduced widths `m` with
`lambdaCore M = cleanCore ℓ m = ¼(Σqᵢ²−Σmₖ²)`, proven via the integer-balanced-split minimum
(design-spec §4.3). (Rung-0c nit: the docstring formerly named `(ℓ,m)` as "the Def-3 selection — the
`ℓ+1` smallest of `M`", but the **existential does not bind** `(ℓ,m)` to that selection — it asserts
only that *some* `(ℓ,m)` works. The Def-3 identification of *which* `(ℓ,m)` is the proof's content,
not part of the statement; docstring softened to match.) Non-vacuous: equates `lambdaCore M` to an
explicit `cleanCore`. -/
theorem lambdaCore_eq_clean (M : Fin (L + 1) → ℕ) :
    ∃ (ℓ : ℕ) (m : Fin (ℓ + 1) → ℕ), lambdaCore M = cleanCore ℓ m := by
  sorry

/-- **A1 (clean = printed).** The clean core form equals the printed Theorem-2 expression — a finite
arithmetic identity in `m, ℓ` (`a = P mod ℓ`), holding for **every** `m` and every `ℓ > 0`. (Rung-0c
nit: the docstring formerly called this "Def-3 regime"-scoped, but the identity is **universal** in
`(m, ℓ)` with `0 < ℓ` — it does not depend on any Def-3 selection; rv-2 verified 9324 cases.
Docstring corrected.) Not part of the headline. Non-vacuous: it equates the two forms. -/
theorem clean_eq_printed (ℓ : ℕ) (m : Fin (ℓ + 1) → ℕ) (hℓ : 0 < ℓ) :
    cleanCore ℓ m = printedCore ℓ m := by
  sorry

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
target `B` of rank `r`. Assembled: D1 (→ deepest point) ▸ L2 (→ reg + core) ▸ R1 (→ charts) ▸ S2
(→ min ratio) ▸ A1 (→ clean form = `aoyagiLambda`). -/
theorem aoyagi_learning_coefficient (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  -- assemble: D1 (→ a deepest point attaining the inf) ▸ L2 (→ closed form at the deepest point).
  obtain ⟨w, hdeep, hinf⟩ := deepest_point_reduction H r B hB
  rw [hinf]
  exact product_reduction H r B w hdeep

end DLNFibre.DLN.RLCT
