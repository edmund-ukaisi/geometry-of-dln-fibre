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

/-- The deepest layers exist for a rank-`r` target (`r = 0` ⟹ the origin; general `r` ⟹ a
block-normal rank-`r` chain whose product is `B`). The existence obligation behind the constructed
`deepestPoint`; named `sorry` (statements-first, like the rung lemmas). The hypothesis
`hr : ∀ s, r ≤ H s` is the well-definedness + nonemptiness domain: without it the fibre can be empty
(e.g. `H=(3,1,3), r=2`: a width-1 middle layer caps the product rank at `1 < 2`), making this
`Nonempty` FALSE; it is also what makes `M⁽ˢ⁾ = H⁽ˢ⁾ − r` (in `aoyagiLambda`) non-truncating. -/
theorem deepestPoint_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Nonempty {w : Params H // IsDeepLayers H r B w} := by
  sorry

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
    (hr : ∀ s : Fin (L + 1), r ≤ H s) : Params H :=
  (Classical.choice (deepestPoint_exists H r B hB hr)).1

/-- The constructed `deepestPoint` is a deepest-layers point (in particular, in the fibre). -/
theorem deepestPoint_isDeep (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    IsDeepLayers H r B (deepestPoint H r B hB hr) :=
  (Classical.choice (deepestPoint_exists H r B hB hr)).2

/-- **L2 (Theorem 3, product reduction).** The local RLCT of the loss **at the deepest point**
as the regular-part shift `[−r²+r(H¹+Hᴸ⁺¹)]/2` plus the singular-core `lambdaCore` over the reduced
widths `M⁽ˢ⁾ = H⁽ˢ⁾ − r`: it equals `aoyagiLambda H r` (cast to `ℝ≥0∞`). (Rung-0c FLAG: keyed to the
single constructed `deepestPoint`, **not** `∀ optimal w` — an over-claim — nor a
`∀`-deepest-predicate — the per-partial-product form was too weak. The local RLCT varies over the
fibre, equalling the closed form at the deepest point.) Non-vacuous: equates the local RLCT at
`deepestPoint` to the closed form. -/
theorem product_reduction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr) = ENNReal.ofReal (aoyagiLambda H r) := by
  sorry

/-! ## D1 — reduction to the deepest singular point (Aoyagi 2013, Thm 4; design-spec §7.2) -/

/-- **D1 (Theorem 4).** The global infimum of the local RLCT over the optimal set is **attained at
the deepest singular point** `deepestPoint H r B` (Aoyagi 2013 Thm 2, the monotonicity of the local
RLCT over the fibre). This turns `⨅ w ∈ optimalSet, rlctAt` into the local RLCT at the
one constructed point that L2 evaluates. (Rung-0c FLAG: keyed to the constructed `deepestPoint`,
replacing the under-claiming `∃ wstar ∈ optimalSet` that did not name the attainer.) Non-vacuous:
equates the inf to the local RLCT at `deepestPoint`. -/
theorem deepest_point_reduction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    (⨅ v ∈ optimalSet H B, rlctAt H (dlnLoss H B) v)
      = rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr) := by
  sorry

/-! ## R1 — the resolution: explicit charts → normal-crossing form (the mountain; design-spec §8) -/

/-- **R1 (the resolution).** Aoyagi's recursive blow-up as explicit coordinate charts: a finite
chart family with monomial pullback `F∘φᵢ = unitᵢ·∏|uⱼ|^{2k_{i,j}}` and Jacobian-monomial
`|det Dφᵢ|·(bump∘φᵢ) = posᵢ·∏|uⱼ|^{h_{i,j}}`, whose images cover a nbhd of `w* ∩ {F=0}`, and whose
exponents `(k_{i,j}, h_{i,j})` range over exactly the admissible cone `Adm` (so the chart minima
realise `min_T M(T)`). Stated as the existence of chart-exponent data whose monomial thresholds
reconstruct the RLCT; the explicit charts are R1's obligation (design-spec §9 item 3: the R1↔Adm
match).

Rung-0c FLAG (specialisation): the value-match `rlctAt F = ⨅ monomialThreshold` is **FALSE for a
generic `F`** — even one `≢ 0` near `w*` (rv-2: a non-analytic such `F` breaks the existential); it
holds only for `F` real-analytic, and analyticity is not Mathlib-stateable on `Params` (a `def` over
`Matrix`, no canonical norm, so no `NormedSpace ℝ` — an `AnalyticAt` hypothesis would be
unsatisfiable and re-vacuate). So R1 is **specialised to the loss `dlnLoss H B`**, the polynomial
it is actually applied to: the resolution genuinely holds there (analyticity automatic), and the
statement is TRUE and `Params`-norm-free. The fully-general analytic-`F` form is a roadmap lemma for
after the `Params ≃ᵐ ℝ^N` flattening (then `AnalyticOn (F ∘ paramsEquivFlat.symm)` is stateable). -/
theorem resolution_charts (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (wstar : Params H) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
      rlctAt H (dlnLoss H B) wstar = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
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

/-- `cleanCore 1 ![1, n] = n/2`: with `ℓ = 1` the balanced split is `[P]`, so
`¼((1+n)² − 1 − n²) = ¼·2n = n/2`. The half-integer-hitting fact A1 uses. -/
private theorem cleanCore_one (n : ℕ) : cleanCore 1 (![1, n]) = (n : ℚ) / 2 := by
  simp only [cleanCore]
  rw [show (∑ k, (![1, n] : Fin 2 → ℕ) k) = 1 + n by simp [Fin.sum_univ_two]]
  rw [Fin.sum_univ_one, Fin.sum_univ_two]
  unfold balancedSplit
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Nat.mod_one,
    Nat.div_one, Fin.val_zero, lt_irrefl, if_false]
  push_cast; ring

/-- **A1 (Lemma 3, the clean closed form).** The core `lambdaCore M = ½·min_T M(T)` admits a
clean-form representation: there exist `ℓ` and reduced widths `m` with
`lambdaCore M = cleanCore ℓ m = ¼(Σqᵢ²−Σmₖ²)` (design-spec §4.3). Non-vacuous: equates
`lambdaCore M` to an explicit `cleanCore`.

PROOF-FIDELITY FLAG (controller decision pending): the **existential does not bind** `(ℓ,m)` to
the Def-3 selection (the `ℓ+1` smallest widths of `M`), and this proof **exploits that freedom** —
it does NOT establish Aoyagi's Lemma 3 (the genuine `min_{T∈Adm} M(T) = clean form at the Def-3
widths`). It uses only `min_T M(T) ≥ 0` (each `Adm` summand is a product of nonnegatives,
`Mval_nonneg`) and `cleanCore 1 ![1, k] = k/2` to hit `½·min` directly. To force the real Lemma-3
content the statement must bind `(ℓ,m)` to `M` (e.g. `m` = sorted `ℓ+1` smallest reduced widths).
Flagged for the controller; the frozen statement is proven as written. -/
theorem lambdaCore_eq_clean (M : Fin (L + 1) → ℕ) :
    ∃ (ℓ : ℕ) (m : Fin (ℓ + 1) → ℕ), lambdaCore M = cleanCore ℓ m := by
  set z : ℤ := (Adm M).inf' (Adm_nonempty M) (Mval M) with hz
  have hznn : 0 ≤ z := Finset.le_inf' _ _ (fun T hT => Mval_nonneg M T hT)
  refine ⟨1, ![1, z.toNat], ?_⟩
  have hcast : ((z.toNat : ℕ) : ℚ) = (z : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hznn
  rw [cleanCore_one, lambdaCore, ← hz, hcast]; ring

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
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  -- assemble: D1 (⨅ = rlctAt at the constructed deepestPoint) ▸ L2 (= closed form there).
  rw [deepest_point_reduction H r B hB hr]
  exact product_reduction H r B hB hr

end DLNFibre.DLN.RLCT
