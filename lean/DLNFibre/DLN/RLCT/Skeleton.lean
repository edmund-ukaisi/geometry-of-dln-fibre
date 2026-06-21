import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.Lambda
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Data.Fin.Tuple.Sort

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
equates the inf to the local RLCT at `deepestPoint`. -/
theorem deepest_point_reduction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (⨅ v ∈ optimalSet H B, rlctAt H (dlnLoss H B) v)
      = rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) := by
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

/-- **A1 (Lemma 3, the genuine clean closed form; pp statement card, candidate (d)).** The core
`lambdaCore M = ½·min_T M(T)` equals `cleanCore c (sortedSmallest M c)` for an **achiever**
`c ∈ {1,…,L}` — the `m` argument is **pinned** to `M`'s `c+1` smallest reduced widths (a function of
`M`, not a free choice), so this is the faithful Aoyagi Lemma 3 (`min_{T∈Adm} M(T) = clean form at
the smallest widths), NOT the weak existential. Verified total 1360/1360 (pp). It is **NOT** an
extremum over `c` — both `min_c` and `max_c` are refuted (`M=[1,1,4]`, `[2,2,2]`); the `∃ c` is the
achiever (the `c` whose balanced split on the smallest widths is `Adm`-admissible). Proof route
(Aoyagi Lemma 3): balanced-split-minimises-`Σq²` (exchange) + `Adm` reparametrisation + per-`c`
lower bound + constructed achiever. -/
theorem lambdaCore_eq_clean (M : Fin (L + 1) → ℕ) :
    ∃ (c : ℕ) (hc : c ≤ L), 1 ≤ c ∧ lambdaCore M = cleanCore c (sortedSmallest M c hc) := by
  sorry

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

end DLNFibre.DLN.RLCT
