import DLNFibre.DLN.RLCT.Validate.RouteMFactorFDeriv
import DLNFibre.DLN.RLCT.Validate.RouteMConjBlock
import DLNFibre.DLN.RLCT.Validate.RouteMGenChainBridge

/-!
# `RouteMFactorMaps` — Phase B item 2: the Schur / LDU / chain factor maps + their fderivs + dets

The nonlinear achiever-chart factor maps on their OWN block spaces, each with a `HasFDerivAt` matching
its banked Phase-A differential, packaged (via `RouteMConjBlock.conjBlockFactor`) into full-ambient
`ChartFactor`s whose abs-dets are the banked monomial values. The genuine item-2 deliverable: each of
the three nontrivial factors is a `ChartFactor N` with its determinant, parametric in the
ambient-split CLE `E` (the specific `E` — the chart match — is item 3).

* `schurFrameMap` / `schurFrameMap_hasFDerivAt` — the Schur frame `S(X,K,N,E) = [[K,KN],[XK,XKN+E]]`
  with fderiv `schurFrameDeriv` (the banked block-triangular differential, `det = |K.det|^(r+c)`).
* `lduCoreMap` / `lduCoreMap_hasFDerivAt` — the LDU core `(l,q,u) ↦ split((1+L)·diag q·(1+U))` with
  fderiv `lduCoreDeriv` (`det = ∏ |q_i|^{2(t−1−i)}`).
* `chainUnitMap` is already LINEAR (`RouteMGenChainBridge`, `det = 1`) — `chainUnitMap_hasFDerivAt`
  is its constant-fderiv `HasFDerivAt`.
* `schurFactor` / `lduFactor` / `chainFactor` (+ `_abs_det`) — the three conjugated `ChartFactor`s.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

/-! ## The Schur frame factor map + its fderiv (`schurFrameDeriv`) -/

/-- **The Schur frame map** `S(X,K,N,E) = (K, K·N, (X·K, X·K·N + E))` on the increment space
`SchurInc t r c` (the achiever chart's per-boundary frame). Nonlinear (products of input blocks). -/
noncomputable def schurFrameMap {t r c : ℕ} (z : SchurInc t r c) : SchurInc t r c :=
  (z.1, z.1 * z.2.1, (z.2.2.1 * z.1, z.2.2.1 * z.1 * z.2.1 + z.2.2.2))

/-- **The Schur frame map's CLM fderiv** `schurFrameDeriv z.X z.K z.N` (the banked block-triangular
differential), as a `ContinuousLinearMap` (finite-dimensional ⟹ continuous). -/
noncomputable def schurFrameD {t r c : ℕ} (z : SchurInc t r c) :
    SchurInc t r c →L[ℝ] SchurInc t r c :=
  LinearMap.toContinuousLinearMap (schurFrameDeriv z.2.2.1 z.1 z.2.1)

/-- **The Schur frame map has fderiv `schurFrameD`** at every point — the product rule assembled over
the four output blocks (`prodMk`/`matMul`/`add`), then matched to `schurFrameDeriv_apply` entry-wise
(the off-diagonal couplings recombine; closed by `noncomm_ring`/`add_mul`+`abel`). -/
theorem schurFrameMap_hasFDerivAt {t r c : ℕ} (z : SchurInc t r c) :
    HasFDerivAt schurFrameMap (schurFrameD z) z := by
  have hK : HasFDerivAt (fun w : SchurInc t r c => w.1) (ContinuousLinearMap.fst ℝ _ _) z :=
    hasFDerivAt_fst
  have hN : HasFDerivAt (fun w : SchurInc t r c => w.2.1)
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) z :=
    hasFDerivAt_fst.comp z hasFDerivAt_snd
  have hX : HasFDerivAt (fun w : SchurInc t r c => w.2.2.1)
      ((ContinuousLinearMap.fst ℝ _ _).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))) z :=
    hasFDerivAt_fst.comp z (hasFDerivAt_snd.comp z hasFDerivAt_snd)
  have hE : HasFDerivAt (fun w : SchurInc t r c => w.2.2.2)
      ((ContinuousLinearMap.snd ℝ _ _).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))) z :=
    hasFDerivAt_snd.comp z (hasFDerivAt_snd.comp z hasFDerivAt_snd)
  have h2 := HasFDerivAt.matMul hK hN
  have h3 := HasFDerivAt.matMul hX hK
  have h4 := (HasFDerivAt.matMul h3 hN).add hE
  have hfull := hK.prodMk (h2.prodMk (h3.prodMk h4))
  refine hfull.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  rw [schurFrameD]
  change _ = (schurFrameDeriv z.2.2.1 z.1 z.2.1) v
  rw [schurFrameDeriv_apply]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.compL_apply, matMulBilin_apply]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
  · noncomm_ring
  · noncomm_ring
  · rw [Matrix.add_mul]; abel

/-- The Schur frame map's fderiv has abs-det `|K.det|^(r+c)` (the banked `schurFrame_abs_det`). -/
theorem schurFrameD_abs_det {t r c : ℕ} (z : SchurInc t r c) :
    |LinearMap.det (schurFrameD z).toLinearMap| = |(z.1).det| ^ (r + c) := by
  rw [schurFrameD, LinearMap.coe_toContinuousLinearMap]
  exact schurFrame_abs_det z.2.2.1 z.1 z.2.1

/-! ## The LDU core factor map + its fderiv (`lduCoreDeriv`) -/

/-- **The LDU core map** `(l,q,u) ↦ split((1+lowMat l)·diag q·(1+upMat u))` on `LDUParam t` — the
achiever chart's per-boundary LDU reparametrization, read back in LDU coordinates via `matrixSplit`.
Nonlinear (a triple matrix product). -/
noncomputable def lduCoreMap {t : ℕ} (w : LDUParam t) : LDUParam t :=
  matrixSplit ((1 + lowMatL w.1) * Matrix.diagonal w.2.1 * (1 + upMatL w.2.2))

/-- **The LDU core map's CLM fderiv** `lduCoreDeriv z.l z.q z.u` (the banked block-diagonal LDU
differential), as a `ContinuousLinearMap`. -/
noncomputable def lduCoreD {t : ℕ} (z : LDUParam t) : LDUParam t →L[ℝ] LDUParam t :=
  LinearMap.toContinuousLinearMap (lduCoreDeriv z.1 z.2.1 z.2.2)

/-- **The LDU core map has fderiv `lduCoreD`** at every point — the triple-product rule on the three
affine pieces (`1+lowMat l`, `diag q`, `1+upMat u`) composed with the linear `matrixSplit`, matched
to `lduDerivMat_apply` (the banked Fréchet form) via `noncomm_ring`. -/
theorem lduCoreMap_hasFDerivAt {t : ℕ} (z : LDUParam t) :
    HasFDerivAt lduCoreMap (lduCoreD z) z := by
  have hL : HasFDerivAt (fun w : LDUParam t => (1 : Matrix (Fin t) (Fin t) ℝ) + lowMatL w.1)
      ((lowMatL (t := t)).toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _)) z := by
    have h := (lowMatL (t := t)).toContinuousLinearMap.hasFDerivAt.comp z hasFDerivAt_fst
    simpa using h.const_add (1 : Matrix (Fin t) (Fin t) ℝ)
  have hD : HasFDerivAt (fun w : LDUParam t => Matrix.diagonal w.2.1)
      ((diagAsMat (t := t)).toContinuousLinearMap.comp
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))) z := by
    have h1 : HasFDerivAt (fun w : LDUParam t => w.2.1)
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) z :=
      hasFDerivAt_fst.comp z hasFDerivAt_snd
    have h := (diagAsMat (t := t)).toContinuousLinearMap.hasFDerivAt.comp z h1
    simpa [diagAsMat_apply] using h
  have hU : HasFDerivAt (fun w : LDUParam t => (1 : Matrix (Fin t) (Fin t) ℝ) + upMatL w.2.2)
      ((upMatL (t := t)).toContinuousLinearMap.comp
        ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))) z := by
    have h1 : HasFDerivAt (fun w : LDUParam t => w.2.2)
        ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) z :=
      hasFDerivAt_snd.comp z hasFDerivAt_snd
    have h := (upMatL (t := t)).toContinuousLinearMap.hasFDerivAt.comp z h1
    simpa using h.const_add (1 : Matrix (Fin t) (Fin t) ℝ)
  have hprod := HasFDerivAt.matMul (HasFDerivAt.matMul hL hD) hU
  have hsplit := (matrixSplit (t := t)).toContinuousLinearMap.hasFDerivAt.comp z hprod
  refine hsplit.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  rw [lduCoreD]
  change _ = (lduCoreDeriv z.1 z.2.1 z.2.2) v
  rw [lduCoreDeriv, LinearMap.comp_apply, lduDerivMat_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.compL_apply,
    matMulBilin_apply, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe, diagAsMat_apply]
  congr 1
  noncomm_ring

/-- The LDU core map's fderiv has abs-det `∏ |q_i|^{2(t−1−i)}` (the banked `lduCoreDeriv_abs_det`). -/
theorem lduCoreD_abs_det {t : ℕ} (z : LDUParam t) :
    |LinearMap.det (lduCoreD z).toLinearMap| = ∏ i : Fin t, |z.2.1 i| ^ (2 * ((t : ℕ) - 1 - (i : ℕ))) := by
  rw [lduCoreD, LinearMap.coe_toContinuousLinearMap]
  exact lduCoreDeriv_abs_det z.1 z.2.1 z.2.2

/-! ## The chain factor map (the banked LINEAR det-1 chaining `chainUnitMap`)

`chainUnitMap N` (`RouteMGenChainBridge`) is already a `LinearMap`; the chain factor map is its
continuous form, with constant fderiv = itself and `det = 1` (`chainUnit_det`). -/

/-- **The chain factor map** — the banked det-1 chaining `chainUnitMap N` (`(W,C) ↦ (W, C − N·W)`) as
a `ContinuousLinearMap` (finite-dimensional ⟹ continuous). -/
noncomputable def chainUnitCLM {t c m' : ℕ} (N : Matrix (Fin t) (Fin c) ℝ) :
    (Matrix (Fin c) (Fin m') ℝ × Matrix (Fin t) (Fin m') ℝ) →L[ℝ]
      (Matrix (Fin c) (Fin m') ℝ × Matrix (Fin t) (Fin m') ℝ) :=
  LinearMap.toContinuousLinearMap (chainUnitMap N)

/-- **The chain factor map has constant fderiv `chainUnitCLM N`** (it is linear). -/
theorem chainUnitCLM_hasFDerivAt {t c m' : ℕ} (N : Matrix (Fin t) (Fin c) ℝ)
    (z : Matrix (Fin c) (Fin m') ℝ × Matrix (Fin t) (Fin m') ℝ) :
    HasFDerivAt (chainUnitCLM N) (chainUnitCLM N) z := (chainUnitCLM N).hasFDerivAt

/-- The chain factor map's fderiv has abs-det `1` (the banked `chainUnit_det`). -/
theorem chainUnitCLM_abs_det {t c m' : ℕ} (N : Matrix (Fin t) (Fin c) ℝ) :
    |LinearMap.det (chainUnitCLM (m' := m') N).toLinearMap| = 1 := by
  rw [chainUnitCLM, LinearMap.coe_toContinuousLinearMap, chainUnit_det, abs_one]

/-! ## The conjugated full-ambient `ChartFactor`s + their abs-dets

Each factor's block space `B` (`SchurInc`/`LDUParam`/the chain pair) carries the diamond-free
pi-norm structure (`RouteMFactorFDeriv`); conjugating into the flat ambient `Fin N → ℝ` via any CLE
`E : (Fin N → ℝ) ≃L[ℝ] B × R` packages it as a `ChartFactor N` whose abs-det is the banked monomial
read at the prefix block `(E u).1`. The specific `E` (the chart match) is item 3; here the det is
parametric in `E`. -/

variable {N : ℕ}

/-- **The Schur `ChartFactor`** — `schurFrameMap` conjugated into the flat ambient via `E`. -/
noncomputable def schurChartFactor {t r c : ℕ} {R : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    (E : (Fin N → ℝ) ≃L[ℝ] SchurInc t r c × R) : ChartFactor N :=
  conjBlockFactor E schurFrameMap schurFrameD (fun b => schurFrameMap_hasFDerivAt b)

/-- **The Schur factor's abs-det**: `|det (D u)| = |K(u).det|^(r+c)` where `K(u) = ((E u).1).1` is the
Schur core block read from the prefix point `u`. -/
theorem schurChartFactor_abs_det {t r c : ℕ} {R : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    (E : (Fin N → ℝ) ≃L[ℝ] SchurInc t r c × R) (u : Fin N → ℝ) :
    |LinearMap.det ((schurChartFactor E).D u).toLinearMap| = |((E u).1.1).det| ^ (r + c) :=
  conjBlockFactor_abs_det E schurFrameMap schurFrameD _
    (fun b => |(b.1).det| ^ (r + c)) (fun b => schurFrameD_abs_det b) u

/-- **The LDU `ChartFactor`** — `lduCoreMap` conjugated into the flat ambient via `E`. -/
noncomputable def lduChartFactor {t : ℕ} {R : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    (E : (Fin N → ℝ) ≃L[ℝ] LDUParam t × R) : ChartFactor N :=
  conjBlockFactor E lduCoreMap lduCoreD (fun b => lduCoreMap_hasFDerivAt b)

/-- **The LDU factor's abs-det**: `|det (D u)| = ∏ |q_i|^{2(t−1−i)}` where `q = ((E u).1).2.1` is the
LDU diagonal block read from the prefix point `u`. -/
theorem lduChartFactor_abs_det {t : ℕ} {R : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    (E : (Fin N → ℝ) ≃L[ℝ] LDUParam t × R) (u : Fin N → ℝ) :
    |LinearMap.det ((lduChartFactor E).D u).toLinearMap|
      = ∏ i : Fin t, |((E u).1).2.1 i| ^ (2 * ((t : ℕ) - 1 - (i : ℕ))) :=
  conjBlockFactor_abs_det E lduCoreMap lduCoreD _
    (fun b => ∏ i : Fin t, |b.2.1 i| ^ (2 * ((t : ℕ) - 1 - (i : ℕ)))) (fun b => lduCoreD_abs_det b) u

/-- **The chain `ChartFactor`** — `chainUnitCLM N` conjugated into the flat ambient via `E`. -/
noncomputable def chainChartFactor {t c m' : ℕ} {R : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    (Nblk : Matrix (Fin t) (Fin c) ℝ)
    (E : (Fin N → ℝ) ≃L[ℝ] (Matrix (Fin c) (Fin m') ℝ × Matrix (Fin t) (Fin m') ℝ) × R) :
    ChartFactor N :=
  conjBlockFactor E (chainUnitCLM Nblk) (fun _ => chainUnitCLM Nblk)
    (fun b => chainUnitCLM_hasFDerivAt Nblk b)

/-- **The chain factor's abs-det**: `|det (D u)| = 1` (the det-1 chaining, every point). -/
theorem chainChartFactor_abs_det {t c m' : ℕ} {R : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    (Nblk : Matrix (Fin t) (Fin c) ℝ)
    (E : (Fin N → ℝ) ≃L[ℝ] (Matrix (Fin c) (Fin m') ℝ × Matrix (Fin t) (Fin m') ℝ) × R)
    (u : Fin N → ℝ) :
    |LinearMap.det ((chainChartFactor Nblk E).D u).toLinearMap| = 1 :=
  conjBlockFactor_abs_det E (chainUnitCLM Nblk) (fun _ => chainUnitCLM Nblk) _
    (fun _ => 1) (fun _ => chainUnitCLM_abs_det Nblk) u

end DLNFibre.DLN.RLCT
