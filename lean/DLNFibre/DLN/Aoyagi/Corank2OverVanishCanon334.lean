import DLNFibre.DLN.Aoyagi.Corank2OverVanish334

/-!
# `DLN.Aoyagi.Corank2OverVanishCanon334` — the per-type CONCRETE facts (canonical `(20,1,1)`)

The over-vanishing seat's per-type deliverables for the canonical leaf `(p1,p2,p3) = (20,1,1)`,
feeding the generic (ii) backbone (`Corank2OverVanish334`):

* **(1′) the 8 reg-seq entry identities** `coreGen k (gFlat idxCanon (Ψ u)) = (∏ u^vmExp)·u_{zc k}`
  (`k ∈ Scanon`, `|Scanon| = 8`), which `monoSumSqGerm_le_of_regSeq_entries` consumes (NO full
  12-entry pullback);
* **(2) the concrete straightening `Ψ = psiCanon`** — a `blockShear` with `|jacDet| = 1`, keep-set
  disjoint from `supp(vm)` and `supp(jacExp)`;
* **(3) the folded Jacobian** `|jacDet (gFlat idxCanon ∘ Ψ)| = jacWeight (jacExp idxCanon)`; and
* **the cubic-inflation cover-transport atom** (coinciding-leaf `Ψ` is CUBIC-unipotent, so the
  quadratic `image_comp_blockShear_superset` does not apply — this module's cubic sibling does).

The over-vanishing leaf `(20,1,1)` is COINCIDING (`p2 = p3 = 1`), so `vm = u₁·u₂₀` (degree 2) and
its straightening carries a cubic term; the entry-identity structure is `vm`-agnostic, so it is a
faithful structural template for the pattern-A (`p2 ∈ {1,5}`) leaves. Non-coinciding pattern-A have
`vm` degree 3 and a purely quadratic straightening. The 8 reg-seq entry values are `sympy`-verified
end-to-end against the Lean `gFlat` (max error `1e-15`); the recipe mirrors the CLEAN-144
`Corank2CleanEntry334` kernel with `w := Ψ u` folded in.
-/

open Matrix MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativePerm334
open DLNFibre.DLN.Aoyagi.NativeShear334
open DLNFibre.DLN.Aoyagi.NativeJac334
open DLNFibre.DLN.Aoyagi.OverVanish334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi.OverVanishCanon334

/-! ## §0 — the canonical leaf and the `coreGen`→matrix-entry reduction -/

/-- The canonical over-vanishing leaf index `(p1,p2,p3) = (20,1,1)`. -/
def idxCanon : Idx := ⟨⟨20, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩⟩

/-- The canonical leaf composite (`gFlat idxCanon`, `∘id`s and `Idx` projections resolved). -/
noncomputable def gCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun w =>
  blockBlowupMap S1 20 (nativeChart1 20
    (blockBlowupMap (sigmaC1Fs 20) 1 (blockBlowupMap (sigmaC2Fs 20) 1 w)))

/-- `gFlat idxCanon = gCanon` (the `∘id`s drop; `idxCanon`'s pivot projections are `20,1,1`). -/
theorem gFlat_idxCanon : gFlat idxCanon = gCanon := by
  funext w; rfl

/-- **`coreGen` at `eWrap` = the `(A1·A0)` matrix entry** (`mult_eWrap` reindexed). -/
theorem coreGen_eWrap_entry (k : Fin (dvec (Fin.last 2) * dvec 0)) (u : Fin 21 → ℝ) :
    coreGen dvec eWrap k u
      = (A1 u * A0 u) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp only [coreGen]
  exact congrFun (congrFun (mult_eWrap u) _) _

theorem A1_00 (u : Fin 21 → ℝ) : A1 u 0 0 = u 8 := rfl
theorem A1_01 (u : Fin 21 → ℝ) : A1 u 0 1 = u 12 := rfl
theorem A1_02 (u : Fin 21 → ℝ) : A1 u 0 2 = u 16 := rfl
theorem A1_10 (u : Fin 21 → ℝ) : A1 u 1 0 = u 9 := rfl
theorem A1_11 (u : Fin 21 → ℝ) : A1 u 1 1 = u 13 := rfl
theorem A1_12 (u : Fin 21 → ℝ) : A1 u 1 2 = u 17 := rfl
theorem A1_20 (u : Fin 21 → ℝ) : A1 u 2 0 = u 10 := rfl
theorem A1_21 (u : Fin 21 → ℝ) : A1 u 2 1 = u 14 := rfl
theorem A1_22 (u : Fin 21 → ℝ) : A1 u 2 2 = u 18 := rfl
theorem A1_30 (u : Fin 21 → ℝ) : A1 u 3 0 = u 11 := rfl
theorem A1_31 (u : Fin 21 → ℝ) : A1 u 3 1 = u 15 := rfl
theorem A1_32 (u : Fin 21 → ℝ) : A1 u 3 2 = u 19 := rfl

/-! ## §1 — the straightening shear `Ψ = psiCanon` -/

/-- **The canonical straightening displacement** `φ`: places the negative of the quadratic/cubic
correction of each column-`c=1` reg-seq entry into the coordinate it straightens to
(`{12,13,14,15}`). All read coordinates lie OUTSIDE `{12,13,14,15}`, so the shear is unipotent. -/
def phiCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun u i =>
  if i = 12 then -(u 0 * u 10 + u 1 * u 16 * u 5)
  else if i = 13 then -(u 10 * u 2 + u 1 * u 17 * u 5)
  else if i = 14 then -(u 10 * u 3 + u 1 * u 18 * u 5)
  else if i = 15 then -(u 10 * u 4 + u 1 * u 19 * u 5)
  else 0

/-- The canonical straightening `Ψ = blockShear φ`. -/
noncomputable def psiCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := blockShear phiCanon

/-- The kept coordinates of `φ`: everything outside the straightened block `{12,13,14,15}`. -/
def keepCanon : Fin 21 → Prop := fun i => i ≠ 12 ∧ i ≠ 13 ∧ i ≠ 14 ∧ i ≠ 15

/-- `φ` fixes every kept coordinate (`= 0` off `{12,13,14,15}`). -/
theorem phiCanon_keep (u : Fin 21 → ℝ) (i : Fin 21) (hi : keepCanon i) : phiCanon u i = 0 := by
  obtain ⟨h12, h13, h14, h15⟩ := hi
  simp only [phiCanon, if_neg h12, if_neg h13, if_neg h14, if_neg h15]

set_option linter.unusedSimpArgs false in
/-- `φ` reads only kept coordinates (`{0,1,2,3,4,5,10,16,17,18,19}`, all outside the block). -/
theorem phiCanon_read (u v : Fin 21 → ℝ) (h : ∀ i, keepCanon i → u i = v i) :
    phiCanon u = phiCanon v := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  have h10 := h 10 (by decide); have h16 := h 16 (by decide); have h17 := h 17 (by decide)
  have h18 := h 18 (by decide); have h19 := h 19 (by decide)
  funext i
  simp only [phiCanon]
  split_ifs <;> simp only [h0, h1, h2, h3, h4, h5, h10, h16, h17, h18, h19]

set_option linter.unusedSimpArgs false in
/-- `φ` is differentiable (each component is a polynomial or `0`). -/
theorem differentiable_phiCanon : Differentiable ℝ phiCanon := by
  apply differentiable_pi.2
  intro i
  fin_cases i <;>
    simp only [phiCanon, Fin.reduceEq, if_true, if_false, reduceIte] <;>
    fun_prop

/-- `Ψ = blockShear φ` is differentiable. -/
theorem differentiable_psiCanon : Differentiable ℝ psiCanon := by
  unfold psiCanon blockShear
  exact differentiable_id.add differentiable_phiCanon

/-- **`|jacDet Ψ| = 1`** (unipotent block shear). -/
theorem jacDet_psiCanon (u : Fin 21 → ℝ) : jacDet psiCanon u = 1 := by
  unfold psiCanon
  exact jacDet_blockShear phiCanon keepCanon differentiable_phiCanon phiCanon_keep phiCanon_read u

/-- `Ψ` fixes every coordinate outside the block `{12,13,14,15}`. -/
theorem psiCanon_apply_offblock (u : Fin 21 → ℝ) (d : Fin 21) (hd : keepCanon d) :
    psiCanon u d = u d := by
  unfold psiCanon blockShear
  simp only [Pi.add_apply, phiCanon_keep u d hd, add_zero]

/-! ## §2 — the per-type data: `vmExp`, the reg-seq index set `S`, the `zc` map, the block `Z` -/

/-- The dominant monomial exponent `vm = u₁·u₂₀` (`1@1 + 1@20`). -/
def vmExpCanon : Fin 21 → ℕ := fun d => if d = 1 ∨ d = 20 then 1 else 0

/-- `∏_d (u d)^(vmExpCanon d) = u₁·u₂₀`. -/
theorem prod_vmExpCanon (u : Fin 21 → ℝ) : (∏ d, (u d) ^ vmExpCanon d) = u 1 * u 20 := by
  have h1 : ∀ d : Fin 21, u d ^ vmExpCanon d = if d = 1 ∨ d = 20 then u d else 1 := fun d => by
    simp only [vmExpCanon]; split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one,
    show Finset.filter (fun d : Fin 21 => d = 1 ∨ d = 20) Finset.univ = {1, 20} from by decide,
    Finset.prod_insert (by decide), Finset.prod_singleton]

/-- The 8 reg-seq `(row, col)` pairs (pattern A: columns `c = 0,1`); clean `Fin 4 × Fin 3` literals
(numeric literals at `Fin (dvec …)` are ill-behaved, so `S` is their `finProdFinEquiv` image). -/
def pairsCanon : Finset (Fin 4 × Fin 3) :=
  {(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1)}

/-- The 8-element regular-sequence entry-index set `S` (pattern A: columns `c = 0,1`). -/
def Scanon : Finset (Fin (dvec (Fin.last 2) * dvec 0)) := pairsCanon.image finProdFinEquiv

/-- The straightening coordinate map on `(row, col)` pairs: each reg-seq entry to its coordinate. -/
def zcPair : Fin 4 × Fin 3 → Fin 21 := fun p =>
  if p = (0, 0) then 0 else if p = (0, 1) then 12 else if p = (1, 0) then 2
  else if p = (1, 1) then 13 else if p = (2, 0) then 3 else if p = (2, 1) then 14
  else if p = (3, 0) then 4 else 15

/-- The straightening coordinate map `zc`: each reg-seq entry to its straightened coordinate. -/
def zcCanon : Fin (dvec (Fin.last 2) * dvec 0) → Fin 21 := fun k => zcPair (finProdFinEquiv.symm k)

/-- The `jac`-free regular-sequence coordinate block `Z = zc '' S`. -/
def Zcanon : Finset (Fin 21) := {0, 2, 3, 4, 12, 13, 14, 15}

theorem hzc_inj : ∀ x ∈ Scanon, ∀ y ∈ Scanon, zcCanon x = zcCanon y → x = y := by decide

theorem hzc_img : Scanon.image zcCanon = Zcanon := by decide

/-! ## §3 — the 8 reg-seq entry identities (`coreGen k (gCanon (Ψ u)) = u₁·u₂₀·u_{zc k}`)

The recipe: `coreGen_eWrap_entry` (→ the `(A1·A0)` matrix entry), `Matrix.mul_apply` +
`Fin.sum_univ_three` (→ the 3-term sum), then the `decide`-powered `simp` unfolds the whole folded
composite `gCanon ∘ Ψ` (blow-ups, native shear/perm, and the straightening `φ`) to a polynomial in
`u`, and `ring` verifies the cancellation. The raised heartbeat budget is for this heavy per-entry
matrix algebra (same scale as the CLEAN-144 `hentry` kernel). -/

-- Heavy `decide`-`simp` over the folded composite (CLEAN-144 `hentry` kernel scale).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
/-- Entry `k = finProdFinEquiv (0,0) = 0`, `zc = 0`. -/
theorem entry_00 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((0 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = u 1 * u 20 * u 0 := by
  rw [coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

-- Heavy `decide`-`simp` over the folded composite (CLEAN-144 `hentry` kernel scale).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
/-- Entry `k = finProdFinEquiv (0,1) = 1`, `zc = 12`. -/
theorem entry_01 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((0 : Fin 4), (1 : Fin 3))) (gCanon (psiCanon u))
      = u 1 * u 20 * u 12 := by
  rw [coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

-- Heavy `decide`-`simp` over the folded composite (CLEAN-144 `hentry` kernel scale).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
/-- Entry `k = finProdFinEquiv (1,0) = 3`, `zc = 2`. -/
theorem entry_10 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((1 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = u 1 * u 20 * u 2 := by
  rw [coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

-- Heavy `decide`-`simp` over the folded composite (CLEAN-144 `hentry` kernel scale).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
/-- Entry `k = finProdFinEquiv (1,1) = 4`, `zc = 13`. -/
theorem entry_11 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((1 : Fin 4), (1 : Fin 3))) (gCanon (psiCanon u))
      = u 1 * u 20 * u 13 := by
  rw [coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

-- Heavy `decide`-`simp` over the folded composite (CLEAN-144 `hentry` kernel scale).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
/-- Entry `k = finProdFinEquiv (2,0) = 6`, `zc = 3`. -/
theorem entry_20 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((2 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = u 1 * u 20 * u 3 := by
  rw [coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

-- Heavy `decide`-`simp` over the folded composite (CLEAN-144 `hentry` kernel scale).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
/-- Entry `k = finProdFinEquiv (2,1) = 7`, `zc = 14`. -/
theorem entry_21 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((2 : Fin 4), (1 : Fin 3))) (gCanon (psiCanon u))
      = u 1 * u 20 * u 14 := by
  rw [coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

-- Heavy `decide`-`simp` over the folded composite (CLEAN-144 `hentry` kernel scale).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
/-- Entry `k = finProdFinEquiv (3,0) = 9`, `zc = 4`. -/
theorem entry_30 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((3 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = u 1 * u 20 * u 4 := by
  rw [coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

-- Heavy `decide`-`simp` over the folded composite (CLEAN-144 `hentry` kernel scale).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
/-- Entry `k = finProdFinEquiv (3,1) = 10`, `zc = 15`. -/
theorem entry_31 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((3 : Fin 4), (1 : Fin 3))) (gCanon (psiCanon u))
      = u 1 * u 20 * u 15 := by
  rw [coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

set_option linter.unusedSimpArgs false in
/-- **The 8 reg-seq entry identities (the (1′) deliverable).** For every reg-seq index `k ∈ Scanon`,
`coreGen k (gFlat idxCanon (Ψ u)) = (∏ u^vmExp)·u_{zc k}`. Fed to the (ii)
`monoSumSqGerm_le_of_regSeq_entries`. -/
theorem canon_hentry (u : Fin 21 → ℝ) (k : Fin (dvec (Fin.last 2) * dvec 0)) (hk : k ∈ Scanon) :
    coreGen dvec eWrap k (gFlat idxCanon (psiCanon u))
      = (∏ d, (u d) ^ vmExpCanon d) * u (zcCanon k) := by
  rw [gFlat_idxCanon, prod_vmExpCanon]
  simp only [Scanon, Finset.mem_image] at hk
  obtain ⟨p, hp, rfl⟩ := hk
  simp only [zcCanon, Equiv.symm_apply_apply]
  fin_cases hp
  · exact entry_00 u
  · exact entry_01 u
  · exact entry_10 u
  · exact entry_11 u
  · exact entry_20 u
  · exact entry_21 u
  · exact entry_30 u
  · exact entry_31 u

/-! ## §4 — the assembled per-type domination fact (consumes the (ii) backbone) -/

/-- **The over-vanishing product-germ domination (the per-type FACT feeding step 6).** For the
canonical leaf, the folded loss `∑_k (coreGen k ∘ (gFlat idxCanon ∘ Ψ))²` dominates the product germ
`vm²·∑_Z z²`. Consumes `monoSumSqGerm_le_of_regSeq_entries` with the 8 entry identities. -/
theorem canon_domination (u : Fin 21 → ℝ) :
    monoSumSqGerm vmExpCanon Zcanon u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gFlat idxCanon ∘ psiCanon)) u :=
  monoSumSqGerm_le_of_regSeq_entries (S := Scanon) (zc := zcCanon) canon_hentry hzc_inj hzc_img u

/-! ## §5 — the folded Jacobian `|jacDet (gFlat idxCanon ∘ Ψ)| = jacWeight (jacExp idxCanon)` -/

set_option linter.unusedSimpArgs false in
/-- Every binding axis of `jacExp idxCanon` (`= {1,20}`) is outside the block `{12,13,14,15}`. -/
theorem hfix_jacExp (u : Fin 21 → ℝ) :
    ∀ d, 0 < jacExp idxCanon d → psiCanon u d = u d := by
  intro d hd
  apply psiCanon_apply_offblock u d
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; subst h; simp [jacExp, idxCanon, NativeJac334.single] at hd)

/-- **The folded Jacobian (the (3) deliverable), `hW` form.** `|jacDet (gFlat idxCanon ∘ Ψ) u| =
jacWeight (jacExp idxCanon) u` — the chain rule (`Ψ` contributes `|jacDet| = 1`) plus the base
`hjac_gFlat` plus `jacWeight_fixOn` (`Ψ` fixes every binding axis of `jacExp idxCanon`). -/
theorem canon_foldedJac (u : Fin 21 → ℝ) :
    |jacDet (gFlat idxCanon ∘ psiCanon) u| = jacWeight (jacExp idxCanon) u := by
  rw [jacDet_comp u (differentiable_gFlat idxCanon).differentiableAt
    differentiable_psiCanon.differentiableAt, abs_mul, jacDet_psiCanon, abs_one, mul_one,
    hjac_gFlat idxCanon (psiCanon u)]
  exact jacWeight_fixOn (jacExp idxCanon) (hfix_jacExp u)

/-! ## §6 — the CUBIC-inflation cover-transport atom (coinciding-leaf `Ψ` is cubic-unipotent)

The coinciding-leaf straightening `Ψ` carries a CUBIC term (`φ_12 = −(u₀u₁₀ + u₁u₁₆u₅)`), so the
quadratic `image_comp_blockShear_superset` (`hquad : ‖φ x‖ ≤ C·r²`) does not apply. This sibling
atom transports the cover under a cubic-unipotent shear (`r ↦ r + C·r³`). Non-coinciding pattern-A
leaves remain quadratic (the existing atom). -/

/-- **The cubic-inflation box-containment atom** (the `blockShear_covers_scaled` cubic sibling): a
`blockShear φ` with a cubic displacement bound `‖φ x‖ ≤ C·r³` box-contains, inflation `r + C·r³`. -/
theorem blockShear_covers_cubic {D : ℕ} {φ : (Fin D → ℝ) → (Fin D → ℝ)} (keep : Fin D → Prop)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v)
    {r C : ℝ} (hcub : ∀ x : Fin D → ℝ, ‖x‖ ≤ r → ‖φ x‖ ≤ C * r ^ 3) :
    closedBall (0 : Fin D → ℝ) r ⊆ blockShear φ '' closedBall 0 (r + C * r ^ 3) := by
  intro x hx
  have hxr : ‖x‖ ≤ r := mem_closedBall_zero_iff.mp hx
  refine ⟨blockShearInv φ x, ?_, blockShearInv_rightInverse φ keep hkeep hread x⟩
  rw [mem_closedBall_zero_iff]
  calc ‖blockShearInv φ x‖ = ‖x - φ x‖ := rfl
    _ ≤ ‖x‖ + ‖φ x‖ := norm_sub_le _ _
    _ ≤ r + C * r ^ 3 := add_le_add hxr (hcub x hxr)

/-- **The cubic displacement bound for `φ = phiCanon`** at radius `r ≥ 1`: each corrected slot is a
quadratic plus a cubic (`|quad| ≤ r² ≤ r³`, `|cubic| ≤ r³`), so `‖φ x‖ ≤ 2·r³`. -/
theorem phiCanon_norm_bound {x : Fin 21 → ℝ} {r : ℝ} (hr1 : 1 ≤ r) (hx : ‖x‖ ≤ r) :
    ‖phiCanon x‖ ≤ 2 * r ^ 3 := by
  have hr0 : 0 ≤ r := by linarith
  have hr23 : r ^ 2 ≤ r ^ 3 := by nlinarith [sq_nonneg r, hr1]
  have habs : ∀ i : Fin 21, |x i| ≤ r := fun i => by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x i).trans hx
  have hq : ∀ a b : Fin 21, |x a * x b| ≤ r ^ 2 := fun a b => by
    rw [abs_mul, sq]; exact mul_le_mul (habs a) (habs b) (abs_nonneg _) hr0
  have hcube : ∀ a b c : Fin 21, |x a * x b * x c| ≤ r ^ 3 := fun a b c => by
    rw [abs_mul, abs_mul]
    calc |x a| * |x b| * |x c| ≤ r * r * r :=
          mul_le_mul (mul_le_mul (habs a) (habs b) (abs_nonneg _) hr0) (habs c) (abs_nonneg _)
            (by positivity)
      _ = r ^ 3 := by ring
  have slot : ∀ a b c d e : Fin 21, |(-(x a * x b + x c * x d * x e))| ≤ 2 * r ^ 3 :=
    fun a b c d e => by
      rw [abs_neg]
      calc |x a * x b + x c * x d * x e| ≤ |x a * x b| + |x c * x d * x e| := abs_add_le _ _
        _ ≤ r ^ 2 + r ^ 3 := add_le_add (hq a b) (hcube c d e)
        _ ≤ 2 * r ^ 3 := by linarith
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  by_cases h12 : i = 12
  · rw [h12, show phiCanon x 12 = -(x 0 * x 10 + x 1 * x 16 * x 5) from rfl]
    exact slot 0 10 1 16 5
  by_cases h13 : i = 13
  · rw [h13, show phiCanon x 13 = -(x 10 * x 2 + x 1 * x 17 * x 5) from rfl]
    exact slot 10 2 1 17 5
  by_cases h14 : i = 14
  · rw [h14, show phiCanon x 14 = -(x 10 * x 3 + x 1 * x 18 * x 5) from rfl]
    exact slot 10 3 1 18 5
  by_cases h15 : i = 15
  · rw [h15, show phiCanon x 15 = -(x 10 * x 4 + x 1 * x 19 * x 5) from rfl]
    exact slot 10 4 1 19 5
  · rw [phiCanon_keep x i ⟨h12, h13, h14, h15⟩, abs_zero]; positivity

/-- **The canonical cubic cover-transport** — `closedBall 0 r ⊆ Ψ '' closedBall 0 (r + 2·r³)` for
`r ≥ 1` (the leaf box radius `leafR ≥ 1`). The cubic sibling of the quadratic leaf-cover atom. -/
theorem psiCanon_cubic_cover {r : ℝ} (hr1 : 1 ≤ r) :
    closedBall (0 : Fin 21 → ℝ) r ⊆ psiCanon '' closedBall 0 (r + 2 * r ^ 3) := by
  unfold psiCanon
  exact blockShear_covers_cubic keepCanon phiCanon_keep phiCanon_read
    (fun x hx => phiCanon_norm_bound hr1 hx)

/-- **The folded-chart cover survives the cubic fold** — the cubic analogue of
`image_comp_blockShear_superset`: the base chart's image over `closedBall 0 r` sits inside the
folded chart `g ∘ Ψ`'s image over the cubically-inflated ball. -/
theorem image_comp_psiCanon_cubic_superset (g : (Fin 21 → ℝ) → (Fin 21 → ℝ)) {r : ℝ} (hr1 : 1 ≤ r) :
    g '' closedBall 0 r ⊆ (g ∘ psiCanon) '' closedBall 0 (r + 2 * r ^ 3) := by
  calc g '' closedBall (0 : Fin 21 → ℝ) r
      ⊆ g '' (psiCanon '' closedBall 0 (r + 2 * r ^ 3)) :=
        Set.image_mono (psiCanon_cubic_cover hr1)
    _ = (g ∘ psiCanon) '' closedBall 0 (r + 2 * r ^ 3) := (Set.image_comp g psiCanon _).symm

end DLNFibre.DLN.Aoyagi.OverVanishCanon334
