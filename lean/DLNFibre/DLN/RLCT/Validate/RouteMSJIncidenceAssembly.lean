import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitDom
import DLNFibre.DLN.RLCT.Validate.MinAdmPermInvariance
import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceChart
import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceChart4Polar
import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceChart5BigCell
import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceExponent
import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceGluing

set_option linter.style.longLine false

/-!
# `RouteMSJIncidenceAssembly` — the coupled-incidence-route assembly of `deeperFlag_shell_le`

**Thread `genm-sj5-capstone` (aoyagi-full Stage 2), the VERIFIED capstone route
(`genm-routeverify/routeverify-cert.md`).** Builds `deeperFlag_shell_le` DIRECTLY through the banked
joint incidence-rank charts (spine → comparator), BYPASSING `headSplit_domination`/route B (a proven type
error, routeverify CHECK 2) and the decoupled `deeperFlagCoreIntegrand`/L1 core.

The 5-step reduction chain (routeverify §6):
1. **Row-split + shell→core** (this file): the shell-restricted spine integrand is dominated by the
   coupled `(z, A_cor)`-box freed-loss integral at the ACTUAL deep factor `Q_b = A_cor · deeperFlagZdeep z`,
   over the FULL `matBox` (NOT the route-B `pivotShell` restriction — `shellSpine_le_hsQ_box` lands on
   `matBox ∩ pivotShell` and is FALSE, routefork; the full-box version is a fortiori TRUE since off-shell
   is already finite to `T1`). Brick F (`exists_headSplitFrame`) is DROPPED — the coupled charts keep the
   det-Gram coupled and never need the Loewner floor (routeverify §5(D)).
2. IsUnit-`P` freed-corner shear + Γ-integration → coupled corank charge `det(Q_bQ_bᵀ)^{−a/2}` [pending].
3. Joint incidence charts (banked: `det_chartGram`, `transverseSchurGram`, `chart4_Htilde_fibre_lt_top`,
   `chart5_bigcell_cov`) [pending].
4. Per-stratum exponent gate — the general-`L` `clsCodim ↔ minAdm(redChain u M)` identity (arity-3
   `clsCodim_gate` is the L=0 template); ISOLATED for gaugelift [pending].
5. Finite-cover gluing (banked `lintegral_lt_top_of_finset_cover`) + per-stratum ratio sum [pending].

This file lands step 1 sorry-free (the row-split reduction to the coupled full-box integral). The banked
plumbing consumed: `hsSplit` / `measurePreserving_hsSplit` (the head/row split), `prod_headSplit` (exposing
`Q_b = A_cor·Z_deep`), and the entrywise action lemmas `hsSplit_fst_zero`/`_succ`/`hsSplit_snd`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## Step 4 dependency — the per-cut pivot bound `minAdm (redChain u M) ≤ u · deepTailMin M`

Copied VERBATIM (same names) from the connector branch `origin/genm-sj5-good`
(`RouteMSJDecoratedStep.lean` L103/L131) so the coupled-route gate cell (step 4) can consume it on this
base; the coordinator's steer (no connector merge — the connector carries open waist sorries). These are
low-level `minAdm`/`redChain` facts (deps `minAdm_comp_perm`, `minAdm_le_mul_head`, `Finset.inf'`, all on
this base); when the connector integrates to canonical this is a trivial dedup (identical statements). The
gate chain (gaugelift `clsCodim_gate_genL`): `minAdm M ≤ (M₀−s)(M₁−s) + minAdm(redChain s M) ≤
(M₀−s)(M₁−s) + s·deepTailMin M ≤ (M₀−s)(M₁−s) + s·M₂ = clsCodim + ab`. -/

/-- **The deep-tail width minimum** `deepTailMin M = ⨅_{i≥2} M i = min (M₂,…,M_last)` — the tail widths
STRICTLY past the pivot layer `M₁` (excludes `M₁`, unlike `tailMinWidth = min (M₁,…,M_last)`). -/
def deepTailMin (M : Fin (L + 1 + 1 + 1) → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin (L + 1))).inf' ⟨0, Finset.mem_univ 0⟩ (fun i => M i.succ.succ)

/-- **The head-times-tail-minimum bound `minAdm N ≤ N₀ · ⨅_{i≥1} Nᵢ`**, via permutation invariance:
move the argmin tail width to position 1 (`minAdm_comp_perm` at `Equiv.swap 1 i★.succ`, fixing `0`),
then apply the head bound `minAdm_le_mul_head`. -/
theorem minAdm_le_head_mul_tailInf {k : ℕ} (N : Fin (k + 1 + 1) → ℕ) :
    minAdm N ≤ N 0 * (Finset.univ : Finset (Fin (k + 1))).inf'
      ⟨0, Finset.mem_univ 0⟩ (fun i => N i.succ) := by
  classical
  obtain ⟨istar, -, histar⟩ := Finset.exists_mem_eq_inf'
    (⟨0, Finset.mem_univ 0⟩ : (Finset.univ : Finset (Fin (k + 1))).Nonempty)
    (fun i => N i.succ)
  rw [histar]
  calc minAdm N = minAdm (N ∘ Equiv.swap (1 : Fin (k + 1 + 1)) istar.succ) :=
        (minAdm_comp_perm _ N).symm
    _ ≤ (N ∘ Equiv.swap (1 : Fin (k + 1 + 1)) istar.succ) 0
          * (N ∘ Equiv.swap (1 : Fin (k + 1 + 1)) istar.succ) 1 := minAdm_le_mul_head _
    _ = N 0 * N istar.succ := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne Fin.zero_ne_one (Fin.succ_ne_zero istar).symm,
          Equiv.swap_apply_left]

/-- **The per-cut pivot bound `minAdm (redChain u M) ≤ u · deepTailMin M`** (∀ u) — the GOOD-branch
per-cut hpiv source. `redChain u M = (u, M₂,…,M_last)`, so its position-0 width is `u` and its tail
minimum (indices `≥ 1`) is `deepTailMin M`; `minAdm_le_head_mul_tailInf` gives the bound. -/
theorem minAdm_redChain_le_deepTailMin (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) :
    minAdm (redChain u M) ≤ u * deepTailMin M := by
  have h := minAdm_le_head_mul_tailInf (redChain u M)
  rw [redChain_zero] at h
  have hfun : (fun i : Fin (L + 1) => (redChain u M) i.succ) = (fun i => M i.succ.succ) := by
    funext i; exact redChain_succ u M i
  rw [hfun] at h
  exact h

/-! ## Step 1, atom (i): the head/row-split box factorization for `hsSplit` -/

/-- **The `hsSplit` box factorization.** `hsSplit M u κ` pulls the product box
`paramsBoxM (redChain u M) 1 ×ˢ matBox (M₁−u) M₂ 1` back to `paramsBoxM (tailChain M) 1`: the leading tail
layer's rows split (pivot rows → the leading `redChain` layer, corank rows → the `matBox` factor) via the
row bijection `blockSplitEquiv κ`, and the deeper layers pass through unchanged. The `hsSplit`-component
readbacks (`hsSplit_fst_zero`/`_succ`/`hsSplit_snd`, all `rfl`) reduce every membership to an entry bound
on `A'`. -/
theorem hsSplit_preimage_box (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (κ : Fin u ↪ Fin (M 1)) :
    hsSplit M u κ ⁻¹' (paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1)
      = paramsBoxM (tailChain M) 1 := by
  ext A'
  simp only [Set.mem_preimage, Set.mem_prod, paramsBoxM, matBox, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hfst, hsnd⟩ s i j
    -- `A' s i j` is bounded: for `s = 0` split rows by `blockSplitEquiv`, deeper layers pass through.
    rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s', rfl⟩
    · -- leading tail layer: every row of `A' 0` is a `blockSplitEquiv` image of a pivot or corank row
      obtain ⟨S, hS⟩ := (blockSplitEquiv κ).surjective i
      cases S with
      | inl a =>
        have := hfst 0 a j
        rw [hsSplit_fst_zero] at this
        rw [← hS]; exact this
      | inr b =>
        have := hsnd b j
        rw [hsSplit_snd] at this
        rw [← hS]; exact this
    · -- deeper layer: `hsSplit` passes it through unchanged
      have := hfst s'.succ i j
      rw [hsSplit_fst_succ] at this
      exact this
  · intro h
    refine ⟨fun s i j => ?_, fun i j => ?_⟩
    · rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s', rfl⟩
      · rw [hsSplit_fst_zero]; exact h 0 _ j
      · rw [hsSplit_fst_succ]; exact h s'.succ i j
    · rw [hsSplit_snd]; exact h 0 _ j

/-! ## Step 1, atom (ii) preparation: `freedSchurLoss` is invariant under a column reindex

The row-split integrand identity (atom (ii)) must relate `freedSchurLoss` at the tailChain column count
`M (Fin.last (L+1+1))` (the LHS `prod (tailChain M)` columns) to `hsQ`'s redChain column count
`dropHead (redChain u M) (Fin.last L)` — the same natural number, but propositionally (not defeq) equal
through the non-`rfl` `redChain_succ`. `freedSchurLoss` reads `Q` only through its two row-blocks, and its
value is a `frobSq` sum over the shared columns, so it is invariant under ANY column reindex `e`. This lets
the column cast be absorbed as a `finCongr`-`submatrix` at the point of use, decoupled from the chain
bookkeeping. -/

/-- `frobSq` is invariant under a column reindex by an equiv: `frobSq (M.submatrix id e) = frobSq M`
(the inner sum reindexes by `e`). -/
theorem frobSq_submatrix_id_cols {p q q' : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q' ≃ Fin q) :
    frobSq (M.submatrix (id : Fin p → Fin p) e) = frobSq M := by
  simp only [frobSq, Matrix.submatrix_apply, id_eq]
  exact Finset.sum_congr rfl (fun i _ => Equiv.sum_comp e (fun k => (M i k) ^ 2))

/-- Left-multiplication commutes with a column reindex: `A * (B.submatrix id e) = (A * B).submatrix id e`
(the reindex touches only `B`'s free columns, not the contracted index). -/
theorem mul_submatrix_id_cols {p r q q' : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin q) ℝ) (e : Fin q' ≃ Fin q) :
    A * (B.submatrix (id : Fin r → Fin r) e) = (A * B).submatrix (id : Fin p → Fin p) e := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq]

/-- **`freedSchurLoss` is invariant under a column reindex of `Q`.** For any equiv `e : Fin q' ≃ Fin q`,
`freedSchurLoss x Γ (Q.submatrix id e) = freedSchurLoss x Γ Q`. Both the pivot energy `frobSq(P·Q̃ₚ)` and
the corank energy `frobSq(C·Q̃ₚ + Γ·Q_b)` are `frobSq` sums over the shared columns, and every matrix
operation (row-block extraction, `+`, left-mul) commutes with the column reindex, so `frobSq` absorbs it
(`frobSq_submatrix_id_cols`). Chain-cast-free (`e` abstract) — the reusable bridge that lets atom (ii)
absorb the tailChain↔redChain column cast as `e = finCongr`. -/
theorem freedSchurLoss_submatrix_id_cols {t a b q q' : ℕ} (x : SJOuter t a b)
    (Γ : Fin a → Fin b → ℝ) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) (e : Fin q' ≃ Fin q) :
    freedSchurLoss x Γ (Q.submatrix (id : (Fin t ⊕ Fin b) → _) e) = freedSchurLoss x Γ Q := by
  unfold freedSchurLoss
  -- row-block extraction commutes with the column reindex
  have hinl : (Q.submatrix (id : (Fin t ⊕ Fin b) → _) e).submatrix Sum.inl id
      = (Q.submatrix Sum.inl (id : Fin q → Fin q)).submatrix (id : Fin t → Fin t) e := by
    ext i k; simp only [Matrix.submatrix_apply, id_eq]
  have hinr : (Q.submatrix (id : (Fin t ⊕ Fin b) → _) e).submatrix Sum.inr id
      = (Q.submatrix Sum.inr (id : Fin q → Fin q)).submatrix (id : Fin b → Fin b) e := by
    ext i k; simp only [Matrix.submatrix_apply, id_eq]
  rw [hinl, hinr]
  -- pull the reindex outward through `+` and left-mul, then `frobSq` absorbs it
  set Qinl := Q.submatrix Sum.inl (id : Fin q → Fin q) with hQinl
  set Qinr := Q.submatrix Sum.inr (id : Fin q → Fin q) with hQinr
  set K : Matrix (Fin t) (Fin b) ℝ := (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 with hK
  -- the shared inner factor `Q̃ₚ = Qinl + K·Qinr`, reindexed, is the un-reindexed one submatrixed
  have hinner : Qinl.submatrix (id : Fin t → Fin t) e + K * Qinr.submatrix (id : Fin b → Fin b) e
      = (Qinl + K * Qinr).submatrix (id : Fin t → Fin t) e := by
    rw [mul_submatrix_id_cols]
    ext i k; simp only [Matrix.submatrix_apply, Matrix.add_apply, id_eq]
  rw [hinner]
  -- pivot energy: `P · (Q̃ₚ.submatrix) = (P · Q̃ₚ).submatrix`, `frobSq` absorbs
  rw [mul_submatrix_id_cols, frobSq_submatrix_id_cols]
  -- corank energy: `C · (Q̃ₚ.submatrix) + Γ · (Qinr.submatrix)` factors out `.submatrix id e`
  rw [mul_submatrix_id_cols, mul_submatrix_id_cols]
  have hcomb : (Matrix.of x.2 * (Qinl + K * Qinr)).submatrix (id : Fin a → Fin a) e
        + (Matrix.of Γ * Qinr).submatrix (id : Fin a → Fin a) e
      = (Matrix.of x.2 * (Qinl + K * Qinr) + Matrix.of Γ * Qinr).submatrix (id : Fin a → Fin a) e := by
    ext i k; simp only [Matrix.submatrix_apply, Matrix.add_apply, id_eq]
  rw [hcomb, frobSq_submatrix_id_cols]

/-! ## Step 1, atom (ii) proper: the row-reindexed product IS `hsQ` at the actual deep factor -/

/-- The column-width bridge `dropHead (redChain u M) (Fin.last L) = tailChain M (Fin.last (L+1))`
(both `= M (Fin.last (L+1+1))`, the input width). -/
theorem dropHead_redChain_last_eq_tailChain_last (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) :
    dropHead (redChain u M) (Fin.last L) = tailChain M (Fin.last (L + 1)) := by
  rw [dropHead_redChain_last]
  simp only [tailChain, Fin.succ_last]

/-- **Step-1 atom (ii) proper — the row-reindexed cut-`u` front factor is `hsQ` at the actual deep
factor.** The leading-tail-layer product `prod (tailChain M) A'`, row-reindexed by `blockSplitEquiv κ`
(pivot rows → `κ`-image, corank rows → complement) and column-cast to the reduced-chain width, equals
`hsQ M u (deeperFlagZdeep M u) z A_cor` for `z = (hsSplit A').1`, `A_cor = (hsSplit A').2`. Both sides
factor `Q = rows · Z_deep` through the SAME (defeq) deep factor `Z_deep = prod (dropHead ·) (A' ∘ succ)`
(`dropHead (tailChain M) = dropHead (redChain u M)` by `rfl`); the pivot/corank row split is
`blockSplitEquiv κ` on `A' 0` (`hsSplit_fst_zero`/`hsSplit_snd`), and the only genuine cast is the shared
column width (`finCongr`). -/
theorem row_reindex_prod_eq_hsQ (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (κ : Fin u ↪ Fin (M 1))
    (A' : Params (tailChain M)) :
    (prod (tailChain M) A').submatrix (blockSplitEquiv κ)
        (finCongr (dropHead_redChain_last_eq_tailChain_last M u))
      = hsQ M u (deeperFlagZdeep M u) (hsSplit M u κ A').1 (hsSplit M u κ A').2 := by
  -- expose both products through the head split (the deep factor is defeq across the two chains)
  rw [prod_headSplit (tailChain M) A']
  unfold hsQ deeperFlagZdeep
  rw [prod_headSplit (redChain u M) (hsSplit M u κ A').1]
  ext I k
  rcases I with i | i
  · -- pivot rows: `blockSplitEquiv κ (Sum.inl i) = κ i`
    simp only [Matrix.submatrix_apply, Matrix.fromRows_apply_inl, blockSplitEquiv_inl,
      rmatMul, finCongr_apply]
    rfl
  · -- corank rows: `(hsSplit A').2 = A' 0 ∘ (complement)`, `of A_cor * Z`
    simp only [Matrix.submatrix_apply, Matrix.fromRows_apply_inr, rmatMul, finCongr_apply,
      Matrix.mul_apply, hsSplit_snd]
    rfl

/-- **The `freedSchurLoss` value identity (step-1 atom (ii)).** The shell-spine's freed loss at the
row-reindexed tailChain product equals the freed loss at `hsQ` (the reduced-chain corank stack at the
actual deep factor): absorb the column-count cast via the bridge (`freedSchurLoss_submatrix_id_cols`),
then the reindexed product IS `hsQ` (`row_reindex_prod_eq_hsQ`). -/
theorem freedSchurLoss_rowReindex_eq_hsQ (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (κ : Fin u ↪ Fin (M 1)) (A' : Params (tailChain M)) {a : ℕ} (x : SJOuter u a (M 1 - u))
    (Γ : Fin a → Fin (M 1 - u) → ℝ) :
    freedSchurLoss x Γ ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)
      = freedSchurLoss x Γ
          (hsQ M u (deeperFlagZdeep M u) (hsSplit M u κ A').1 (hsSplit M u κ A').2) := by
  rw [← row_reindex_prod_eq_hsQ M u κ A',
    ← freedSchurLoss_submatrix_id_cols x Γ
      ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)
      (finCongr (dropHead_redChain_last_eq_tailChain_last M u))]
  congr 1

/-! ## Step 1: the row-split reduction to the coupled full-box freed-loss integral -/

/-- **The coupled full-box freed-loss integrand** — the RHS of the step-1 reduction, as a function of the
reduced params `z` and the corank matrix `A_cor`. The corank block `Q_b = A_cor · deeperFlagZdeep z` is
the ACTUAL deep factor (COUPLED — no `sup_{A_cor}` pull-out), integrated over the FULL `matBox`
(NOT route-B's `pivotShell`). Brick F absent: `deeperFlagZdeep` is the actual measurable deep factor. -/
noncomputable def coupledBoxIntegrand (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (p : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ)) : ℝ≥0∞ :=
  ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
    ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
        Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
      ENNReal.ofReal
        ((freedSchurLoss x Γ (hsQ M u (deeperFlagZdeep M u) p.1 p.2)) ^ (-c'))

/-- **Step 1 (row-split → coupled full-box) — the coupled-incidence-route entry point.** The
shell-restricted spine integrand at a strict shell `j ≤ r = min(M₀−t, M₁−t)` is dominated by the coupled
`(z, A_cor)`-box freed-loss integral at the ACTUAL deep factor `Q_b = A_cor · deeperFlagZdeep z`, over the
FULL product box `paramsBoxM (redChain u M) 1 ×ˢ matBox (M₁−u) M₂ 1` (`u = t+j`). Route: drop the shell
indicator (`lintegral_mono_set`, a fortiori — off-shell is finite to T1 per incidence-cert §Verdict), then
the measure-preserving head/row split transports the `A'`-integral to the `(z, A_cor)`-product box
(`measurePreserving_hsSplit` + `setLIntegral_comp_preimage_emb`, consuming the box factorization
`hsSplit_preimage_box`), with the integrand identity `freedSchurLoss_rowReindex_eq_hsQ` exhibiting the
row-reindexed product as `hsQ`. This bypasses route-B's FALSE `shellSpine_le_hsQ_box` (which lands on
`matBox ∩ pivotShell`). Coupling KEPT (`Q_b = A_cor · deeperFlagZdeep z` joint); INTEGRATED not pointwise;
`hcT`/shell retained in the STATEMENT (dropped only in the a-fortiori bound). -/
theorem shellSpine_le_coupledBox (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) (ε c' : ℝ) (hj : j ≤ min (M 0 - t) (M 1 - t)) :
    shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
      ≤ ∫⁻ p in paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1,
          coupledBoxIntegrand M (t + j) c' p := by
  rw [shellSpineIntegrand]
  -- integrand identity: the shell-spine inner integral is `coupledBoxIntegrand ∘ hsSplit`
  have hval : ∀ A' : Params (tailChain M),
      (∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
            ENNReal.ofReal
              ((freedSchurLoss x Γ
                  ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-c')))
        = coupledBoxIntegrand M (t + j) c' (hsSplit M (t + j) κ A') := by
    intro A'
    rw [coupledBoxIntegrand]
    refine lintegral_congr fun x => lintegral_congr fun Γ => ?_
    rw [freedSchurLoss_rowReindex_eq_hsQ M (t + j) κ A' x Γ]
  calc ∫⁻ A' in paramsBoxM (tailChain M) 1
          ∩ {A' | prod (tailChain M) A'
              ∈ singularShell ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩},
        ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
            ENNReal.ofReal
              ((freedSchurLoss x Γ
                  ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-c'))
      ≤ ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
            ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
                Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
              ENNReal.ofReal
                ((freedSchurLoss x Γ
                    ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-c')) :=
        lintegral_mono_set Set.inter_subset_left
    _ = ∫⁻ A' in paramsBoxM (tailChain M) 1, coupledBoxIntegrand M (t + j) c' (hsSplit M (t + j) κ A') :=
        lintegral_congr hval
    _ = ∫⁻ p in paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1,
          coupledBoxIntegrand M (t + j) c' p := by
        rw [← hsSplit_preimage_box M (t + j) κ]
        exact (measurePreserving_hsSplit M (t + j) κ).setLIntegral_comp_preimage_emb
          (MeasurableEquiv.measurableEmbedding (hsSplit M (t + j) κ))
          (coupledBoxIntegrand M (t + j) c')
          (paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1)

/-! ## Step 2, atomic core: the coupled Γ-peel producing the corank charge `det(Q_bQ_bᵀ)^{−a/2}` -/

/-- **Step-2 pointwise Γ-peel — the coupled corank charge, per fixed front `x` and corank rows.** For the
freed Schur loss at any `Q` whose corank rows `Q_b = Q.submatrix Sum.inr id` have a `PosDef` Gram (full
row rank, a.e. in `A_cor` on the incidence route) and pivot energy `w = frobSq(P·Q̃ₚ) > 0` (a.e. in `x`,
since the stack is full row rank a.e.), the Γ-integral over any domain `s` produces the COUPLED corank
charge `det(Q_bQ_bᵀ)^{−a/2}` and shifts the exponent `c' → c'−ab/2`, leaving the transverse-Schur core
`(E_top + E_tr)`. Direct consumption of the banked `corankBlock_morsePeel_setLE` (`Apiv := 0`); the
COUPLED version — the det charge rides on `Q_b = A_cor · Z_deep` (no `sup_{A_cor}` pull-out, the route-B
error). `Q̃ₚ = Q_inl + P⁻¹·B₁₂·Q_inr`, `E_tr = frobSq(C·Q̃ₚ·(I − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b))` the transverse
Schur. -/
theorem freedSchurLoss_gammaPeel_le {u a b n : ℕ} (x : SJOuter u a b)
    (Q : Matrix (Fin u ⊕ Fin b) (Fin n) ℝ)
    (hG : ((Q.submatrix Sum.inr id) * (Q.submatrix Sum.inr id)ᵀ).PosDef)
    (c' : ℝ) (hc' : (a * b : ℝ) / 2 < c')
    (hw : 0 < frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)))
    (s : Set (Fin a → Fin b → ℝ)) :
    ∫⁻ Γ in s, ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c'))
      ≤ ENNReal.ofReal
          (((Q.submatrix Sum.inr id) * (Q.submatrix Sum.inr id)ᵀ).det ^ (-(a : ℝ) / 2)
            * Cresid (a * b) c'
            * (frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
                  + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
                + frobSq ((Matrix.of x.2 * (Q.submatrix Sum.inl id
                    + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
                  * (1 - (Q.submatrix Sum.inr id)ᵀ
                      * ((Q.submatrix Sum.inr id) * (Q.submatrix Sum.inr id)ᵀ)⁻¹
                      * (Q.submatrix Sum.inr id)))) ^ (-(c' - (a * b : ℝ) / 2))) := by
  set Qtp := Q.submatrix Sum.inl id
      + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id with hQtp
  set Qb := Q.submatrix Sum.inr id with hQb
  -- freedSchurLoss matches the atom's `w + frobSq Apiv + frobSq (Ccross + Γ·Qb)` with `Apiv = 0`
  have hz : frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) = 0 := by simp [frobSq]
  have hfree : ∀ Γ : Fin a → Fin b → ℝ,
      ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c'))
        = ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * Qtp)
            + frobSq (0 : Matrix (Fin 0) (Fin n) ℝ)
            + frobSq (Matrix.of x.2 * Qtp + (Matrix.of Γ) * Qb)) ^ (-c')) := by
    intro Γ
    rw [freedSchurLoss, hz, add_zero]
  rw [lintegral_congr hfree]
  refine le_trans (corankBlock_morsePeel_setLE (0 : Matrix (Fin 0) (Fin n) ℝ) (Matrix.of x.2 * Qtp)
    Qb hG c' hc' (frobSq (Matrix.of x.1.1 * Qtp)) hw s) (le_of_eq ?_)
  rw [hz, add_zero]

/-- **The pivot energy in polynomial form (on `IsUnit P`).** `P·Q̃ₚ = P·Q_p + B₁₂·Q_b = [P|B₁₂]·hsQ`,
free of the matrix inverse (`P·P⁻¹ = 1`). So the pivot energy `E_top = frobSq(P·Q̃ₚ)` is a POLYNOMIAL in
the front block `x = (P, B₁₂, C)` on the invertible-pivot chart — the form the `E_top > 0` a.e.
positivity (polynomial nonvanishing, à la `deeperFlagCore_decLoss_pos_ae`) needs; `Q̃ₚ`'s inverse would
otherwise block that machinery. -/
theorem pivotEnergy_stack_eq {u a b n : ℕ} (x : SJOuter u a b)
    (Q : Matrix (Fin u ⊕ Fin b) (Fin n) ℝ) (hP : IsUnit (Matrix.of x.1.1)) :
    Matrix.of x.1.1 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)
      = Matrix.of x.1.1 * Q.submatrix Sum.inl id + Matrix.of x.1.2 * Q.submatrix Sum.inr id := by
  have hdet : IsUnit (Matrix.of x.1.1).det := (Matrix.isUnit_iff_isUnit_det _).mp hP
  rw [Matrix.mul_add]
  congr 1
  rw [Matrix.mul_assoc (Matrix.of x.1.1)⁻¹ (Matrix.of x.1.2) (Q.submatrix Sum.inr id),
    ← Matrix.mul_assoc (Matrix.of x.1.1) (Matrix.of x.1.1)⁻¹,
    Matrix.mul_nonsing_inv (Matrix.of x.1.1) hdet, Matrix.one_mul]

/-! ## Step 2, integrated: the coupled corank charge over the front block -/

/-- **The front-charge integrand** — the coupled Γ-peel output at cut `u`, per reduced params `z` and
corank matrix `A_cor` (`p = (z, A_cor)`). Integrating the `Γ`-peel RHS (`freedSchurLoss_gammaPeel_le`,
`Q = hsQ M u deeperFlagZdeep p`) over the front block `x`: the COUPLED corank charge
`det(Q_bQ_bᵀ)^{−a/2}·Cresid(ab)c'` (`Q_b = A_cor·Z_deep`, a function of `p` — no pull-out) times the
transverse-Schur front loss `(E_top + E_tr)^{−q}`, `q = c'−ab/2`. Step 3 (the joint incidence charts)
resolves this `∫_x`. -/
noncomputable def frontChargeIntegrand (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (p : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ)) : ℝ≥0∞ :=
  ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
    ENNReal.ofReal
      ((((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id
            * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ).det
              ^ (-((M 0 - u : ℕ) : ℝ) / 2)
          * Cresid ((M 0 - u) * (M 1 - u)) c'
          * (frobSq (Matrix.of x.1.1
                * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inl id
                  + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2
                      * (hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id))
              + frobSq ((Matrix.of x.2
                  * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inl id
                    + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2
                        * (hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id))
                * (1 - ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ
                    * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id
                        * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ)⁻¹
                    * (hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)))
              ^ (-(c' - ((M 0 - u : ℕ) : ℝ) * ((M 1 - u : ℕ) : ℝ) / 2))))

/-- **Step 2 (per-`p`) — the coupled corank charge over the front block.** For a fixed reduced-param /
corank pair `p = (z, A_cor)` with corank Gram `Q_b·Q_bᵀ` PosDef (`Q_b = A_cor·Z_deep` full row rank — a.e.
in `A_cor` via `corank_survival_ae`, GIVEN the threaded deep-factor rank `b ≤ Z_deep(z).rank`), and pivot
energy `E_top > 0` a.e. in the front `x` (a.e. via `pivotEnergy_stack_eq` + polynomial nonvanishing, since
`hsQ ≠ 0`), the coupled box integrand is dominated by the front-charge integrand — the `Γ`-peel executed
pointwise a.e. (`freedSchurLoss_gammaPeel_le`), producing the COUPLED charge `det(Q_bQ_bᵀ)^{−a/2}` and the
exponent shift `c' → c'−ab/2`. The two a.e. hypotheses are the genericity content (`hEtop` reachable;
`hG` from the threaded rank, discharged by rankgen). -/
theorem coupledBox_le_frontCharge (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (p : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ))
    (hc' : ((M 0 - u : ℕ) : ℝ) * ((M 1 - u : ℕ) : ℝ) / 2 < c')
    (hG : ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id
        * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ).PosDef)
    (hEtop : ∀ᵐ x ∂(volume.restrict (outerDom u (M 0 - u) (M 1 - u) 1)),
        0 < frobSq (Matrix.of x.1.1
          * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2
                * (hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id))) :
    coupledBoxIntegrand M u c' p ≤ frontChargeIntegrand M u c' p := by
  rw [coupledBoxIntegrand, frontChargeIntegrand]
  refine lintegral_mono_ae ?_
  filter_upwards [hEtop] with x hx
  exact freedSchurLoss_gammaPeel_le x (hsQ M u (deeperFlagZdeep M u) p.1 p.2) hG c' hc' hx
    {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
      Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1}

/-- **Steps 1 + 2 composed — the coupled-route bound spine → front-charge.** The shell-restricted spine
integrand (strict shell `1≤j<r`) is dominated by the `(z, A_cor)`-box integral of the front-charge
integrand — the coupled corank charge `det(Q_bQ_bᵀ)^{−a/2}` (`Q_b = A_cor·Z_deep`, coupled) times the
front loss `(E_top+E_tr)^{−q}`. Composes `shellSpine_le_coupledBox` (step 1) with the per-`p`
`coupledBox_le_frontCharge` (step 2, `lintegral_mono_ae` over `p`). The two a.e.-`p` genericity
hypotheses (`hGae` corank Gram PosDef a.e.; `hEtopae` pivot energy `>0` a.e. in `x`, a.e. in `p`) are the
honest genericity content — `hGae` from the threaded deep-factor rank `b ≤ Z_deep(z).rank` + `corank_survival_ae`
(discharged by rankgen); `hEtopae` from `pivotEnergy_stack_eq` + polynomial nonvanishing. Ready for step 3
(the joint incidence charts resolve `frontChargeIntegrand`). -/
theorem shellSpine_le_frontCharge (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) (ε c' : ℝ) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (hc' : ((M 0 - (t + j) : ℕ) : ℝ) * ((M 1 - (t + j) : ℕ) : ℝ) / 2 < c')
    (hGae : ∀ᵐ p ∂(volume.restrict
        (paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1)),
        ((hsQ M (t + j) (deeperFlagZdeep M (t + j)) p.1 p.2).submatrix Sum.inr id
          * ((hsQ M (t + j) (deeperFlagZdeep M (t + j)) p.1 p.2).submatrix Sum.inr id)ᵀ).PosDef)
    (hEtopae : ∀ᵐ p ∂(volume.restrict
        (paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1)),
        ∀ᵐ x ∂(volume.restrict (outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1)),
          0 < frobSq (Matrix.of x.1.1
            * ((hsQ M (t + j) (deeperFlagZdeep M (t + j)) p.1 p.2).submatrix Sum.inl id
              + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2
                  * (hsQ M (t + j) (deeperFlagZdeep M (t + j)) p.1 p.2).submatrix Sum.inr id))) :
    shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
      ≤ ∫⁻ p in paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1,
          frontChargeIntegrand M (t + j) c' p := by
  refine le_trans (shellSpine_le_coupledBox M t j κ ε c' hj) (lintegral_mono_ae ?_)
  filter_upwards [hGae, hEtopae] with p hG hEtop
  exact coupledBox_le_frontCharge M (t + j) c' p hc' hG hEtop

end DLNFibre.DLN.RLCT
