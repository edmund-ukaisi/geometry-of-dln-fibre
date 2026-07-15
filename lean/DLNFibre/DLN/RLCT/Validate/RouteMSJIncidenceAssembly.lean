import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitDom
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

end DLNFibre.DLN.RLCT
