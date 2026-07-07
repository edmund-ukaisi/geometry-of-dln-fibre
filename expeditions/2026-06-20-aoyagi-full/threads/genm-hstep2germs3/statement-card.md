# Statement card — the left-column half of Invariant A (`leftCol_movedC`), #120 `hstep2`

Thread `genm-hstep2germs3`. Delivers **Item 1** of the cert §6 build order (the flagged genuinely
`L`-recursive identity). The abstract joint move `movedC` (pivots fixed, up-edit all layers, one `Z₀`
override, cores) preserves the bottom-left block `(partProd)₂₁` of the full chain product — the down-half
of Invariant A. Together with the banked top-row half (`topRow_movedC`) this is the abstract heart of the
reg-preservation germ `hsub3reg` (`deepestEFull` invariant under the move).

Module: `lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiSplitGenLeftCol.lean`
(branch `genm-hstep2germs3` @ `9abecfaa`).

## The headline result

> **Claim.** For the general-`L` joint move `movedC C (Z0edit0 C L)` (the cert's `psiSplitRawGen` in
> abstract chain coordinates), with the specific `Z₀` override `Z0edit0 C L = Z_0 + ΔV_0·A_0`
> (`ΔV_0 = ∑_{j<L}(blockSchur(Q_j) − Ŵ_j)·V_j·N_j⁻¹·B_j⁻¹`, the cert's `a_L − ã_L`), the full product's
> reg-residual blocks are all preserved: `(P̂₁₁, P̂₁₂, P̂₂₁) = (P₁₁, P₁₂, P₂₁)`.

- **Lean:** `DLNFibre.DLN.RLCT.leftCol_movedC` and `DLNFibre.DLN.RLCT.regBlocks_movedC`
  (`lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiSplitGenLeftCol.lean`).
- **Gloss.**
  - `leftCol_movedC`: `(partProd (movedC C (Z0edit0 C L)) L).toBlocks₂₁ = (partProd C L).toBlocks₂₁`,
    for any chain `C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s+1)) α` over a `CommRing`, given every layer
    pivot `(C k)₁₁`, every partial-product pivot `(partProd C k)₁₁`, and every pivot-mix `nMix C k` is a
    unit, and `1 ≤ L`.
  - `regBlocks_movedC`: the conjunction of the two banked top-row equalities (`.₁₁`, `.₁₂`) with
    `leftCol_movedC` — all three reg-residual blocks preserved.
- **Proved.** Both theorems, sorry-free, axiom footprint `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`; forced `#print axioms`). Supporting lemmas, all axiom-clean:
  - `partProd_toBlocks₁₁_succ` : `B_{s+1} = B_s · N_s · A_s`.
  - `partProd_toBlocks₂₁_succ` : `D_{s+1} = D_s · N_s · A_s + blockSchur(Q_s) · Z_s` (needs only `A_s`
    invertible — the `B_s⁻¹` terms cancel formally).
  - `partProd_toBlocks₂₁_eq_leftAccum` : the closed form `D_L = leftAccum C L · B_L`.
  - `nMix_movedC` / `Kcoup_movedC` / `blockSchur_partProd_movedC` : the moved chain's data agrees with
    `C`'s (`N̂ = N`, `K̂ = K`, `blockSchur(Q̂_s) = wHatAccum C s`, the last `Z₀`-independent).
  - `leftAccum_movedC` : `leftAccum (movedC C (Z0edit0 C L)) L = leftAccum C L` (the `Z₀` accumulator
    exactly cancels the `Ŵ − blockSchur` mismatch).
- **Assumed.** The `IsUnit` hypotheses on every layer pivot, partial pivot, and pivot-mix, and `1 ≤ L`.
  These hold at the deepest point (every pivot is `I`, so `N = 1`), matching the cert's neighbourhood-of-
  origin scope. No hypothesis beyond what the informal claim needs.
- **Cited.** None. Pure `Matrix`/`Ring` algebra; builds on the banked `DeepestPsiSplitGenMoved`
  (`movedC`, `topRow_movedC`, `blockSchur_movedC`) and `DeepestSchurRecursion` (`schur_product_ldu_rec`).
- **Deferred.** The concrete DLN instantiation (Items 2–4 of cert §6): the `DeepestSplit`-coordinate
  map `psiSplitRawGen`, the `Fin`-side `framedParamsPivot ↔ partProd` reindex/cast bridge that transports
  `regBlocks_movedC` to `deepestEFull`, the analytic diffeo triple (`ContDiffAt`, `psi 0 = 0`,
  `D(psi − id)(0) = 0`), and the compose into `deepest_diffeo_bridge_gen_assembled` closing `hstep2` at
  `DeepestL2Wiring:1060`. `hstep2` is UNTOUCHED.
- **Structure & ideas observed (cert, genm-d1psidesign).** The move keeps pivots fixed, edits every
  up-block by `ΔY_s = N_s⁻¹ u_s (S_s − S̃_s)` (fixes the top row), and edits one down-block `Z₀` to cancel
  the accumulated left-column mismatch. Verified exactly `L ≤ 5, m ≤ 3, r ≤ 2` (sympy `codex_construction.py`,
  decorrelated Codex). This tide re-derived the cert's normalised accumulators into two clean non-normalised
  recursions (`B_{s+1} = B_s N_s A_s`, `D_{s+1} = D_s N_s A_s + blockSchur(Q_s) Z_s`) that avoid a Woodbury
  identity; re-verified exactly `L ≤ 5` (`sympy/lc_check.py`).
- **Route.** (formaliser, this tide.) Prove the closed form `D_L = leftAccum·B_L` for any chain, so
  preserving `P₂₁` reduces to `leftAccum (moved) L = leftAccum C L`; the moved chain's increments differ
  from `C`'s only by `blockSchur → Ŵ` (via the Schur recursion) and the `s = 0` down-edit, and the `Z₀`
  accumulator `Z0edit0` is defined to make the telescoped difference vanish.
- **Status.** sorry-free (pending reviewer fidelity check).
