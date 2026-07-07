# Statement card — the general-`L` Schur-product LDU recursion (identity F2)

Thread `genm-sjldu`, sub-lemma 1 of the #120 `hstep2` runway (cert
`expeditions/2026-06-20-aoyagi-full/threads/genm-gauge120/cert.md`, identity **F2**).

> **Claim (F2).** For an `L`-layer chain of `2×2`-blocked matrices
> `C_s = fromBlocks (I_r+X_s) Y_s Z_s T_s` (an `r×r` regular pivot block, a core block of width
> `m_s`), the `(1,1)`-block Schur complement of the ordered product factors as the ordered product
> of per-layer Schur cores interspersed with unipotent corrections:
> `Sch(C_0·C_1·…·C_{L−1}) = S_0·(1−K_1)·S_1·(1−K_2)·S_2·…·(1−K_{L−1})·S_{L−1}`, where
> `S_s = Sch(C_s)` and `K_k = (C_k)₂₁·((P_k)₁₁)⁻¹·(P_{k−1})₁₂` with `P_k = C_0·…·C_k` (the cert's
> *inclusive* partial products). In the Lean encoding `partProd C j = C_0·…·C_{j−1}` (the first `j`
> layers), so `cert P_k = partProd C (k+1)` and `K_k = Kcoup C k` (see gloss below).
>
> - **Lean:** `DLNFibre.DLN.RLCT.schur_product_ldu_rec`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurRecursion.lean`, worktree `genm-sjldu`; base
>   `origin/expedition/aoyagi-full` @ `cff6cb50`; SHA to be pinned by the controller at integration).
> - **Gloss.** With a width family `m : ℕ → Type*` and a chain
>   `C : (s:ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s+1)) α` over a `CommRing α`:
>   - `partProd C k` is the honest matrix fold `C 0 · C 1 · … · C (k−1)` (`partProd C 0 = 1`,
>     `partProd C (k+1) = partProd C k * C k`), of block shape `(r ⊕ m 0) × (r ⊕ m k)`;
>   - `blockSchur P = P.toBlocks₂₂ − P.toBlocks₂₁ · (P.toBlocks₁₁)⁻¹ · P.toBlocks₁₂`
>     (the `(1,1)`-block Schur complement, total via `Ring.inverse`);
>   - `Kcoup C k = (C k).toBlocks₂₁ · ((partProd C (k+1)).toBlocks₁₁)⁻¹ · (partProd C k).toBlocks₁₂`
>     (the `K_k` coupling);
>   - `coreProd C k = S_0·(1−K_1)·…·(1−K_{k−1})·S_{k−1}` (the interspersed ordered product,
>     `coreProd C 0 = 1`, `coreProd C (k+1) = coreProd C k · (1 − Kcoup C k) · blockSchur (C k)`);
>   - then `blockSchur (partProd C L) = coreProd C L` for every `L`, given `Invertible` on every
>     layer pivot `(C k).toBlocks₁₁` for `k < L` and every partial-product pivot
>     `(partProd C k).toBlocks₁₁` for `k ≤ L`.
> - **Proved.** The full closed ordered-product identity, unconditionally over any `CommRing α`,
>   for all `L`, under the stated `Invertible` hypotheses. Axiom-clean
>   `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`, no `sorryAx`/`native_decide`).
>   Supporting reusable lemmas, all sorry-free: `blockSchur_mul` (the `toBlocks`-native two-factor
>   step), `blockSchur_partProd_succ` (the single-step chain recursion / last-layer peel),
>   `toBlocks₁₁_one`.
> - **Assumed.** Invertibility of every layer pivot (`k < L`) and every partial-product pivot
>   (`k ≤ L`), carried as explicit `Invertible` hypotheses — matching how the base case
>   `schur_product_ldu` carries `[Invertible (A0*A1+Y0*Z1)]`. The informal claim needs exactly
>   these (at the deepest point they hold since each `C_s(0) = blockdiag[I_r, 0]` forces
>   `(P_k)₁₁(0) = I_r`, invertible near 0).
> - **Cited.** The two-factor base case `DLNFibre.DLN.RLCT.schur_product_ldu`
>   (`DeepestSchurComparability`, sympy-verified, axiom-clean) — reused, not re-derived; it is the
>   step of the induction.
> - **Deferred.** The **analytic** facts are NOT in this file (by design; they are later sub-lemmas
>   of the `hstep2` runway): (i) the invertibility hypotheses hold *on a neighbourhood of 0* (the
>   `(P_k)₁₁(0)=I_r` continuity argument — sub-lemma 2); (ii) smoothness/`ContDiff` of `S_s`, `K_k`,
>   `Ψ` (sub-lemma 2); (iii) `dΨ(0)=I` (sub-lemma 3); (iv) the `rlctAtOn_comp_localDiffeo` bridge
>   (sub-lemma 4, interface already exists). Also **not** in this file: the `Fin (H k)`-side wiring
>   relating the DLN `prod`/`prodAux` to this abstract `fromBlocks` fold
>   (`DeepestBlockDecomp.reindex_mul_fromBlocks` is the connective; the L=2 grouping is banked, the
>   general-L grouping is a separate bridge step).
> - **Status.** sorry-free (pending reviewer fidelity check).

## Numeric sanity (pre-proof)

Identity F2 verified exact-symbolically by gauge120 (`codex/schur_ldu2.py`, non-commutative, L=3,4,
r,M∈{1,2}, uniform width) and re-verified here for **rectangular varying-width** chains
(`r=1, ms=[2,1,3,2]`; `r=2, ms=[1,2,1,2]`; `r=1, ms=[2,3,1,2,3]`; etc.) — all HOLD.

## Design notes

- **Why `m : ℕ → Type*` (not `Fin (H k)`).** The partial-product fold
  `partProd C (k+1) = partProd C k * C k` is **cast-free** because the shared middle type `r ⊕ m k`
  matches definitionally. This is the same abstraction the base case `schur_product_ldu` uses
  (abstract core types), and it sidesteps the `finCongr`/`prodAux` reindex cast-grind that the DLN
  `Fin (H k)` product carries. The mission brief anticipated that cast-grind as the hard part; the
  abstraction removes it. The single-step content is entirely the banked `schur_product_ldu`; the
  general-`L` theorem is its induction (peel the last layer).
- **`Ring.inverse` (total) in the `def`s**, bridged to `⅟` under `[Invertible]` via
  `Ring.inverse_invertible` inside `blockSchur_mul` — so `blockSchur`/`Kcoup`/`coreProd` are genuine
  `def`s (no threaded instance data), and the theorems carry the invertibility as hypotheses.

## Non-vacuity

In-file `example`: the constant identity chain (`r = Fin 1`, core `Fin 1`, over `ℚ`) satisfies all
`Invertible` hypotheses, so the theorem applies at `L = 3` (rules out vacuity-by-unsatisfiable
hypotheses). The `1 − K_k` corrections are genuinely nonzero for other chains — the `L = 2` instance
coincides with `schur_product_ldu`, whose file carries a `K ≠ 0`, `R − ∏S ≠ 0` witness.
