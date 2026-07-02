# Statement card — general-`L` SMEARED chart-eval core + rank-`r` bottleneck front factorization

*Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedGenAtom.lean`, committed `0e510be3` on
`origin/genm-smeargen` (branched off `origin/expedition/aoyagi-full` @ `870f05f5`). Axiom-clean
`[propext, Classical.choice, Quot.sound]`; zero sorries.*

Goal context: discharge the general-`L` SMEARED branch of the achiever-dispatch spine's last caller
obligation `hSmeared : ∀ _ : 2 ≤ L, BoundarySmeared M → BoxDiverges M c' ε`
(`RouteMAchieverDispatch`). This card banks the two PROVED foundations toward that; the full
`SmearedAchieverChart M` builder is not yet closed (obstruction below).

---

> **Claim (chart-eval collapse, ∀ `L ≥ 1`).** For the general-`L` smeared chart — a free front tuple `A`
> with its deepest layer `L−1` overridden by the row-split factor `chartGenDeep` — the multiplication
> map collapses to the pure radial `z·(P₁·H̄)` off the shear cancellation `P₁·Λ₀ = P₂`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.prod_chartGen_collapse` (`RouteMSmearedGenAtom.lean` @ `0e510be3`).
> - **Signature (essential).** `(M : Fin (L+1)→ℕ) (A : Params M) (hL : 0 < L) {r s} (hrs : r + s = M ⟨L−1⟩) (z) (Hbar : Matrix (Fin r)(Fin (M (last L)))) (Sbot : Matrix (Fin s)(Fin (M (last L)))) (Λ₀) (e1 e2 : width-casts) (P₁ P₂) (hP₁ : P₁ = frontProd[:, inl via deepWidthEquiv]) (hP₂ : P₂ = frontProd[:, inr]) (hcancel : P₁·Λ₀ = P₂) : prod M (chartGenParams … ) = z • (P₁ * Hbar)`.
> - **Gloss.** `frontProd M A hL := prodAux M A (L−1)` is the prefix product `A⁰·…·A^{L−2}`. The
>   last-layer peel `prod = frontProd · A^{L−1}` (`prod_eq_frontProd_mul_deep`, native `prodAux_succ`)
>   plus the SAME single `deepWidthEquiv (r+s = M_{L−1})` sum-reindex + banked `deepBlock_collapse`
>   gives the identical rate as the L=2 `prod_chartL2Params`. The only `L ≥ 3` novelty: `frontProd` is a
>   PRODUCT of layers, not the single free `A⁰`.
> - **Proved.** The collapse, for every `L ≥ 1`, from `hcancel` alone (pure matrix ring algebra).
> - **Assumed.** `hcancel : P₁·Λ₀ = P₂` (the shear cancellation — a hypothesis here; supplied off-pole
>   by `staircase_cancel` below in the intended chart). Width casts `e1`/`e2` (`rfl`-true).
> - **Cited.** none (`deepBlock_collapse`, `prodAux_succ`, `deepWidthEquiv` are landed).
> - **Status.** sorry-free, axiom-clean.

> **Claim (rank-`r` bottleneck front factorization = de-risk (b) in Lean).** For a `C·[I_r|K]` front
> (`C` a FREE `M 0 × r` block, `K` the `r × s` routing block), the column split gives `P₁ = C`,
> `P₂ = C·K = P₁·K`, and the shear cancellation `P₁·Λ₀ = P₂` fires off `det(CᵀC) ≠ 0`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.idKGate` / `mul_idKGate_split` / `staircase_cancel` (same file / SHA).
> - **Signature (`staircase_cancel`).** `(C : Matrix (Fin m0)(Fin r)) (K : Matrix (Fin r)(Fin s)) (P₁ P₂) (hP₁ : P₁ = (C·idKGate K)∘inl) (hP₂ : P₂ = (C·idKGate K)∘inr) (hdet : (Cᵀ·C).det ≠ 0) : P₁ * ((P₁ᵀP₁)⁻¹P₁ᵀP₂) = P₂`.
> - **Gloss.** `idKGate K = [I_r | K] : Matrix (Fin r)(Fin r ⊕ Fin s)`. `mul_idKGate_split` proves the
>   column split `(C·G)∘inl = C`, `(C·G)∘inr = C·K` (so `P₁ = C` FREE, `col(P₂) ⊆ col(P₁)`).
>   `staircase_cancel` then reads `P₂ = P₁·K` and fires the banked `proj_cancel_of_factorsThrough` off
>   `det(CᵀC) ≠ 0`. This is exactly the de-risk (b) reduction: `det(P₁ᵀP₁) = det(CᵀC)` on the conditioned
>   box reduces to the SAME free-block diagonal dominance as the L=2 `subBox_det_ne`, and the tall-`P₁`
>   cancellation holds on a FREE `P₁`.
> - **Proved.** The split + the cancellation, sorry-free.
> - **Assumed.** `hdet : det(CᵀC) ≠ 0` (the free-block Gram off-pole condition — a genuine null-set
>   hypothesis the conditioned box supplies; not fabricated).
> - **Cited.** none (`proj_cancel_of_factorsThrough` is landed, `RouteMSmearedProjCancel`).
> - **Status.** sorry-free, axiom-clean.

## De-risk (b) verdict: THREADS

The one open Lean-feasibility piece the design flagged — the front-staircase rank-`r` factorization
`frontProd = C·[I_r|K]` reducing the Gram nondegeneracy to the L=2 free-block diagonal dominance — is
CONFIRMED. Verified exact (sympy L=2..5, 7 cases): the naive truncated-identity chart FAILS the factoring
(`rank(frontProd) > r`); the `[C|0]` rank-`r` bottleneck (`A⁰=[C|0]`, interiors `carry_r`,
`A^{L−2}=[I_r|K;0]`) is load-bearing and gives `frontProd = C·[I_r|K]`. Structural: `r = deepRank ≤ M_k`
for every front width `k=0..L−1` (0/330 smeared M violate), so the staircase always has `r` slots.

## Obstruction (what the `SmearedAchieverChart M` builder still owes)

The consumer `routeMCore_box_diverges_of_smearedChart` (`RouteMSmearedAchieverGeneral`) is already ∀L and
takes the structure verbatim. The remaining pieces, each a substantial cast-heavy build:

1. **The flat `L`-layer decode** (`genDecode_params`): `packM (shearMBody (R u)) = chartGenParams M A_base
   … C K z H̄ S_bot Λ₀`, generalizing the ~765-line `Fin 3`-hardcoded `RouteMSmearedDecodeL2.decode_params`
   to `Fin L` layers. Codex-reviewed clean route: keep interior `carry_r` staircase as CONSTANTS in a
   fixed `A_base`; the decode need only hit free layers `0, L−2, L−1`; constant layers fall out of
   `shearMBody_apply_of_not_mem`. Riskiest cast: the `deepWidthEquiv` row-split at layer `L−1` (isolate in
   one `deepest_slot_split_spec` lemma).
2. **General-`r` det/U positivity on the conditioned box**: `det(CᵀC) ≠ 0` and `Uy = ‖C·H̄‖² > 0` — the
   general-`r` free-block diagonal dominance (the L2 `subBox231_det_ne` is `det_fin_two`-specific). Set `C`
   = staircase-identity-plus-small on the conditioned box ⟹ `CᵀC = I_r + small`, positive-definite.
   **Codex subtlety (load-bearing):** `K`'s coords must be FREE spectators (sheared, NOT radial-active),
   else the radial det exponent exceeds `minAdm − 1`.
3. **Assembly** into `SmearedAchieverChart M` + `hSmeared_of_smearedChart` wiring (mechanical once 1–2 land).

`minAdm M = deepRank·M_L = r·c` is banked (`minAdm_eq_deepRank_mul_last`), giving the radial exponent
`h = r·c − 1 = minAdm − 1`. The rate core (this card's claim 1) + the cancellation (claim 2) are the
foundations these consume.
