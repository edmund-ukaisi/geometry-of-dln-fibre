# Statement card — FrontPivotWLOG (b-wlog-spec.md lemmas 1–4)

The column-permutation WLOG machinery: the headline-level `rlctAt`-invariance under a column
permutation of `B`, used to discharge the gauge chart's front-pivot hypothesis `hJfront`. INDEPENDENT
of the gauge chart / producer / `hfin` — purely `dlnLoss` + the column permutation + the banked
`rlctAtOn`-MP-invariance.

All four lemmas live in `lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean` (a NEW self-contained
module; NOT yet wired into the `DLNFibre.lean` aggregator — controller wires it). Built atop merge of
`origin/expedition/aoyagi-full` @ `66fa6c78`; module file currently **untracked** (single-writer
controller integrates — pin the SHA at commit time).

The transfer route uses the **exact reindexing identity** (NOT an orthogonal-Frobenius argument):
`prod (τ_P A) = (prod A).submatrix id P`, where `τ_P = paramColPermLast` right-multiplies the last
layer's columns by `P`. The square-Frobenius loss against `B.submatrix id P` then reindexes exactly to
the loss against `B` by summing the squared entries over the permuted column index.

---

## Lemma 1 — `front_pivot_perm_exists`

> **Claim.** A rank-`r` matrix `B` admits a column permutation `P` bringing `r` linearly-independent
> columns to the front `{0..r-1}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.front_pivot_perm_exists`
> - **Gloss.** For `B : Matrix (Fin H0) (Fin n) ℝ` with `B.rank = r`, there exist a permutation
>   `P : Equiv.Perm (Fin n)` and `hrn : r ≤ n` such that `(B.submatrix id P).rank = r` AND the first
>   `r` columns of `B.submatrix id P` (the submatrix at `Fin.castLE hrn : Fin r → Fin n`) have rank `r`.
> - **Proved.** Both rank facts, unconditionally. Column selection via a maximal independent subfamily
>   of `B.col` (`exists_linearIndependent'` + `finrank_span_eq_card`); the embedding `J` extended to a
>   permutation fronting `range J` via `Equiv.extendSubtype`; the front-pivot rank from
>   `submatrix_submatrix` collapsing `P ∘ castLE = J`.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Lemma 2 — `dlnLoss_colPerm_eq`

> **Claim.** The DLN loss is invariant under (column-permute `B`, apply `τ_P` to params).
>
> - **Lean:** `DLNFibre.DLN.RLCT.dlnLoss_colPerm_eq`
> - **Gloss.** For `hL : 1 ≤ L`, target `B`, permutation `P`, params `A`:
>   `dlnLoss H B A = dlnLoss H (B.submatrix id P) (paramColPermLast H hL P A)`.
> - **Proved.** Exact equality. Via `prod_paramColPermLast` (helper:
>   `prod (paramColPermLast P A) = (prod A).submatrix id P`, by single-layer-update tracking through
>   the matrix-chain product) + `Equiv.sum_comp P` reindexing the squared-entry sum over the columns.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Lemma 3 — `paramColPermLast_measurePreserving`

> **Claim.** `τ_P` is measure-preserving on the parameter space.
>
> - **Lean:** `DLNFibre.DLN.RLCT.paramColPermLast_measurePreserving`
> - **Gloss.** `MeasurePreserving (paramColPermLast H hL P) volume volume` on `Params H`.
> - **Proved.** Unconditionally. `τ_P` is `Function.update`-of-the-identity by a column permutation of
>   the last layer; `volume_preserving_pi` over layers (identity off the last; per-row
>   `MeasurableEquiv.piCongrLeft` compose-MP on the last).
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Lemma 4 — `rlct_infimum_colPerm_eq`

> **Claim.** The `⨅`-over-`optimalSet` RLCT is invariant under a column permutation of `B`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.rlct_infimum_colPerm_eq`
> - **Gloss.** `(⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ⨅ w ∈ optimalSet H (B.submatrix id
>   P), rlctAt H (dlnLoss H (B.submatrix id P)) w`.
> - **Proved.** Unconditionally. `τ_P` as a homeomorphism `Params H ≃ₜ Params H` (continuous +
>   continuous inverse `τ_{P⁻¹}`), measure-preserving (lemma 3), a measurable embedding; the banked
>   `rlctAtOn_comp_homeomorph` (`S1Fubini:54`) + `rlctAtOn_eq_rlctAt` give the per-point identity
>   `rlctAt (dlnLoss (B·P)) (τ_P w) = rlctAt (dlnLoss B) w`; `τ_P` is a `Set.BijOn` between the
>   loss-zero sets (lemma 2); `Set.BijOn.iInf_congr` transfers the infimum. Choice-independent —
>   no deepest-point equivariance, exactly the headline's `⨅`-form (the cert's soundness-subtlety
>   resolution).
> - **Cited.** `rlctAtOn_comp_homeomorph` (banked, `S1Fubini.lean`) — the MP-homeomorph germ-invariance.
> - **Assumed / Deferred.** none.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

## NOT in scope (per the task)

- **Lemma 5** (the headline `rw` for general non-front `B`) and the squeeze-exists relocation /
  case-split — the controller-coordinated final wire, after the producer + this land.
- Wiring `FrontPivotWLOG` into `DLNFibre.lean` (single-writer aggregator) — controller wires it.

## Numerical sanity (SPECIFY step)

`/tmp/wlog_sanity.py` (numpy, independent of the cert's sympy): the product identity
`prod(τ_P A) = (prod A).submatrix id P` is machine-exact (L=2,3; several widths), the loss reindexes
exactly, and the front-pivot column permutation exists with the front `r` columns at rank `r` (QR-pivot
construction across `H0,n,r` cases). Matches the cert's L=2 sympy checks.
