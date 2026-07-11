# Statement card — AG-free free-matrix corank survival (#2 part b)

Piece #2 (part b) of the §5 decorated-descent discharge (thread `genm-sj5-desc2`,
`transversality-recursion.md §8`, controller's #2 (b)). The AG-free free-`A_cor` corank survival.

> **Claim (cert §8 / controller #2b).** For a FIXED deeper product `Zdeep` of rank `≥ b`, a.e. free
> corank block `A` satisfies `rank (A · Zdeep) = b` — genericity in the FREE integration variable
> `A` (minor-cut null set), NOT generic-rank-on-a-variety-component.
>
> - **Lean:** `DLNFibre.DLN.RLCT.corank_survival_ae` (+ the helper `ae_matrix_eval_ne_zero`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankSurvival.lean`, untracked @ `<HEAD>`; SHA on
>   controller integration).
> - **Gloss.** `{b m D : ℕ} (Zdeep : Matrix (Fin m) (Fin D) ℝ) (hb : b ≤ Zdeep.rank) :`
>   `∀ᵐ A : Fin b → Fin m → ℝ, (Matrix.of A * Zdeep).rank = b`. The rank of `Zdeep` is a HYPOTHESIS
>   (`b ≤ Zdeep.rank`), supplied combinatorially by #1's co-minimizing `ρ ≥ b`.
> - **Proved.** The full a.e. statement, unconditionally. `rank ≤ b` always (`b` rows,
>   `Matrix.rank_le_height`); the deficient set `{A | rank < b}` ⊆ zero-set of one fixed `b×b` minor
>   `det ((A·Zdeep).submatrix id ec)`, a nonzero `MvPolynomial` in `A` (nonzero at the one-hot
>   row-selection witness `A₀` on `er`), whose zero-set is Lebesgue-null. Axiom-clean
>   `[propext, Classical.choice, Quot.sound]`.
> - **Assumed.** `b ≤ Zdeep.rank` (from #1). No other hypotheses.
> - **Cited.** none. Banked pieces CONSUMED (all in-repo, sorry-free): `Core.RankLocusClosed`
>   (`exists_submatrix_det_ne_zero_of_le_rank`, `submatrix_det_eq_zero_of_rank_le`),
>   `Core.MeasureTheory.PolynomialZeroSet.MvPolynomial.ae_eval_ne_zero` /
>   `volume_zeroSet_eq_zero`, `RouteMSJCorankResidual.measurePreserving_eMatFlat`, `Matrix.map_mul`.
> - **Deferred (remaining #2 pieces).** (b→units) the **units bridge**
>   `full-row-rank ⟹ ∃c>0, Z·Zᵀ≽c·I` feeding route-A `corankLeaf_rpow_lt_top`'s `hZ`; (a) the
>   codim-decomposition `codim{A_piv·Zdeep=0}=min_r(δ_r+t·r)` over rank strata + (c) the tie to #1's
>   ρ. These wire `corank_survival_ae` into `adm ⟹ p=0` (with #3's adm def).
> - **AG-FREE confirmation (controller's watch-point).** Genericity is in the FREE variable `A`;
>   `Zdeep`'s rank is an INPUT; deficient locus is a minor-cut null set (Borel / measure). No
>   irreducible-component decomposition, no generic rank on a component. The AG wall (#114) does not
>   recur.
> - **Status.** sorry-free (awaiting cover fidelity review + controller integration).

## Design doc

`expeditions/2026-06-20-aoyagi-full/threads/genm-sj5-piece2-design.md` (the AG-free proof plan +
banked-piece map, now realised).
