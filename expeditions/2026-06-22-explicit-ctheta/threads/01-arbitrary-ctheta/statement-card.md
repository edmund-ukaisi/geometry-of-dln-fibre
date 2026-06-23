# Statement card — explicit `(C, θ)` for an arbitrary dimension vector

*Module: `lean/DLNFibre/Core/CThetaArbitrary.lean`, committed at `d6fb6ba` (feat commit). PR #7 → `dev`.*

---

> **Claim (r = 0, C).** For any dimension vector `d : Fin (N+1) → ℕ` with `1 ≤ N`, the combinatorial
> codimension of the zero-product locus equals the closed form `cValue` evaluated on the monotone
> rearrangement `d ∘ Tuple.sort d` — no `Monotone d` hypothesis.
>
> - **Lean:** `DLNFibre.Core.cCodim_zero_eq_cValue_comp_sort`
>   (`lean/DLNFibre/Core/CThetaArbitrary.lean` @ `d6fb6ba`)
> - **Signature.** `(hN : 1 ≤ N) (d : Fin (N+1) → ℕ) (h : (kostantPartitions d 0).Nonempty) : cCodim d 0 h = cValue (d ∘ Tuple.sort d)`
> - **Gloss.** `cCodim d 0` (min of `codimForm` over corner-`0` Kostant partitions of `d`) equals the
>   Thm 7.10 closed form `cValue` applied to the weakly-increasing reordering of `d`. The LHS keeps an
>   abstract nonemptiness hypothesis `h`; the sorted-side nonemptiness is discharged internally from
>   `1 ≤ N`.
> - **Proved.** The equality, for every `d` (the `Monotone` gate of `cCodim_eq_qipMin` /
>   `qipMin_eq_cValue` is removed by composing with the sort bridge `cCodim_comp_sort` and
>   `Tuple.monotone_sort`).
> - **Assumed.** `1 ≤ N` (needed for `kostantPartitions_nonempty_of_le` and `abs_qipDelta_le_m`);
>   `(kostantPartitions d 0).Nonempty` (the locus is non-degenerate).
> - **Cited.** none (all bricks are landed `Core` lemmas).
> - **Deferred.** none for `r = 0`.
> - **Status.** sorry-free.

> **Claim (r = 0, θ).** Same hypotheses; the combinatorial top-component count equals `cTheta` on the
> monotone rearrangement.
>
> - **Lean:** `DLNFibre.Core.numTop_zero_eq_cTheta_comp_sort` (same file / SHA)
> - **Signature.** `(hN : 1 ≤ N) (d) (h : (kostantPartitions d 0).Nonempty) : numTop d 0 h = cTheta (d ∘ Tuple.sort d)`
> - **Gloss.** `numTop d 0` (count of `codimForm`-minimising corner-`0` Kostant partitions) equals
>   `cTheta = C(m, |δ|)` on the sorted vector.
> - **Proved / Assumed / Cited / Deferred.** As above; `Status: sorry-free`.

> **Claim (general r, C).** For `1 ≤ N`, the codimension of `Σ̄^r` equals `cValue` on the sorted
> shifted vector `(d − r) ∘ Tuple.sort (d − r)`. The rank bound `r ≤ d k` is NOT assumed — it is
> forced by the Kostant set being nonempty.
>
> - **Lean:** `DLNFibre.Core.cCodim_eq_cValue_comp_sort` (same file / SHA)
> - **Signature.** `(hN : 1 ≤ N) (d) (r) (h : (kostantPartitions d r).Nonempty) : cCodim d r h = cValue (dminus d r ∘ Tuple.sort (dminus d r))`
> - **Gloss.** Rank-`r` codimension = closed form on the sorted *rank-shifted* vector `d − r`
>   (`dminus d r = fun k ↦ d k − r`). Routes through `cCodim_rankShift` to the `r = 0` result on
>   `d − r`. The `cCodim_rankShift` precondition `∀ k, r ≤ d k` is derived internally from `h` via
>   `corner_le_dim_of_mem` (a corner-`r` Kostant partition forces `r ≤ d k`), so it is not a
>   user-supplied hypothesis — the weakest honest form.
> - **Proved.** The equality, for every `d` (via `cCodim_rankShift` then the `r = 0` theorem on
>   `dminus d r`).
> - **Assumed.** `1 ≤ N`; `(kostantPartitions d r).Nonempty`. (The rank bound is a *consequence* of
>   the latter, not an assumption.)
> - **Cited / Deferred.** none.
> - **Status.** sorry-free.

> **Claim (general r, θ).** Same hypotheses; `numTop d r = cTheta ((d − r) ∘ Tuple.sort (d − r))`.
>
> - **Lean:** `DLNFibre.Core.numTop_eq_cTheta_comp_sort` (same file / SHA)
> - **Signature.** `(hN : 1 ≤ N) (d) (r) (h : (kostantPartitions d r).Nonempty) : numTop d r h = cTheta (dminus d r ∘ Tuple.sort (dminus d r))`
> - **Proved / Assumed / Cited / Deferred.** As the general-`r` C case (rank bound derived from `h`,
>   not assumed); `Status: sorry-free`.

---

## Witness (non-monotone, shown in-file)

`d = ![2,3,2]` is genuinely non-monotone (`not_monotone_d232`: `d 1 = 3 > 2 = d 2`). The Kostant side
computes `cCodim ![2,3,2] 0 = 4` (`cCodim_d232_zero`) and `numTop ![2,3,2] 0 = 2` (`numTop_d232_zero`)
by `decide +kernel`. The bridge instances `cCodim_d232_eq_cValue_comp_sort` /
`numTop_d232_eq_cTheta_comp_sort` apply the arbitrary-`d` theorems to this non-monotone vector. The
closed-form-on-sorted side is `cValue_d232_comp_sort = 4` and `cTheta_d232_comp_sort = 2`: since
`Tuple.sort` is not kernel-reducible, `d232_comp_sort` rewrites `![2,3,2] ∘ sort` to the concrete
monotone `![2,2,3]` (via the swap `(1 2)` and `Tuple.comp_sort_eq_comp_iff_monotone`), then
`decide +kernel`. Both sides land on `(C, θ) = (4, 2)`, matching the permutation-invariance
expedition.

## Axioms

Every new theorem: `[propext, Classical.choice, Quot.sound]` (`not_monotone_d232`: `[propext]`).
No `sorryAx`, no `native_decide`.

## Key Mathlib lemma

`Tuple.monotone_sort (f : Fin n → α) : Monotone (f ∘ Tuple.sort f)`
(`Mathlib/Data/Fin/Tuple/Sort.lean`), with `Tuple.comp_sort_eq_comp_iff_monotone` used for the
concrete-witness rewrite.
