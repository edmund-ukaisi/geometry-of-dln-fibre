# G1 — fibre-`θ` count WITHOUT `Monotone d`

**Seat.** formaliser (tide). **Branch.** `expedition/rlct-g1` (off `expedition/rlct-foundation`).
**Status.** sorry-free; whole-library green; awaiting reviewer fidelity pass.

## Gap

The fibre-`θ` headline (`Core.FibreThetaCount.ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` and its
arbitrary-`B` transport `Core.FibreThetaCountArbitrary.ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_of_rank`)
counted the top-dimensional irreducible components of `mult⁻¹(B)` as the **closed form**
`cTheta (d − r)`, gated on `hd : Monotone d`. The paper's result holds for arbitrary (non-monotone)
dimension vectors; the task was to drop `Monotone`.

## What the gate actually was (recon)

The seven-rung count chain is `Monotone`-free at six rungs (W3←radical, poly, W2, chartE, W1, W0)
and at the `topComponents ↔ TopDimMinPrimes` bijection. `Monotone` enters at EXACTLY one place: the
E0 rung's closed-form evaluation `numTop d r = cTheta (d − r)`
(`Core.CThetaShiftCount.numTop_eq_cTheta_dminus`), which reads the **order-sensitive** prefix data of
`d`. The intermediate geometric count `numTop d r = #{top-dim components of Σ̄^r}`
(`Core.CCodimZeroStrict.numTop_eq_ncard_topComponents`) is already UNCONDITIONAL. So dropping the gate
= **stopping the headline at `numTop d r`** rather than evaluating to `cTheta (d − r)`. No fibration
transfer construction was needed; no new cite; no new deep math.

## Statement cards

> **Claim (E0 geometric half, `Monotone`-free).** For an algebraically closed field of characteristic
> `0`, the number of top-dimensional minimal primes of `O(Σ̄^r) = R ⧸ sigmaIdeal d r` equals the
> combinatorial minimiser count `numTop d r`, needing only `(kostantPartitions d r).Nonempty`.
>
> - **Lean:** `DLNFibre.Core.ncard_topDimMinPrimes_sigma_eq_numTop`
>   (`lean/DLNFibre/Core/TopComponentsTopDim.lean` @ `a98a4b76`)
> - **Gloss.** `(TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)).ncard = numTop d r hr'`.
> - **Proved.** The count identity, unconditionally in the order of `d`. Composes the
>   `topComponents ↔ TopDimMinPrimes` bijection (`ncard_topComponents_eq_ncard_topDimMinPrimes_sigma`)
>   with the unconditional `numTop_eq_ncard_topComponents`.
> - **Assumed.** `[IsAlgClosed k] [CharZero k]`; `(kostantPartitions d r).Nonempty` (the fibre is
>   nonempty). `[Infinite k]` resolves from `[CharZero k]`.
> - **Cited.** none.
> - **Deferred.** none. (`= cTheta (d − r)` is the separate `Monotone`-gated closed-form corollary.)
> - **Status.** sorry-free.

> **Claim (fibre-`θ`, normal-form target, `Monotone`-free).** For an ARBITRARY dimension vector `d`,
> the number of top-dimensional irreducible components of the fibre `mult⁻¹(E_r)` over the rank-`r`
> normal form equals `numTop d r`.
>
> - **Lean:** `DLNFibre.Core.ncard_topDimMinPrimes_fibre_eq_numTop`
>   (`lean/DLNFibre/Core/FibreThetaCountUnconditional.lean` @ `a98a4b76`)
> - **Gloss.** `(TopDimMinPrimes (R ⧸ fibreGenIdeal d (normalForm … r hp hq))).ncard = numTop d r h`.
> - **Proved.** The count identity for any `d`. Composes the six `Monotone`-free fibre rungs with the
>   `Monotone`-free E0-geometric rung above.
> - **Assumed.** `[IsAlgClosed k] [CharZero k]`; `hp : r ≤ d (last)`, `hq : r ≤ d 0` (bound `r` by the
>   endpoint dimensions, needed for the normal form to exist); `hN` (distinct endpoints, automatic for
>   the `Fin (N+2)` indexing); `(kostantPartitions d r).Nonempty`. Dropped vs the old headline:
>   `hd : Monotone d`, `hr : ∀ i, r ≤ d i`, `h₀ : (kostantPartitions (d − r) 0).Nonempty`.
> - **Cited.** none.
> - **Deferred.** the `numTop d r = cTheta (d − r)` closed-form evaluation — recovered exactly under
>   `Monotone d` via the existing `numTop_eq_cTheta_dminus`, so the old
>   `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` is a corollary; not re-stated here.
> - **Status.** sorry-free.

> **Claim (fibre-`θ`, arbitrary target `B`, `Monotone`-free).** For any `B` of rank `r` and an
> arbitrary `d`, `#{top-dim components of mult⁻¹ B} = numTop d r`.
>
> - **Lean:** `DLNFibre.Core.ncard_topDimMinPrimes_fibre_eq_numTop_of_rank`
>   (`lean/DLNFibre/Core/FibreThetaCountUnconditional.lean` @ `a98a4b76`)
> - **Gloss.** `(TopDimMinPrimes (R ⧸ fibreGenIdeal d B)).ncard = numTop d r h`, `hB : B.rank = r`.
> - **Proved.** Transports the normal-form headline along the LANDED `Monotone`-free same-rank
>   component-count invariance `ncard_topDimMinPrimes_fibre_eq_of_rank_eq` (`B` and `E_r` have equal
>   rank `r`).
> - **Assumed.** as the normal-form headline, plus `hB : B.rank = r`.
> - **Cited / Deferred.** as above.
> - **Status.** sorry-free.

## Non-vacuity (bedrock: witness shown in-file)

`dNonMono = ![1, 2, 1]` (`Fin 3`, so `N = 1`) is NOT monotone (`1 < 2 > 1`,
`not_monotone_dNonMono` by `decide`) yet `kostantPartitions dNonMono 0` is nonempty (4 elements,
`kostantPartitions_dNonMono_zero_nonempty` by `decide`). The theorem
`ncard_topDimMinPrimes_fibre_dNonMono_eq_numTop` instantiates the arbitrary-`d` headline at it over
`AlgebraicClosure ℚ` — a case the old `cTheta`-gated headline cannot even be stated. (Numerically:
`![2,1,2]` also non-monotone with `kostantPartitions … 0` of card 3.)

## Gates

- `scripts/lb DLNFibre` green (3835 jobs). `scripts/sorries` = `0 sorry / 0 #exit / 0 native_decide /
  0 axiom`.
- All four theorems axiom-clean `[propext, Classical.choice, Quot.sound]` — no new axioms/cites. The
  `decide` witnesses are kernel `decide`.

## Integration note for the controller

`lean/DLNFibre.lean` import added at END (sole-writer on this branch; the whole-library green gate
needed it). Existing import order untouched. The module is self-contained if you prefer to own that
edit on integration.
