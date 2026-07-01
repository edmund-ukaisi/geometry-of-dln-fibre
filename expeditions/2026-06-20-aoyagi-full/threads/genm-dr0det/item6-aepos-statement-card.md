# Statement card — item 6: a.e.-positivity of the `deepRank = 0` unit factor

> **Claim.** For a `deepRank = 0` (i.e. `Text 2 = 0`) interior stratum at `L = 2`, the unit factor of
> the E-block radial blow-up chart (`genBlkFlatEfp`) is a.e.-positive: for Lebesgue-a.e. `u`, the
> squared-Frobenius unit `V = VvalGen (u eBlockPivot) M (tach M) (genBlkFlatEfp ha hp1 hp2 u) hle` is
> strictly positive. Hypotheses: `ha : StructAdm M (tach M)`; the `deepRank = 0` witness `hdr0 : Text 2 = 0`;
> the front E-block non-degeneracy `hr : 0 < Text 1 − Text 2` and `hc : 0 < Wext 1 − Text 2`; the
> `rmatPad` shape bounds `hp1 : Text 2 ≤ Text 1`, `hp2 : Text 2 ≤ Wext 1`; the nonempty output column
> `hM2 : 0 < Wext 2`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.eDeepRank0Unit_ae_pos`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDeepRank0AePos.lean`, module uncommitted — controller
>   to wire into `DLNFibre.lean` + `AxCheck`).
> - **Gloss.** `∀ᵐ u, 0 < VvalGen (u (eBlockPivot ha hr hc)) M (tach M) (genBlkFlatEfp ha hp1 hp2 u)
>   (hleStruct M (tach M) ha)`. The unit is the sum-of-squares `∑∑ (Hr entry)²` of the telescoped chain
>   quotient of the E-fixed-pivot decoder (pivot E-slot pinned to `1`, other E-slots live). "a.e." is
>   w.r.t. the ambient Lebesgue `volume` on `Fin (routeMAmbient M) → ℝ`.
> - **Proved.** Unconditionally (given the seven hypotheses): the unit is `eval u` of a NAMED polynomial
>   `UPolyEfp` (via the Efp-decoder `GenBlkMap` + `chainOfMt_map` + `VvalGen_eq_sqSumHmat0`), that
>   polynomial is nonzero (interior-drop sparse witness `wInt M ha 1`, where the Efp decoder collapses to
>   the plain `genBlkFlatLive ha 0` since `EfixedReader (wInt 1) = readE (wInt 1) ⟨0⟩` — both the `(0,0)`
>   pivot indicator — and the surviving quotient entry `Hmat 0 (ρ, 0) = 1` is built by the banked
>   `Hmat_pivot`/`Hmat_row_thread`/`suffix_carrier` machinery), hence its zero set is Lebesgue-null
>   (`MvPolynomial.ae_eval_ne_zero`) and `V ≥ 0` (`VvalGen_nonneg`, sum of squares) upgrades `≠ 0` to `> 0`.
> - **Assumed.** The seven stated hypotheses. `hdr0`/`hr`/`hc`/`hM2` characterize the `deepRank = 0`
>   interior stratum at `L = 2` (they are exactly what makes `wInt M ha 1` a valid interior-drop witness:
>   `Text 2 = 0 < Text 1`, `Text 2 = 0 < Wext 1`, `0 < Wext 2`). No extra positivity/genericity assumed.
> - **Cited.** none (the nullity is the elementary `MvPolynomial.volume_zeroSet_eq_zero`; no S2 / analytic
>   interface).
> - **Deferred.** none — the statement is exactly the item-6 soundness pin the `deepRank = 0` handler
>   consumes.
> - **Route.** Codex xhigh route (a): single named nonzero polynomial + zero-set nullity + sum-of-squares.
>   Mirrors the LIVE-leaf template `RouteMUPolyLive.interiorLiveUnit_ae_pos`, adapted to the Efp decoder
>   (`Function.update` pivot-`Rmat` override) and the `deepRank = 0` witness (`wInt M ha 1`, pivot boundary
>   `p = 1`).
> - **Axioms.** `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`, olean deleted first).
> - **Status.** sorry-free + reviewed (reviewer verdict SURVIVED: fidelity YES, soundness gap-free YES,
>   axioms clean via forced recompile; decorrelated Codex xhigh concurred. `hM2` confirmed load-bearing.).
