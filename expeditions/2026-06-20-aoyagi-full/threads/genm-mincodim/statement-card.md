# Statement card — `minAdm = cCodim` (the central codimension identity, all widths)

Route-i Part 2 (the A-monotone bridge + all-width wire). Completes the QIP↔geometric-codim
equivalence machine-checked: the paper's central identity that the QIP combinatorial fibre codimension
equals the geometric (Ext/orbit) fibre codimension.

> **Claim.** For every width vector `M : Fin (L+1) → ℕ` with `1 ≤ L`, the QIP combinatorial minimum
> `minAdm M` equals the geometric fibre codimension `cCodim M 0` of the zero-product locus:
> `(minAdm M : ℤ) = cCodim M 0`. (Nonemptiness of the Kostant partition set is a hypothesis; no
> monotonicity or rank hypothesis on `M`.)
>
> - **Lean:** `DLNFibre.DLN.RLCT.minAdm_eq_cCodim`
>   (`lean/DLNFibre/DLN/RLCT/Validate/MinAdmCCodim.lean` @ `da4d264f`+ — new file, controller to pin the
>   integration SHA)
> - **Gloss.** `minAdm M = ((Adm M).inf' Mval).toNat` is Aoyagi's admissible-cone minimum of the candidate
>   value `M(T) = ∑_j (t^{j-1}−t^j)(M^{j+1}−t^j)` (the QIP side, `RouteMLayerSplit`). `cCodim M 0 h` is the
>   minimum of the Cor 3.5 quadratic form `codimForm (extendℤ m)` over the Kostant partitions `m` of `M`
>   with corner `0` (`Core.CTheta`) — the geometric codimension of `Σ̄^0` (`Core.SigmaCodim`). The theorem
>   states these two integers are equal for all `M` with at least two layers.
> - **Proved.** The equality `(minAdm M : ℤ) = cCodim M 0 h`, unconditionally in `M` (given `1 ≤ L` and
>   the Kostant set nonempty). Route: (i) the value-preserving map `eOfT M T c = ρ_c − ρ_{c+1}`
>   (`ρ = expSurvivor`) is a bijection `Adm M ↔ qipFeasible M` for monotone `M`, with
>   `Mval M T = Gqip M (eOfT M T)` (`Mval_eq_Gqip`); (ii) hence `minAdm (mono M) = qipMin M = cCodim M 0`
>   via the banked `cCodim_eq_qipMin`; (iii) the all-width form drops monotonicity by
>   `minAdm_comp_sort` (Part 1) + `cCodim_comp_sort`, applied to `M ∘ Tuple.sort M`. Value identity is the
>   banked signed ring identity `Mval = codimForm (diffRank (cascadeRank))` (`MvalMultSum`) matched against
>   the banked lace substitution `codimForm (mOfE) = Gqip` (`Core.CThetaQIP`): the two `codimForm`
>   arguments agree on the reads (the `diffRank ≥ 0` nonnegativity corollary the ring identity's docstring
>   flagged is discharged here, from admissibility + monotonicity, making the `ℕ`-valued lace array cast
>   faithfully). Axiom footprint `[propext, Classical.choice, Quot.sound]` (force-recompiled `#print
>   axioms`, no `sorryAx`).
> - **Assumed.** `1 ≤ L` (at least two layers — for `L = 0` the QIP feasible set / last-zero telescope
>   degenerate and the identity's `∑ e = M₀` feasibility fails); `(kostantPartitions M 0).Nonempty` (keeps
>   the LHS `cCodim` total, as in the rest of `Core.CTheta`). Both are hypotheses the informal claim also
>   needs.
> - **Cited.** None inside this identity. (The *downstream* RLCT reading `RLCT = ½·cCodim = ½·minAdm` rests
>   on the cited Aoyagi `RLCT = ½·codim`, named where it is used — not in this theorem.)
> - **Deferred.** None for the `r = 0` identity. The general-rank statement `minAdm(shifted) = cCodim M r`
>   is *already* covered by the banked rank-shift `cCodim_rankShift` (`cCodim M r = cCodim (M−r) 0`)
>   composed with this identity on the shifted widths — no new content owed.
> - **Structure & ideas observed (formaliser).** The reverse `qipFeasible → Adm` map `tOfE M e c = M₀ −
>   ∑_{j≤c} e_j` lands in `Adm` for monotone `M` because `M_{c+1} ≥ M_0` forces every staircase value
>   `≤ M_0 ≤ admBound` — monotonicity is used *exactly* at the reverse-map admissibility, nowhere else in
>   the bijection; the forward map + feasibility + value identity are monotonicity-free (feasibility uses
>   only admissibility's last-zero + `ρ` weak-decrease). The `codimForm`-read agreement is cleanest phrased
>   as two hypotheses matching the two factors `m(i−1,j−1)` (top-row `ρ_{j-1}−ρ_j`) and `m(u,v)`
>   (right-column `q_u−q_{u-1}`), NOT a full-box agreement — this sidesteps the never-read corner `(0,N)`
>   and lets the banked `extendℤ_mOfE_first/second` discharge the lace side directly.
> - **Route.** (controller/route-i cert `genm-sj5/minadm-perminv-cert.md` "Consequence".) The bridge is the
>   `inf'`-level value-preserving bijection `Adm M ↔ qipFeasible M` via `e_c = ρ_c − ρ_{c+1}`, routed
>   through the banked `mOfE`/`Gqip`/`codimForm_mOfE`/`cCodim_eq_qipMin` machinery rather than a direct
>   bijection to arbitrary Kostant partitions (the forward image is only the boundary-supported ones).
> - **Status.** sorry-free (fidelity review pending — controller-routed).

## Numeric non-vacuity witness

`minAdm_eq_cCodim_d222 : (minAdm ![2,2,2] : ℤ) = cCodim ![2,2,2] 0` (instance of the general theorem),
and `minAdm_d222_eq_three : minAdm ![2,2,2] = 3` — the QIP minimum equals the paper's `C = 3`
(Lehalleur–Rimányi Ex 4.3), obtained through the identity + the banked Kostant-side `cCodim ![2,2,2] 0 = 3`
(the two sides are computed by different machinery, so this is a genuine cross-check, not a tautology).

## Verification done before formalising

`/tmp/check_bridge.py` (numpy-free brute force): over all 434 weakly-increasing `M` with `L+1 ∈ {3,4,5}`,
entries `0..5`: the value identity `Mval M T = Gqip M (eOfT M T)`, `eOfT` nonnegativity + feasibility
`∑ = M₀`, the `Adm ↔ qipFeasible` bijection (injective + surjective), and `minAdm = min_e Gqip = qipMin`
all hold with 0 failures.
