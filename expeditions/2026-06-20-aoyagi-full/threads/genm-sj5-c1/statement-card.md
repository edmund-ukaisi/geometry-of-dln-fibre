# Statement card — (c1) deep-factor generic rank

The last `hGae`-discharge input (rankgen cert route (c), `genm-rankgen/rankgen-cert.md` §4). Delivered on
branch `genm-sj5-c1` (off the capstone base `@12a7ae38a`).

> **Claim (c1).** For a.e. `z` in the reduced-params box `paramsBoxM (redChain u M) 1`, the deep-layer
> product `deeperFlagZdeep M u z` (the `M₂ × M_last` product of the deep chain `M₂,…,M_last`) attains its
> generic rank `deepTailMin M = min(M₂,…,M_last) = ⨅_i M i.succ.succ`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deeperFlagZdeep_rank_ge_min_ae`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDeepRankGeneric.lean` @ `6b5a7d5ea`)
> - **Gloss.** `∀ᵐ z ∂(volume.restrict (paramsBoxM (redChain u M) 1)), (⨅_{i:Fin (L+1)} M i.succ.succ) ≤ (deeperFlagZdeep M u z).rank`.
>   The LHS `(Finset.univ).inf' ⟨0,_⟩ (fun i => M i.succ.succ)` is **definitionally** `deepTailMin M`
>   (`RouteMSJIncidenceAssembly.lean:57` — identical expression; the raw `⨅` form is used to avoid importing
>   the heavy `IncidenceAssembly`).
> - **Proved.** The full a.e. statement, unconditionally in `M, u` (no width or binding-cut hypotheses:
>   when `deepTailMin M = 0` the bound is trivial `0 ≤ rank`; when `≥ 1` all deep widths are `≥ 1` and the
>   generic rank equals the min width). Sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.
>   Reusable network-free engine: `prod_rank_ge_chainInf_ae {n} (C : Fin (n+1) → ℕ) : ∀ᵐ p ∂(volume :
>   Params C), (⨅_s C s) ≤ (prod C p).rank` (a generic point of any chain product attains its min-width rank).
> - **Assumed.** none (in this lemma).
> - **Cited.** none new. Consumes banked infra: `prodPolyAux`/`coreXmat`/`prodPolyAux_map` +
>   `measurePreserving_paramsEquivFlat` (`DeepestCoreNonvanishing`/`ParamsFlat`), `MvPolynomial.ae_eval_ne_zero`
>   (`Core.MeasureTheory.PolynomialZeroSet`), `Core.submatrix_det_eq_zero_of_rank_le` (`Core.RankLocusClosed`),
>   `paramsHeadSplit_mp` (`RouteMSJHeadSplit`), `Measure.quasiMeasurePreserving_snd` (Mathlib).
> - **Deferred.** The composition to the consumer's `hZrank : ∀ᵐ z, M 1 - u ≤ rank` needs the Nat bound
>   `M 1 - u ≤ deepTailMin M` (rankgen route (b′), the binding-cut lemma) — built in a separate lane, NOT here.
>   Given that bound, `deeperFlagZdeep_rank_ge_min_ae` discharges `hGae_from_deepRank`'s `hZrank`
>   (verified end-to-end: `hGae_from_deepRank M u (by filter_upwards [deeperFlagZdeep_rank_ge_min_ae M u]
>   with z hz; exact le_trans hb hz)` compiles).
> - **Route.** Mirrors `corank_survival_ae` / the `corePoly` encoding. (i) The **staircase** witness
>   `stairWitness C` (each layer `= 1_{(i:ℕ)=(j:ℕ)}`) makes the top-left `ρ×ρ` block of `prod C stairWitness`
>   the identity (`prodAux_stairWitness_diag`, induction on chain length picking the `l = ⟨(j:ℕ)⟩` summand),
>   so the `ρ×ρ` minor determinant is `1 ≠ 0`. (ii) Hence the minor polynomial
>   `Q = det((prodPolyAux C (coreXmat C) n).submatrix er ec)` is a NONZERO `MvPolynomial (Fin (flatDim C)) ℝ`;
>   `MvPolynomial.ae_eval_ne_zero` + `measurePreserving_paramsEquivFlat C` ⟹ minor a.e. nonzero ⟹ `rank ≥ ρ`
>   a.e. (`Core.submatrix_det_eq_zero_of_rank_le`, contrapositive). (iii) Transport to `deeperFlagZdeep` via
>   the measure-preserving head split (`paramsHeadSplit_mp`) ∘ `Measure.quasiMeasurePreserving_snd`, using
>   `deeperFlagZdeep M u z = prod (dropHead (redChain u M)) (paramsHeadSplit (redChain u M) z).2` and
>   `⨅_s (dropHead (redChain u M)) s = deepTailMin M`; then `ae_restrict_of_ae` to the box.
> - **Status.** sorry-free (fidelity review requested).
