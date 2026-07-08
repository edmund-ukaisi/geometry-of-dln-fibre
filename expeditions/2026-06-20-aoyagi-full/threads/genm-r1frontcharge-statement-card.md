# Statement card — the FRONT-PEEL identity for `minAdm`

> **Claim.** For a `≥ 3`-width chain `M = (M₀,…,M_L)`, the minimal admissible codim satisfies the
> front-peel identity
> `minAdm M = min_{q ≤ min(M₁,…,M_L)} [ M₀·q + minAdm (M₁−q, M₂−q, …, M_L−q) ]`,
> and each term dominates: `minAdm M ≤ M₀·q + minAdm ((M₁,…,M_L) − q)` for every `q ≤ tailMin M`.
> (cert `expeditions/2026-06-20-aoyagi-full/threads/genm-r1substratum/cert.md` §C.)
>
> - **Lean:** `DLNFibre.DLN.RLCT.minAdm_eq_frontPeel`, `DLNFibre.DLN.RLCT.frontCharge_ge_minAdm`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMFrontPeelCharge.lean` @ `89d4823c`)
>   - supporting: `twoVar_min_eq` (the 2-variable min keystone), `tailMin`, `frontCharge`,
>     `inf'_univ_sub_right`, `le_tailMin_iff`, `tailMin_split`.
> - **Gloss.**
>   - `tailMin M := ⨅_{i} M i.succ` — the min of the tail widths `M₁,…,M_{L+2}` of `M : Fin (L+1+1+1) → ℕ`.
>   - `frontCharge M q := M 0 * q + minAdm (fun i => M i.succ − q)` — front-peel charge at tail-rank `q`:
>     the `M₀·q` cost of `A₀` killing a `q`-dim column space of the tail product, plus the codim of the
>     `{rank tail ≤ q}` locus (`minAdm` of the tail chain shifted down by `q`, truncated `ℕ`-subtraction).
>   - `minAdm_eq_frontPeel M : minAdm M = (Finset.range (tailMin M + 1)).inf' _ (frontCharge M)` — the min
>     over admissible tail-ranks `q ∈ {0,…,tailMin M}` of `frontCharge M q` equals `minAdm M`.
>   - `frontCharge_ge_minAdm M q (hq : q ≤ tailMin M) : minAdm M ≤ frontCharge M q` — every admissible
>     `q` charges at least `minAdm M` (the `≥`-at-every-`q` half; a term of the achieved min).
> - **Proved.** Both statements, unconditionally, for all `M : Fin (L+1+1+1) → ℕ` (i.e. `≥ 3` widths) and
>   all `L : ℕ`. Axiom-clean: `#print axioms` on `minAdm_eq_frontPeel`, `frontCharge_ge_minAdm`,
>   `twoVar_min_eq` = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Method: arity induction
>   over the EXISTING banked `minAdm` recursion (`sjChargeBudget_recursion` / `_le` / `_binding`,
>   `minAdm_cons_eq`, `minAdm_two_eq`) + the 2-variable identity `twoVar_min_eq`
>   (`min_t (M₀−t)(M₁−t)+t·r = min_q M₀·q+(M₁−q)(r−q)`, reflection `q = M₁−t` with clamped witnesses).
>   No permutation-invariance used. In-file fidelity anchors match the cert §C: `(3,3,3,4)` →
>   `tailMin=3`, `frontCharge` over `q=0..3` = `8,7,7,9`, `minAdm=7`; `(4,4,2)` → top component at the
>   SUB-generic rank `q=1` (`<tailMin=2`), `frontCharge 1 = 7 = minAdm`.
> - **Assumed.** None (no open hypotheses).
> - **Cited.** None — pure `ℕ` combinatorics, self-contained over the banked `minAdm` ecosystem.
> - **Deferred.** The `FrontPeelStep` analytic primitive of cert §C (the measure-theoretic
>   `A₀ ↦ A₀·U` shift `M₀·q/2` + tail-rank-locus recursion) is a SEPARATE, non-combinatorial obligation —
>   this card covers only the pure-`ℕ` closure identity, not the analysis that consumes it.
> - **Domain note (fidelity).** Stated at `Fin (L+1+1+1)` (`≥ 3` widths), not the cert's nominal
>   `Fin (L+1)`. The identity is FALSE at 2 widths (front-peel of `(M₀,M₁)` collapses to `0 ≠ M₀·M₁`,
>   since the tail must itself be a `≥ 2`-width product-chain); `Fin (L+1+1+1)` is the faithful domain,
>   matching the cert's geometry ("the tail `(M₁,…,M_L)` must be a genuine `≥ 2`-width product-chain").
> - **Structure & ideas observed.** (from cert `genm-r1substratum`, pen-and-paper) the sub-generic tail
>   strata CLOSE — the top component of `Σ⁰` frequently sits at a sub-generic tail rank (`(4,4,2)` at
>   `q=1`, not the generic `q=2`); mechanism is the exact compensation `M₀·q + minAdm(tail−q)`.
> - **Route.** (formaliser `genm-r1frontcharge`) The layer-peel and front-peel are DIFFERENT recursions
>   (no clean `Adm`/`Mval` bijection — verified numerically). Bridge: expand `minAdm` by the banked
>   layer-peel, apply the front-peel IH to both reduced chains, factor the shared deep `minAdm(W−r)` out of
>   the double-min, and both directions coincide by the 2-variable `twoVar_min_eq`. Full skeleton
>   (base `n=3` direct = `f=g`; step `n≥4`) exhaustively pre-verified in Python (0 fails).
> - **Status.** sorry-free
