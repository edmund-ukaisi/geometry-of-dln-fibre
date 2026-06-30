# Statement card — the assembled LIVE-leaf interior box-divergence atom

> **Claim.** For the interior-drop class at `L = 2`, the deepest-front loss integral
> `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'}` DIVERGES (`= ⊤`) for every `c' ≥ ½·minAdm M` and every
> `ε > 0` — the `hInterior` atom feeding the dispatch spine → `cover_ge_div` → the L=2 R1-LOWER headline.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_box_diverges_interiorLive`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveAtom.lean` @ `fa3f6c8b`)
> - **Gloss.** Given `M : Fin 3 → ℕ`, achiever admissibility `ha`, deepest-width positivity `h0r`/`h0c`,
>   `hpos : 1 ≤ minAdm M`, the interior class `hInt : InteriorDrop M`, a corank-or-deeper exponent
>   `hc' : (minAdm M)/2 ≤ c'`, and `hε : 0 < ε`: the lintegral of `|routeMCore M x|^{−c'}` over the
>   ε-cube is `⊤`. Assembled M-agnostically from the `NodeAchieverChart` bundle `interiorLiveNodeChart`
>   via `routeMCore_box_diverges_of_nodeChart`.
> - **Proved.** The full box-divergence, modulo the SINGLE open leaf `interiorLive_BdetMonomial` (the
>   abs-det monomial). The bundle's fields are all closed: rate (`routeMCore_interiorLivePhi`),
>   differentiability (`interiorLive_diff`), injectivity (`interiorLive_injOn` — both injOn halves
>   sorry-free, reviewed), leaf-H bookkeeping, cov (`interiorLive_cov`, modulo abs-det), and the three
>   LEAF-1 analytic facts: `ldu_image` / `ldu_Umeas` / `ldu_Ubound` (genm-ubound) + the positivity
>   `interiorLiveUnit_ae_pos` (genm-upolylive).
> - **Assumed.** `StructAdm`, deepest-width positivity, `1 ≤ minAdm M`, `InteriorDrop M`, the exponent
>   bound `c' ≥ ½·minAdm M`. All carried explicitly.
> - **Cited.** `monomial_rlct` (the S2 RLCT axiom) — pre-existing in the M-agnostic engine
>   `routeMCore_box_diverges_of_nodeChart` (NodeAchieverChart.lean); NOT introduced by this assembly
>   (verified: the engine carries it independently of the bundle).
> - **Deferred.** `interiorLive_BdetMonomial` (the abs-det monomial `|det D(BchartLeaf∘kLDU)| =
>   ∏ if j=pivot then 1 else |u j|^{leafH j}`) ← genm-ambdet, folding the DONE free-point eihd
>   (`Dtot_abs_det_free`, RouteMEihdFreePoint) + ambient det + genm-castdet's `eihd_hreg`. When it lands
>   (RouteMEihdFreePoint is UPSTREAM of the contract — fillable in-contract, no cycle), the whole
>   interior leg goes sorry-free.
> - **Route.** Architecture (forced by the import DAG): the LEAF-1 analytic facts reference the
>   contract's `interiorLivePhi`/`interiorLiveUnit`, so they sit DOWNSTREAM of the contract — they cannot
>   be wired in-contract (cycle). The cov + bundle + atom were therefore moved from the contract into the
>   new `RouteMInteriorLiveAtom` (imports contract + `RouteMInteriorLiveAnalytic` + `RouteMUPolyLive`),
>   keeping the atom NAME unchanged (no consumer yet; the spine imports the new module when wired). The 3
>   dead contract ubound stubs were deleted. Note: `ae_restrict_of_ae` is applied INSIDE `ldu_Ubound`,
>   not at the call site (the `hpos` arg is the plain `∀ᵐ u, 0 < unit`).
> - **Status.** the three ubound leaves + injectivity + rate + cov are sorry-free + reviewed; the atom
>   carries exactly one open leaf (`interiorLive_BdetMonomial`) + the permitted `monomial_rlct`. Contract
>   sorry count 4 → 1.

## Module split (post-Route-A)

  * `RouteMInteriorLiveContract` — chart `interiorLivePhi`, unit, rate, det `interiorLive_abs_det`
    (gated on `interiorLive_BdetMonomial`), injectivity `interiorLive_injOn` (sorry-free). 1 sorry.
  * `RouteMInteriorLiveAnalytic` (genm-ubound) — `ldu_image`/`ldu_Umeas`/`ldu_Ubound` (downstream).
  * `RouteMUPolyLive` (genm-upolylive) — `interiorLiveUnit_ae_pos` (downstream).
  * `RouteMInteriorLiveAtom` (this thread) — cov + bundle + atom, joining all of the above.
