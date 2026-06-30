# Statement cards — genm-d1asm (D1 ≥-leg L=2 de-risk)

Branch `expedition/genm-d1asm` (off canonical `aca74685`). All builds via `scripts/lb` on the shared
mathlib store; axioms forced with `#print axioms` (force-rebuilt scratch).

---

## Card 1 — the second-peel minor `hminor₂` from a rank bound

> **Claim.** For a `C¹` residual vector `h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)`, if the residual
> Jacobian `jacResid h t0` (the `(i,c)` matrix of component partials `∂_c (h·i)(t0)`) has rank
> `≥ extra`, then there are injective `eh : Fin extra → Fin n`, `ec : Fin extra → Fin N` selecting an
> invertible `extra × extra` Jacobian minor — i.e. the second-peel non-degeneracy `hminor₂`
> `secondPeel_hchart_residual` consumes.
>
> - **Lean:** `DLNFibre.DLN.RLCT.exists_secondPeel_minor`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1SecondPeelMinor.lean` @ `c9685540`)
> - **Gloss.** `extra ≤ (jacResid h t0).rank → ∃ eh ec, eh inj ∧ ec inj ∧ det of the (eh,ec) Jacobian
>   minor ≠ 0`, with the minor in the exact `Matrix.of (fun k k' => fderiv (h·(eh k)) t0 (single (ec k')
>   1))` encoding. Plus the supporting `jacResid` def and the bridge `jacResid_submatrix_eq`
>   ((jacResid h t0).submatrix eh ec = that `Matrix.of`).
> - **Proved.** The rank-bound ⟹ minor existence brick, network-free, generic over any `C¹` residual
>   vector. Reuses the banked determinantal engine `exists_minor_of_le_rank`
>   (← `exists_submatrix_det_ne_zero_of_le_rank`, `Core.RankLocusClosed`). The EXACT structural analog
>   of the first peel's `exists_jacFlatL2_minor`.
> - **Assumed.** `hrank : extra ≤ (jacResid h t0).rank` — the rank lower bound (a hypothesis here).
> - **Cited.** none.
> - **Deferred.** The rank bound itself, when `h` is the bump-globalised first-peel slice residual
>   `q(0,·)` and `extra = extraCount m a b`. STEP-0 verdict (BOUNDED): it follows by the same
>   gauge-fixed linear injection as the first peel (middle-stratum layer ranks `(r+a, r+b)` vs deepest
>   `(r, r)`; dimension count `(r+a)H0+(r+b)H2−(r+a)(r+b) − nReg = extraCount`, sympy-exact), via a
>   Schur/quotient step `rank(D h(t0)) = rank(Dg(v)) − nReg`. Tying it to the bump-globalised `q(0,·)`
>   needs the IFT-chart / split-homeomorph / bump unwind — NOT done here.
> - **Status.** sorry-free; axioms `[propext, Classical.choice, Quot.sound]`.

---

## Card 2 — the L=2 D1 `≥`-leg Skeleton reduction (the glue)

> **Claim.** At a middle-stratum optimal `v` (square deepest reduced widths `(m,m,m)`, `a+b ≤ m`), the
> local RLCT at the constructed deepest point is `≤` that at `v`:
> `rlctAt (deepestPoint H r B hB hr hL) ≤ rlctAt v` — reducing the L=2 specialisation of the bare
> Skeleton `sorry` `rlctAt_deepest_le_of_optimal` to the assembled Route A producer, with `hminor₂`
> DISCHARGED from a rank bound and exactly TWO named-open gated hypotheses remaining.
>
> - **Lean:** `DLNFibre.DLN.RLCT.rlctAt_deepest_le_of_optimal_L2`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1SecondPeelGlueL2.lean` @ `c9685540`)
> - **Gloss.** Threads the first-peel `C¹` residual `q` + chart transfer `hchart` + slice nonvanishing,
>   the second-peel slice `C²`-ness + vanishing + the rank bound `hrank₂` (from which it BUILDS
>   `hminor₂` + selectors via `exists_secondPeel_minor`), and the two gates `hDeepest`/`hInterface`,
>   into `deepest_le_of_optimal_secondPeel_discharged` (instantiated at `deepest := deepestPoint …`).
> - **Proved.** The reduction: GIVEN the per-`v` first-peel chart data, the second-peel slice data +
>   rank bound, `hDeepest`, and `hInterface`, the Skeleton per-point `≥`-leg conclusion holds at L=2.
>   `hminor₂` is no longer a hypothesis — discharged inside from `hrank₂`.
> - **Assumed (per-`v` analytic data, producible / bounded).** the first-peel residual `q`/`hq`/`t0`/
>   `hchart`/`hRne` (the `dln_hchart_residual` output at `v`, banked sorry-free + `exists_jacFlatL2_minor`);
>   the second-peel `hslice`/`hslice0`/`hrank₂`.
> - **Cited.** none (the producers it chains are all sorry-free at canonical).
> - **Deferred — the TWO named-open gates (each with its tracked producer):**
>   - `hDeepest` = #44 `deepest_regular_core_normal_form` at the L=2 `deepestPoint`, Route-A
>     `nReg/2 + coreDeepest` form — ← open #149/#153 `deepest_diffeo_bridge_L2` wiring.
>   - `hInterface` = `R1ResolutionInterface` at the degraded core `M'` — ← R1-LOWER `cover_ge_div`.
> - **Status.** sorry-free; axioms `[propext, Classical.choice, Quot.sound]` (no `monomial_rlct`,
>   no `sorryAx`). Does NOT edit `Skeleton.lean` — the controller wires `rlctAt_deepest_le_of_optimal_L2`
>   into the Skeleton `sorry` at integration.

---

## Scope note (precision)

These two cards do NOT close the D1 `≥`-leg. They turn the bare Skeleton `sorry` into a legible
reduction whose remaining debt is exactly the two named gates above + the per-`v` first-peel chart
(producible) + the second-peel rank bound (BOUNDED, STEP-0). The day R1-LOWER lands `hInterface` and
#44-at-L2 lands `hDeepest`, the only residual D1 piece is the second-peel rank bound's chart-unwind
(named in Card 1's Deferred) — D1≥ is then a pure assembly, R1-independent (modulo the two gates), as
the STEP-0 verdict established.
