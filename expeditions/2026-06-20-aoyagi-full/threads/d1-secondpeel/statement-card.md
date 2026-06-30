# Statement card — D1 second-peel `extraCount` chart producer (L = 2)

> **Claim.** The L = 2 D1 second peel — peeling the `extra = extraCount m a b` regular Morse squares
> out of the first-peel slice residual `R`, landing on the degraded core `M' = (m−a, m−a−b, m−b)` — is
> a BOUNDED selected-minor IFT chart (the structural analog of the first peel), not the `#120`
> gauge-slice wall. Concretely: for a `C²` residual vector `h` vanishing at the basepoint with an
> invertible `extra`-minor of its Jacobian, `rlctAtOn (∑ h i²) t0 = rlctAtOn (∑ s² + ‖q₂‖²) (0, t0₂)`
> for a global `C¹` residual `q₂`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.secondPeel_hchart_residual`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1SecondPeelChart.lean` @ `d9abb550`)
>   and `DLNFibre.DLN.RLCT.deepest_le_of_optimal_secondPeel_discharged`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1SecondPeelAssembly.lean` @ `d9abb550`)
> - **Gloss.** `secondPeel_hchart_residual`: given `h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)`
>   `C²` with `h t0 = 0`, injective component/coordinate selections `eh, ec : Fin extra → …`, and the
>   `extra × extra` Jacobian minor `of (k,k' ↦ (D(h·(eh k))(t0)) (single (ec k') 1))` invertible,
>   there exist a global `C¹` `q₂` and a basepoint `t0₂` with the local RLCT of `∑ h i²` at `t0`
>   equal to that of the post-chart `∑ p.1² + ∑ q₂ p²` at `(0, t0₂)`. The assembly theorem wires this
>   into the two-peel D1 producer to conclude `rlctAt deepest ≤ rlctAt v` at a middle-stratum `v`.
> - **Proved.** Both theorems sorry-free, axioms `[propext, Classical.choice, Quot.sound]`. The
>   second-peel chart is built (not hypothesized) from the residual-vector selected-minor data via the
>   network-free chart spine (IFT chart `abChartΦ`, right-inverse, germ split `abGermA`,
>   bump-globalised `C¹` residual, MP split homeomorph `abSplitHomeo`) — mirroring `dln_hchart_residual`.
> - **Assumed (named-open, EXPLICIT hypotheses, not axioms).** (i) the first-peel chart transfer
>   `hchart` (DLN bounded-unit IFT at `v`); (ii) `hDeepest` = #44; (iii) `hInterface` = the R1-
>   resolution value at `M'` + the second-peel slice non-vanishing `hR₂ne`; (iv) `hminor₂`, the
>   second-peel selected-minor non-degeneracy (a JACOBIAN-rank condition on the residual VECTOR).
> - **Cited.** none (network-free real analysis; reuses banked engine `rlct_quasiSplit_ge` and the
>   chart primitives, all in-repo).
> - **Deferred.** none for the chart itself. The `≥`-leg as a whole still SEQUENCES on R1 (`hInterface`),
>   #44 (`hDeepest`), and the first-peel `hchart` — those are tracked obligations, not this tide's.
> - **Structure & ideas observed (verify-first gate).** `∇R(t0) = 0` (scalar) but `Hess R(t0) =
>   2 (dh(t0))ᵀ dh(t0)` — the `extra` Morse directions of `R` are first-order rank in the residual
>   VECTOR `h`. Selecting the minor from `h` (not the scalar `R`) is what keeps the second peel at the
>   bounded IFT altitude, off the gauge-slice wall. Decorrelated Codex xhigh confirmed the verdict.
> - **Status.** sorry-free (awaiting reviewer fidelity check).
