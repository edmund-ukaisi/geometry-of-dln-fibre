# Statement card — `genm-corndblock`: the `Fin d`-block corner-blow-up finiteness

The **width-general (`Fin d`)** binding-corner endpoint for a depth-`d` flag — the `d`-block
generalization of the banked TWO-block corner-blow-up crux
(`genm-sjslice`, `sjSlice_corner_two_block_lt_top`). Module
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCornerBlock.lean`. All theorems clean-three
`[propext, Classical.choice, Quot.sound]`, 0 `sorry` (force-recompiled `#print axioms`).

---

> **Claim (width-general `d`-block corner).** For `d` radial blow-ups of block dimensions `hᵢ+1`
> (accumulated Jacobian powers `hᵢ`; each loss term radial order 2) sharing the deep factor, the
> binding corner local model `(∑ᵢ uᵢ²·Uᵢ)^{−c'}` with Jacobian `∏ᵢ |uᵢ|^{hᵢ}` and residual units `Uᵢ`
> bounded below by `a>0` on the unit box has finite `∫⁻` for every `c' < ½·∑ᵢ(hᵢ+1)` (the branch
> threshold where all `d` codimensions ADD).
>
> - **Lean:** `DLNFibre.DLN.RLCT.sjSlice_corner_block_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCornerBlock.lean` @ `ebe28e51`)
> - **Gloss.** `∀ d : ℕ, ∀ h : Fin d → ℕ, ∀ c' : ℝ≥0, (c':ℝ) < (∑ i, ((h i : ℝ)+1))/2 →
>   ∀ U : Fin d → (Fin d → ℝ) → ℝ, ∀ a : ℝ, 0 < a → (∀ i, ∀ u ∈ unitBox d, a ≤ U i u) →
>   ∫⁻ u in unitBox d, ENNReal.ofReal ((∑ i, u i ^ 2 * U i u) ^ (−(c':ℝ)) * (∏ i, |u i| ^ h i)) < ⊤`.
> - **Proved.** The `ℝ≥0∞` box integral is finite (`< ⊤`) below the threshold, unconditionally in
>   `(d, h)`. Proof: `d`-ary weighted AM-GM (`Real.geom_mean_le_arith_mean_weighted` on `Finset.univ`)
>   at the min-cut weights `wᵢ = (hᵢ+1)/∑ⱼ(hⱼ+1)` dominates the loss base below by `∏ᵢ |uᵢ|^{2wᵢ}`
>   (`∑ᵢ uᵢ² ≥ ∑ᵢ wᵢuᵢ² ≥ ∏ᵢ (uᵢ²)^{wᵢ}`, each `wᵢ ≤ 1` by `Finset.single_le_sum`), so after the units'
>   lower bound `a` the integrand is dominated by the *separated* monomial `∏ᵢ |uᵢ|^{hᵢ−2wᵢc'}`, which is
>   box-integrable iff every axis exponent `> −1` — and at these weights every constraint coincides at
>   `c' < ½·∑ⱼ(hⱼ+1)` (`2wᵢc' < hᵢ+1 ⟺ 2c' < ∑ⱼ(hⱼ+1)`). Lands on the banked
>   `RouteMSJMonomialLower.prod_rpow_lintegral_Ioo_box_lt_top` (`Fin d` open-box rpow-product) via the
>   banked `restrict_unitBox_eq_open` boundary bridge. `d = 0` is handled uniformly: `hc'` forces
>   `(c':ℝ) < 0`, contradicting `c'.coe_nonneg`, so `0 < ∑ᵢ(hᵢ+1)` throughout.
> - **Assumed.** Each unit `Uᵢ` is bounded below by `a>0` on the box (`∀ i, ∀ u ∈ unitBox d, a ≤ U i u`)
>   — the §8 shared-support closure carried as a hypothesis, exactly as the 2-block card and the banked
>   terminal endpoint carry their `hunit`. No measurability of `Uᵢ` is needed (domination is monotone).
> - **Cited.** None (S2-free: no `monomial_rlct`, no `cited_aoyagi_dln`). The `rlct = ½·codim` reading
>   stays Cited elsewhere; this proves box-finiteness at the branch threshold only.
> - **Deferred.** The change-of-variables that PRODUCES this `d`-block corner model from the
>   `gammaPeelIntegral` at a depth-`d` flag (the general-width CoV / resolution-map mountain) is NOT done
>   here — this closes the corner analytically, Jacobian-free, exactly as the 2-block crux does; the CoV
>   feeding it is deferred. Also deferred: discharging the §8 unit-boundedness `a ≤ Uᵢ` from the actual
>   resolved cores.
> - **Structure & ideas observed.** The generalization is faithful and clean: the 2-block min-cut
>   weighting `((h₀+1)/s, (h₁+1)/s)` extends verbatim to the `Fin d` simplex `wᵢ = (hᵢ+1)/∑ⱼ(hⱼ+1)`, the
>   direction where all `d` axis constraints coincide at `½·∑ⱼ(hⱼ+1) = ½·(sum of block dims)` — the
>   analytic encoding of "the `d` codimensions add on the terminal exceptional divisor". The threshold
>   `½·∑ᵢ(hᵢ+1)` is the `d`-block corner charge; the symmetric-weight (basic AM-GM) undershoot generalizes
>   to `minᵢ(hᵢ+1)` (not reached here — only the min-cut weighting is used).
> - **Route (formaliser).** Direct generalization of the banked 2-block proof: replace the explicit
>   `X^{2w₀}Y^{2w₁} ≤ X²+Y²` two-term AM-GM by the `Finset.univ` weighted AM-GM
>   (`Real.geom_mean_le_arith_mean_weighted`), the two-factor products/sums by `∏ i`/`∑ i`, and the
>   entrywise rpow exponent-bookkeeping by a `Finset.prod_congr` per-term (`Real.finset_prod_rpow`,
>   `Real.rpow_mul`, `Real.rpow_natCast`, `Real.rpow_add`). Same banked endpoints
>   (`prod_rpow_lintegral_Ioo_box_lt_top`, `restrict_unitBox_eq_open`).
> - **Status.** sorry-free (pending fidelity review).

> **Corollary (recovers the banked 2-block case).**
>
> - **Lean:** `DLNFibre.DLN.RLCT.sjSlice_corner_block_recovers_two_block` — instantiates the general
>   theorem at `d=2`, `h = ![h₀,h₁]`, `U = ![U₀,U₁]` and rewrites (`Fin.sum_univ_two`,
>   `Fin.prod_univ_two`) to reproduce the banked `sjSlice_corner_two_block_lt_top` statement verbatim
>   (explicit two-term sum `u₀²·U₀ + u₁²·U₁`, two-factor Jacobian `|u₀|^{h₀}·|u₁|^{h₁}`, threshold
>   `(h₀+h₁+2)/2`) (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCornerBlock.lean` @ `ebe28e51`).
> - **Proved.** `½·∑ᵢ(hᵢ+1)` at `d=2` is `(h₀+h₁+2)/2`; the general theorem subsumes the 2-block crux.
> - **Non-vacuity.** An `example` with trivial units `Uᵢ=1` (`a=1`) and any `(d,h)` exhibits the concrete
>   integral `∫⁻ (∑ᵢ uᵢ²)^{−c'}·∏ᵢ|uᵢ|^{hᵢ}`, finite below the threshold (hypotheses jointly satisfiable).
> - **Status.** sorry-free (pending fidelity review).

---

## Notes

- **Not wired into the aggregator by this thread.** `DLNFibre.lean` is single-writer; the controller
  wires `import DLNFibre.DLN.RLCT.Validate.RouteMSJCornerBlock` (and, if load-bearing, a
  `#print axioms sjSlice_corner_block_lt_top` line in `DLNFibre/DLN/RLCT/AxCheck.lean`). Full
  `lake build DLNFibre` was green-gated locally with the import temporarily appended (then reverted); no
  name clash (`sjSlice_corner_block_lt_top`, `sjSlice_corner_block_recovers_two_block` are new).
