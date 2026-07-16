# Statement card — corank-one edge scalar engine (D)

## Card 1 — the scaled radial engine (LANDED, sorry-free)

> **Claim.** The scalar radial factors of satred's corank-one edge peel: the 1-D and `a`-dimensional
> radials `∫(w+‖·‖²)^{−p}` obey the pivot-energy scaling `= w^{d/2−p}·(base radial)` (`d=1` resp. `d=a`)
> and are finite (`w>0`, and `p>1/2` resp. `(a:ℝ)<2p`).
>
> - **Lean:**
>   - `DLNFibre.DLN.RLCT.scaledRadial1D_eq` — `∫⁻ t:ℝ, ofReal((w+t²)^{−p}) = ofReal(w^{1/2−p}) · ∫⁻ s, ofReal((1+s²)^{−p})` (`hw : 0 < w`)
>   - `DLNFibre.DLN.RLCT.scaledRadial1D_lt_top` — the above `< ⊤` (`hw : 0<w`, `hp : 1/2 < p`)
>   - `DLNFibre.DLN.RLCT.japaneseBracket_euclid_lt_top` — `∫⁻ x:EuclideanSpace ℝ (Fin a), ofReal((1+‖x‖²)^{−p}) < ⊤` (`ha : (a:ℝ) < 2*p`)
>   - `DLNFibre.DLN.RLCT.scaledRadialEuclid_eq` — `∫⁻ x:EuclideanSpace ℝ (Fin a), ofReal((w+‖x‖²)^{−p}) = ofReal(w^{a/2−p}) · ∫⁻ s, ofReal((1+‖s‖²)^{−p})` (`hw : 0<w`)
>   - `DLNFibre.DLN.RLCT.scaledRadialEuclid_lt_top` — the above `< ⊤` (`hw : 0<w`, `ha : (a:ℝ) < 2*p`)
>   - File: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJEdgeScalar.lean` @ `<pending-SHA>`
> - **Gloss.** After polar coordinates, the corank-one edge leaf reduces to these radials; the `w^{d/2−p}`
>   factor is the pivot-energy (`w = frobSq(P·Q̃ₚ)`) dependence carried into the arity−1 comparator. The `eq`
>   forms give the exact `w`-power (via `Real.map_volume_mul_left` / `map_addHaar_smul`); the `lt_top` forms
>   the finiteness (via dbuild's `radial1D_lintegral_lt_top` / Mathlib `integrable_rpow_neg_one_add_norm_sq`).
> - **Proved.** All five, unconditionally on their stated hypotheses (`w>0`, and `p>1/2` / `a<2p`).
> - **Assumed.** none beyond the stated hypotheses.
> - **Cited.** Mathlib only (`integrable_rpow_neg_one_add_norm_sq`, `map_addHaar_smul`,
>   `Real.map_volume_mul_left`); dbuild's `RouteMSJEdgeAtoms.radial1D_lintegral_lt_top`.
> - **Deferred.** these are the RADIAL FACTORS (satred steps 3–4/P3); the full `edge_coupledBox_lt_top`
>   (the coupling `u=rs`→log, the C-shift CoV, the b≥2 minor chart, the δ-fold assembly, the w-integral=IH)
>   is NOT here — see `thread.md` § "the remaining mountain".
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` (all five, force-recompiled
>   `#print axioms`).

## Card 2 — the `edge_coupledBox_lt_top` interface (VALIDATED signature; body `sorry`, NOT landed)

> **Claim (target, arch1build-pinned).** The generic tight-edge cell integrates `coupledBox` to a finite
> value.
>
> - **Lean signature (validated to compile; body `sorry`):**
>   `DLNFibre.DLN.RLCT.edge_coupledBox_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJEdgeAssembly.lean`, uncommitted scratch)
>   ```
>   theorem edge_coupledBox_lt_top (M : Fin (L+1+1+1) → ℕ) (t j : ℕ) (c' : ℝ)
>       (hnd : ∀ i, 1 ≤ M i) (hj : j < min (M 0 - t) (M 1 - t))
>       (i : CRIndex (dropHead (redChain (t+j) M)))
>       (hedge : cellRankIndex (dropHead (redChain (t+j) M)) i = deepTailMin M
>           ∧ deepTailMin M < (M 0 - (t+j)) + (M 1 - (t+j)))
>       (hc' : ((M 0 - (t+j) : ℕ):ℝ) * ((M 1 - (t+j) : ℕ):ℝ) / 2 < c')
>       (hcT : c' < (minAdm M : ℝ) / 2)
>       (hIH : ∀ M' : Fin (L+1+1) → ℕ, RouteMBoxThresholdFinite M') :
>       ∫⁻ p in (paramsBoxM (redChain (t+j) M) 1 ×ˢ matBox (M 1 - (t+j)) (M 2) 1)
>           ∩ projDeep M (t+j) ⁻¹' (deepCell (dropHead (redChain (t+j) M)) (dropHead (redChain (t+j) M) 0) L
>               le_rfl (dropHead (redChain (t+j) M) (Fin.last L)) i (fun _ => (1 : Matrix …))),
>         coupledBoxIntegrand M (t+j) c' p < ⊤
>   ```
> - **Gloss.** For the co-null generic edge cell (deep-factor rank `= deepTailMin`, corank regime
>   `deepTailMin < a+b`, so `a+b = deepTailMin+1` exactly), the coupled-box integral over the cell is
>   finite in the top window `(M₀−u)(M₁−u)/2 < c' < ½·minAdm M`, given the arity−1 IH.
> - **Proved.** nothing yet (body `sorry`); the SIGNATURE compiles and exact-fits arch1build's `hcell(edge i)`.
> - **Deferred.** the whole proof — see `thread.md` § "the remaining mountain" for the step decomposition
>   (R1–W2) and which pieces are banked / landed / HARD.
> - **Status.** interface validated (compiles); proof NOT started. Do NOT commit until sorry-free.
