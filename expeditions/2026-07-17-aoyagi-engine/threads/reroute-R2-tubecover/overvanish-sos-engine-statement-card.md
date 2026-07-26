# Statement card — (ii) over-vanishing value engine: the monomial × sum-of-squares product RLCT

Seat (ii), the over-vanishing-144 value side. The clean-144 single-survivor `hentry` path is DEAD on
these leaves (0 single-entry survivors); the honest lower bound rides a NEW product-RLCT engine
(elder-confirmed ADOPT-WITH-AMENDMENTS; controller-authorized after the chain-wire was 3-way verified
dead). This card banks the **Core value engine** (network-free), a SPECIFY skeleton whose easy facts
are proved sorry-free and whose one analytic crux is a statement-locked tracked hole.

Branch `expedition/aoyagi-r2overvanish-regseq` off `2583a6bd1`.
Module `lean/DLNFibre/Core/Aoyagi/MonomialSumSqRLCT.lean`.

---

> **Why the chain-wire is dead here (the finding that reshaped the seat).** The V-lower wire
> `rlctAt_ge_iInf_threshold_of_sandwich_cover` reads its per-chart value off the chain-minimal
> monomial: its engine `monomialSumSq_integrableAtFilter_of_lt` collapses `∑ bₖ² = b_{k₀}²·U` with
> `U ≥ 1` a UNIT bounded ABOVE (`U^{-c} ≤ M`), discarding the sum's vanishing. For the over-vanishing
> family `{vm·z_j}` no member divides another (not a chain); the only chain repair (`k₀ = vm`) gives
> `monomialThreshold(vm) = 1/2` (`jac`-0 on `vm`'s binding axes). The `r/2 = 4` improvement — from the
> 8 `jac`-0 coords forming a nondegenerate sum-of-squares — is structurally invisible to that engine.
> Verified in Lean by reading the engine; 3-way confirmed (me / controller / pnp exact algebra).

> **Claim (the product germ + its measure-theoretic facts — PROVED sorry-free, clean-three).**
> `monoSumSqGerm a Z u = (∏_d u_d^{a_d})² · ∑_{j∈Z} u_j²` is nonnegative, measurable, and (given `Z`
> nonempty) has a locally-null zero set (`LocallyNullZeros`, the guard the domination leg needs).
>
> - **Lean:** `DLNFibre.Core.Aoyagi.monoSumSqGerm` / `monoSumSqGerm_nonneg` /
>   `measurable_monoSumSqGerm` / `locallyNullZeros_monoSumSqGerm` / `monoSumSqThreshold`
>   (`…/Core/Aoyagi/MonomialSumSqRLCT.lean`).
> - **Gloss.** The over-vanishing loss lower bound (`vm² · ∑_Z z²`); the null-zero fact bounds the zero
>   set inside `⋃_d {u_d = 0}` (either `vm = 0` forces a binding `u_d = 0`, or `∑_Z z² = 0` forces
>   `u_{j₀} = 0` for `j₀ ∈ Z`), a finite union of null coordinate hyperplanes.
> - **Axioms.** `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all three.
> - **Status.** sorry-free.

> **Claim (the weighted product-RLCT integrability engine — STATEMENT-LOCKED, one tracked hole).**
> `monoSumSq_integrableAtFilter_of_lt`: for a weight `W =ᶠ jacWeight jac · unit` near `p`
> (`unit` continuous nonvanishing measurable) and `cc` below BOTH `monomialThreshold a jac` AND
> `|Z|/2` (`2·cc < |Z|`), with `Z` disjoint from `supp(vm)` and `jac`-0 on `Z` (`hZa`, `hZjac`), the
> weighted product germ `W · (monoSumSqGerm a Z)^{-cc}` is integrable on a neighbourhood of `p`.
>
> - **Lean:** `DLNFibre.Core.Aoyagi.monoSumSq_integrableAtFilter_of_lt`.
> - **Gloss.** The ≥-direction (convergence) the V-lower wire consumes; per-chart, at an arbitrary
>   base point (needed for the blow-up cover). The value read-off is `min(threshold(vm²), |Z|/2)` (all
>   16 over-vanishing types: `threshold(vm²) ∈ {4, 9/2}`, `|Z|/2 = 8/2 = 4` ⟹ min = 4).
> - **Proof mechanism (locked, the hole).** Bound `unit` by its `sup` near `p` (elder amendment A: the
>   unit COUPLES the blocks, does NOT factor); the unit-free box integral then factors over the
>   coordinate partition `Z ⊔ Zᶜ` (Tonelli via `MeasurableEquiv.piEquivPiSubtypeProd`,
>   `measurePreserving_piEquivPiSubtypeProd`): the `Z`-block sum-of-squares integral is finite for
>   `2·cc < |Z|` (`RLCT.SumSq`: `integrableOn_ball_norm_rpow_iff` transported to the `Z`-subtype), the
>   complement pure-power monomial box integral is finite below the threshold
>   (`MonomialBox.prodRpow_boxSymm_lt_top`). `-- map: ov-sos-tonelli`.
> - **Status.** tracked-open (`sorry`); the ONE analytic crux. Statement-locked.

> **Direction warning banked in the module.** The toric-LP over the term-ideal `M ⊇ I` is an UPPER
> bound on the true RLCT (SoS-RLCT is monotone INCREASING under ideal inclusion), NOT a lower bound —
> equality iff `I` is already monomial (the clean leaves). The honest over-vanishing lower bound is
> this SoS/regular-sequence engine.

---

**Remaining build ladder (handed back — multi-tide unit).**
1. **[Core] `ov-sos-tonelli`** — the disjoint-block Tonelli finiteness (est. ~150–250 lines): the
   `Z`-block SumSq transport to a coord subtype + the `Zᶜ` MonomialBox (may need un-`private`-ing
   `MonomialBox.prodRpow_boxSymm_lt_top`) + the unit-sup reduction + the arbitrary-`p` box (mirror
   `monomialSumSq_integrableAtFilter_of_lt` lines 777–888). Closes the Core engine sorry-free.
2. **[Core, optional bedrock]** the two-sided `rlctAt … = min` equality (elder (B), `_eq` form): the
   `≤` half via the unit `inf > 0` marginalization. Not needed for the payoff (`≥` suffices).
3. **[DLN] the over-vanishing pullback identity** `∑_i (coreGen … i (gFlat idx w))² = vm²·∑_{k} vf_k²`
   via `mult_eWrap (v := gFlat idx w)` + `lossDLN_zero_eq_coreLoss`, then entry-wise factoring — per
   type (16), the analog of the clean-144 `hentry`.
4. **[DLN] the regular-sequence `Ψ` per type** (a `blockShear`, det-1, keep-set ⊇ `supp(vm)`,
   `pnp/ii_builddata.out`): `vf_k|_{reg-seq} ∘ Ψ = z_j` (coords) + `subset_le_sum` (drop 4, keep 8).
5. **[DLN] the cover transport** (route (b), elder (C): fold `Ψ` into `g' = g ∘ Ψ`): generic atom
   `g '' ball 0 r ⊆ (g ∘ blockShear φ) '' ball 0 (r + C·r²)` via `blockShear_covers_scaled` +
   `Set.image_mono` + `Set.image_comp`.
6. **[DLN/Core] the assembly** — a V-lower wire variant whose per-chart integrability is the Core
   engine (share the area-formula/cover spine of `mem_localAdmissible_of_sandwich_lt`), giving
   `4 ≤ rlctAt (∑ coreGen²) 0` over the mixed 288-chart family with B's clean-144.

**pnp build data:** `expeditions/.../reroute-R2-tubecover/pnp/ii_builddata.out` (16 types: `vm`, the 8
`vf→z` map, `Ψ` shear per `z`, disjoint+`jac`-0 = True, `threshold(vm²) ∈ {4, 9/2}`, value = 4);
`ii_perdominant.out` (σ_{p1} EXACT 144/144 → canonical-16 + one relabel).

---

## DLN backbone + STEP-6 skeleton LANDED (`Corank2OverVanish334.lean` / `Corank2OverVanishAssembly334.lean`)

The generic, network-facing scaffolding for pieces (3)–(6), built against the LOCKED Core engine
(commits `96f735f44` → `fec1909e4`). Merged the rework seat's `Corank2NativeEntry334`
(`A0_gFlat_factor` / `A1_gFlat_spectator` / `gInner`).

> **`DLN.Aoyagi.OverVanish334` (backbone).** CLEAN-THREE:
> - `image_comp_blockShear_superset` (5) — fold `Ψ = blockShear φ` into a chart ⟹ the `0`-ball cover
>   survives (`g '' cB 0 r ⊆ (g∘Ψ) '' cB 0 (r+C·r²)`), via `blockShear_covers_scaled`.
> - `monoSumSqGerm_le_sumSqFam_comp` (4, full-`hpull` form) and `monoSumSqGerm_le_of_regSeq_entries`
>   (4, LEAN entry form — reduces the per-type obligation to the 8 reg-seq entry identities
>   `coreGen k (gFlat idx (Ψ u)) = vm·u_{zc k}`, no full 12-entry pullback).
> - `jacWeight_fixOn` — `Ψ` fixing `supp(h)` ⟹ `jacWeight h` invariant (the folded weight).
> - `coreGen_gFlat_factor` (toward 3) — the uniform `u_{p1}` factor of every entry
>   (`= u_{p1}·resid_k`, via `A0_gFlat_factor` + `Matrix.mul_smul`).
>
> TRACKED-OPEN (Core sorry propagates, by design):
> - `chart_integrableAtFilter_of_monoSumSq_dom` — the per-chart integrability the wire consumes,
>   routed through the LOCKED `monoSumSq_integrableAtFilter_of_lt` + junk-guarded domination
>   (`wLocalAdmissibleExponents_subset_of_eventually_le` + `locallyNullZeros_monoSumSqGerm`). The
>   over-vanishing analogue of `integrableAtFilter_of_sandwich`.

> **`DLN.Aoyagi.OverVanishAssembly334` (STEP-6, P6 skeleton).**
> `rlctAt_coreGen334_ge_four_of_perchart_integrable` — the mechanism-heterogeneous headline
> `4 ≤ rlctAt (sumSqFam (coreGen dvec eWrap)) 0`, abstracting the per-chart per-point
> integrability-below-4 as ONE hyp `hint` (discharged: clean-144 via `hentry`→chain `≥9/2`;
> over-vanishing-144 via the bridge `=4`; both over the full-288 cover). Body `-- map: step6-assembly`
> (a refactor of `mem_localAdmissible_of_sandwich_lt`'s spine with `hint` in place of the sandwich;
> `hbdd` = `bddAbove_localAdmissible_coreGen334`). NEEDS AGGREGATOR WIRING.

**Seat split (controller):** the per-type grind (the pullback + concrete `Ψ` + the 8 reg-seq entry
identities per canonical type + σ_{p1}) is a SEATED follow-on; the Core Tonelli is a SEATED follow-on;
this seat owns the backbone + the step-6 assembly (fill on convergence).
