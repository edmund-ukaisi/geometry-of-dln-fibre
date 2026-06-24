# Route-M cover facts — statement card (abstract reductions + the (2,2,2) discharge)

The two `IsRouteMCover` integral facts (`cover_le` / `cover_ge_div`), delivered as (i) ABSTRACT reductions
over arbitrary `(F, U, ι, d, k, h)` and (ii) the CONCRETE `(2,2,2)` discharge over `F = myF222`. These are
the standalone facts crux2 packages into `IsRouteMCover` on `route-m-atlas` (the structure is defined
there, not on `fm3/routem`). Key finding (Codex g206, verified vs `RouteMBridge`): the bridge consumes
`cover_le` ONLY for the `≥`-leg finiteness transfer, so `cover_le` reduces to FINITENESS + SCALING — no
explicit per-node change-of-variables.

Seat: `fm3-routem` (formalisation, R1 general-M cover grind). Tasks #87/#89. Modules:
`lean/DLNFibre/DLN/RLCT/Validate/RouteMCoverLemmas.lean` (@`3a0da38`, abstract),
`lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMCover.lean` (@`8bc5819`, concrete (2,2,2)).
Verification: reviewer fidelity check (PASS, all 5 questions; one docstring fence tightened @`8bc5819`).

---

> **Claim (abstract `cover_le` reduction).** From below-threshold finiteness + a nonzero leaf-sum RHS,
> the `IsRouteMCover.cover_le` field shape holds.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeM_coverLe_of_finiteness`
>   (`RouteMCoverLemmas.lean` @ `3a0da38`).
> - **Gloss.** For abstract `F : (Fin N → ℝ) → ℝ`, `U`, `[Fintype ι]`, `d k h`: if (a) `hpos : ∀ c',
>   (∑ᵢ ∫⁻_{unitBox(d i)} ofReal(monomialIntegrand (d i)(k i)(h i) c')) ≠ 0` and (b) `hfin : ∀ c', that
>   sum < ⊤ → ∫⁻_U ofReal(|F|^{−c'}) < ⊤`, then `∀ c', ∃ C < ⊤, ∫⁻_U ofReal(|F|^{−c'}) ≤ C·(that sum)`.
> - **Proved.** Unconditionally. Sum `= ⊤` ⟹ `C = 1` (`A ≤ ⊤`); sum `< ⊤` ⟹ `A < ⊤` by (b) ⟹
>   `coverLe_scaling` (`A<⊤ ∧ B≠0 ⟹ ∃C<⊤, A≤C·B`, `C = A/B`). Axioms: clean-three.
> - **Status.** sorry-free; reviewed (PASS).

> **Claim (abstract `cover_ge_div` reduction).** From an `ε`-uniform box divergence, the
> `IsRouteMCover.cover_ge_div` field shape holds.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeM_coverGeDiv_of_boxDiverges` (`RouteMCoverLemmas.lean` @ `3a0da38`).
> - **Gloss.** If `hdiv : ∀ c', (∃ i, monomialThreshold (d i)(k i)(h i) ≤ c') → ∀ ε>0,
>   ∫⁻_{cubeBox N ε} ofReal(|F|^{−c'}) = ⊤`, then `∀ c', (∃ i, monomialThreshold ≤ c') → ∀ Ω open ∋0,
>   ¬ IntegrableOn (fun x => |F x|^{−c'}·1) Ω`.
> - **Proved.** The inner argument is the body of `rlctAtOn_le_of_box_diverges` (`cubeBox_subset_of_isOpen`
>   + `lintegral_mono_set`), repackaged to the `¬ IntegrableOn` field form. Axioms: clean-three.
> - **Status.** sorry-free; reviewed (PASS).

---

> **Claim ((2,2,2) `cover_le`).** Over `F = myF222`, `U = openBox = (−1,1)^8`, the single binding-leaf
> family `(ι, d, k, h) = (Fin 1, 8, unitK8, unitH8)` (threshold `3/2`): the `cover_le` field holds.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeM222_cover_le` (`Case222RouteMCover.lean` @ `8bc5819`).
> - **Gloss.** `∀ c', ∃ C<⊤, ∫⁻_{openBox} ofReal(|myF222|^{−c'}) ≤ C·∑_{i:Fin 1} ∫⁻_{unitBox(routeM222D i)}
>   ofReal(monomialIntegrand (routeM222D i)(routeM222K i)(routeM222H i) c')`. Via the abstract reduction +
>   `routeM222_rhs_ne_zero` (single-leaf RHS `> 0` on the interior `(½,1)^8`) + `routeM222_below_threshold_fin`
>   (RHS `< ⊤` ⟹ `c' < 3/2` via `monomialIntegrand_lintegral_box_eq_top` contrapositive ⟹
>   `myF222_threshold_lt_top'`).
> - **Cited.** `monomial_rlct` (S2; via the banked `monomialThreshold`/integrability atoms). Axioms:
>   `[propext, Classical.choice, Quot.sound, monomial_rlct]`.
> - **Status.** sorry-free; reviewed (PASS, field-for-field match to `IsRouteMCover.cover_le`).

> **Claim ((2,2,2) `cover_ge_div`).** Over the same data: the `cover_ge_div` field holds.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeM222_cover_ge_div` (`Case222RouteMCover.lean` @ `8bc5819`).
> - **Gloss.** `∀ c', (∃ i:Fin 1, monomialThreshold … ≤ c') → ∀ Ω open ∋0, ¬IntegrableOn
>   (fun x => |myF222 x|^{−c'}·1) Ω`. Via the abstract reduction + `routeM222_box_diverges` (the
>   `rlctAtOn_myF222_le` `≤`-leg box-divergence, hoisted to the NON-strict endpoint `c' ≥ 3/2` the
>   `cover_ge_div` premise needs — the original was `c' > 3/2`; the only strictness carried `0 < c'`,
>   which survives at `c' = 3/2`. Reviewer-verified faithful).
> - **Cited.** `monomial_rlct` (via `leaf_box_div` / `monomialIntegrand_lintegral_box_eq_top`). Axioms:
>   `[propext, Classical.choice, Quot.sound, monomial_rlct]`.
> - **Status.** sorry-free; reviewed (PASS).

> **Supporting.** `routeM222_iInf_threshold : ⨅_{i:Fin 1} monomialThreshold (routeM222D i)… = 3/2`
> (`= lambdaCore (2,2,2)`); `routeM222_Fmeas/Uopen/Umem` (trivial). So
> `⟨routeM222_Fmeas, _Uopen, _Umem, _cover_le, _cover_ge_div⟩ : IsRouteMCover myF222 openBox (Fin 1)
> routeM222D routeM222K routeM222H` (crux2 packages), and `routeM_rlctAtOn_eq_iInf` ⟹
> `rlctAtOn myF222 0 = 3/2`.

---

## Scoping fences (caveats next to the claims)

- **`F = myF222`, the FLAT (2,2,2) core — NOT `dlnLoss H222 0`.** The seam is NOT bare equality:
  `dlnLoss222_eq_myF222` is `dlnLoss H222 0 = myF222 ∘ e222` (a measure-preserving coordinate REINDEX
  `e222`). Lifting these flat-core cover facts to a network-loss RLCT statement transports across `e222`
  (`rlctAtOn_dlnLoss222_transport`); the `e222` reindex must stay explicit, not be elided. The cover facts
  here are honestly scoped to the flat core; the `e222`-transport is the consumer's (crux2's) step.
  (Reviewer Q5 — fence tightened in the file docstring @`8bc5819`.)
- **`ι = Fin 1` (the binding leaf), NOT `routeMIota H222`.** This is a complete `IsRouteMCover` family
  (`⨅ = 3/2`), sufficient to validate the bridge end-to-end on the (2,2,2) anchor. Keying the instance to
  the general `routeMIota H222` needs `routeStep H222` concrete — blocked on the PivotWitness
  root-anchoring fix (pp2 g207, surfaced to fm3). The analytic facts are family-independent.
- **`cover_le` is finiteness-only for the bridge.** The `∃-C` prefactor carries the irreducible
  `a^{−c'}·2^d` normalization slack; it rides the `≥`-leg `mul_lt_top` and never enters the `⨅` (the
  threshold reads the exponents). So no explicit per-node change-of-variables is needed for `cover_le`
  (Codex g206, verified vs `RouteMBridge`).

## Kill-conditions

- **A leaf threshold `≠ 3/2`.** Would move `⨅` and break the `cover_ge_div` premise / value match. *Guard:*
  `routeM222_leaf_threshold = 3/2` (`le_antisymm` of the banked `unitMonomialThreshold_ge`/`_le`).
- **The box divergence false at the endpoint `c' = 3/2`.** `cover_ge_div`'s premise is non-strict
  (`monomialThreshold ≤ c'`), so divergence must hold AT `3/2`, not only above. *Guard:*
  `routeM222_box_diverges` is stated non-strict; `leaf_box_div` + `monomialIntegrand_lintegral_box_eq_top`
  both take non-strict threshold premises; `0 < c'` holds at `3/2`. Reviewer-verified faithful.
- **RHS `= 0` (vacuous positivity).** Would make `cover_le`'s scaling step demand `A ≤ 0`. *Guard:*
  `routeM222_rhs_ne_zero` shows the integrand `> 0` on the positive-measure interior `(½,1)^8` (witness
  in-file via `setLIntegral_pos_iff`).
- **Field-type drift from `IsRouteMCover`.** If the `∃-C-inside`, the `*1` weight, or the `ofReal`/`|·|`
  placement differed from crux2's fields, the package would not type-check. *Guard:* reviewer Q1 confirmed
  field-for-field match vs `RouteMBridge` @ `91159e1`.

## Verification ledger

- **fm3 self-build:** green (2707 jobs); `scripts`-grade `sorry` count `= 0` in both files; `#print axioms`
  = clean-three (`RouteMCoverLemmas`) and clean-three `+ monomial_rlct` (the (2,2,2) facts).
- **reviewer (fidelity, PASS):** Q1 field-for-field match (verbatim), Q2 non-strict box-divergence faithful
  (the strict `>` carried only positivity), Q3 RHS positivity sound (interior witness), Q4 names denote
  content, Q5 `myF222`/`dlnLoss` `e222`-seam honestly scoped (docstring fence tightened). Build green,
  axioms clean-three + `monomial_rlct`.
- **Codex (`xhigh`, g206 architecture red-team):** confirmed cover_le finiteness-only; flagged the general
  routeStep decoupling unsound (forced the (2,2,2)-anchor-first scoping). Artifact:
  `codex/g206-routestep-arch-{prompt,answer}.md`.
