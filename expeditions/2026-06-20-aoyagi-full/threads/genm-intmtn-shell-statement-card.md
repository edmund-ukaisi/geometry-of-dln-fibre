# Statement card — interior charge free-box (route C, `b=1,a=1`) + the log-integrability atom

Thread `genm-intmtn-shell` (aoyagi-full Stage 2, the interior coupled shell-integration). Branch
`origin/genm-intmtn-shell` (based off schurB's `genm-schurcore-B @0dca0c932`). Module
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJInteriorShell.lean`.

---

## 1. The interior charge free-box (route C — the interior closure for the 3 square `b=1` witnesses)

> **Claim.** For `n ≥ 2`, `p ≥ 2` (`= a+b ≤ ρ`, `ρ = min(n,p)`), the interior CHARGE free-box
> `∫∫_{(A_cor,S)∈box} det((A_cor·S)(A_cor·S)ᵀ)^{−1/2}` is finite (`b=1, a=1`). This IS the interior gate:
> arch1build's definitional read shows the loss factor is `x`-independent and BOUNDED on the interior
> generic cell (`E_top`'s `P·P⁻¹` cancels; `E_tr`'s `Q_inr` is killed by its own orthogonal projector), so
> it pulls out and the gate reduces to the charge.

- **Lean (UNCONDITIONAL headline, LANDED):** `DLNFibre.DLN.RLCT.chargeFreeBox_b1a1_lt_top`
  (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJInteriorShell.lean` @ `a5f5a8554`)
- **Lean (assembly + general form):** `chargeFreeBox_b1_of_inner` (general `a < n`) and its `a=1` corollary
  `chargeFreeBox_b1a1_of_inner` (same file/SHA).
- **Gloss.** `chargeFreeBox_b1a1_lt_top`: for `n ≥ 2` and `p ≥ 2`, the iterated free-box
  `∫⁻_{A_cor∈matBox 1 n 1} ∫⁻_{S∈matBox n p 1} ofReal(chargeGramDet A_cor S ^ (−1/2))` is `< ⊤`.
  (`chargeGramDet A_cor S = det((A_cor·S)(A_cor·S)ᵀ)`; at `b=1` `= ‖A_cor·S‖²`.)
- **Proved.** UNCONDITIONALLY (for `n≥2 ∧ p≥2`). Chain: `chargeFreeBox_b1a1_of_inner` (the assembly:
  `lintegral_mono` on the inner bound → `lintegral_const_mul'` → inline `det_gramRow` → banked
  `detGram_lintegral_lt_top` `r=1`, `a=1<n`) ∘ slabcore/schurB's `corankSlab_charge_sint_le` (the inner
  corank-slab bound `∫_S charge^{−1/2} ≤ C·frobSq^{−1/2}`, via the banked projection-radial core, `S`-first
  pure power). VERIFIED: `scripts/lb` green + forced `#print axioms chargeFreeBox_b1a1_lt_top` =
  `[propext, Classical.choice, Quot.sound]` (the WHOLE chain incl. the crux, not just source-sorry-free);
  zero sorry/admit/axiom in both modules.
- **Cited.** none (native; NO `cited_aoyagi_dln`).
- **Deferred.** `b≥2` interior (general det-Gram slab — schurB's wheelhouse); `ρ<n` for `b≥2`
  (couplerad's rowspace/drop-columns rework). NOT this card.
- **Structure & ideas observed (couplerad + schurB + arch1build, decorrelated).** The interior is
  **POWER-convergent** by integrating `S` FIRST (`∫_S ‖A_cor·S‖⁻¹ dS ≤ C‖A_cor‖⁻¹` uniform, then
  `∫_{A_cor} ‖A_cor‖⁻¹ < ⊤`). There is **NO log** on the interior — the fixed-`S`/`A_cor`-first charge weight
  `W(S) ~ log(1/σ_min(S))` was an integration-ORDER artifact; the `S`-first order avoids it. The genuine log
  lives at the EDGE `a+b = ρ+1` (edgeasm). The `S`-first route SUBSUMES the bulk atom + shell-integration +
  det-pushforward CoV + arcsinh — one banked radial core does it.
- **Route (controller-adopted).** Route C, split: schurB/slabcore own the inner corank slab (via the banked
  radial core); intmtn owns the assembly + the banked outer `detGram` + the unconditional wiring.
- **Status.** sorry-free, UNCONDITIONAL (`chargeFreeBox_b1a1_lt_top` @ `a5f5a8554`, green + clean-three,
  whole chain verified); awaiting a reviewer fidelity check.

---

## 2. The log-integrability atom (re-homed: EDGE tool, reusable bedrock)

> **Claim.** `∫₀^{δ₀} C·(1 + log(1/ε))·ε^s dε < ∞` for `0 < δ₀ ≤ 1`, `−1 < s`, `0 ≤ C` — the log charge
> against a shell measure converges. (Needed at the EDGE `a+b=ρ+1` where the charge genuinely log-diverges;
> NOT on the interior, which is power.)

- **Lean:** `DLNFibre.DLN.RLCT.shellLogWeight_lintegral_lt_top` (+ `shellLogWeight_integrableOn`,
  `log_one_div_le_rpow_neg`) (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJInteriorShell.lean` @ `980a4cc68`)
- **Gloss.** `∫⁻ ε in Ioc 0 t, ofReal(C·(1+log(1/ε))·ε^s) < ⊤` for `0<t≤1`, `−1<s`, `0≤C`; via the
  domination `log(1/x) ≤ η⁻¹·x^{−η}` (any `η>0`) reducing to a power integral (`s−η > −1`).
- **Proved.** Fully, unconditionally. Clean-three `[propext, Classical.choice, Quot.sound]`; zero sorry.
- **Cited / Deferred.** none.
- **Status.** sorry-free (re-homed as the edge tool for edgeasm; reusable clean bedrock).
