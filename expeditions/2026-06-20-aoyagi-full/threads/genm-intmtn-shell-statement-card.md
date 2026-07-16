# Statement card — interior charge free-box (route C, `b=1,a=1`) + the log-integrability atom

Thread `genm-intmtn-shell` (aoyagi-full Stage 2, the interior coupled shell-integration). Branch
`origin/genm-intmtn-shell` (based off schurB's `genm-schurcore-B @0dca0c932`). Module
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJInteriorShell.lean`.

---

## 1. The interior charge free-box (route C — the interior closure for the 3 square `b=1` witnesses)

> **Claim.** For the interior scope `a+b ≤ n ∧ a+b ≤ p` (`= a+b ≤ ρ`, `ρ = min(n,p)`), ALL `b`, the interior
> CHARGE free-box `∫∫_{(A_cor,S)∈box} det((A_cor·S)(A_cor·S)ᵀ)^{−a/2}` is finite. This IS the interior gate:
> arch1build's definitional read shows the loss factor is `x`-independent and BOUNDED on the interior
> generic cell (`E_top`'s `P·P⁻¹` cancels; `E_tr`'s `Q_inr` is killed by its own orthogonal projector), so
> it pulls out and the gate reduces to the charge.

- **Lean (UNCONDITIONAL headline, LANDED — general `b`):** `DLNFibre.DLN.RLCT.chargeFreeBox_lt_top`
  (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJInteriorShell.lean` @ `8edeb7231`); the `b=1, a=1` special case
  is `chargeFreeBox_b1a1_lt_top` (subsumed).
- **Lean (assembly + general form):** `chargeFreeBox_of_inner` (`b`-general outer, `a+b ≤ n`),
  `chargeFreeBox_b1_of_inner` (`b=1`, general `a < n`), `chargeFreeBox_b1a1_of_inner` (`b=1,a=1`) — same file.
- **Gloss.** `chargeFreeBox_lt_top`: for `a+b ≤ n` and `a+b ≤ p`, the iterated free-box
  `∫⁻_{A_cor∈matBox b n 1} ∫⁻_{S∈matBox n p 1} ofReal(chargeGramDet A_cor S ^ (−a/2))` is `< ⊤`.
  (`chargeGramDet A_cor S = det((A_cor·S)(A_cor·S)ᵀ)`, the `b×b` corank-Gram det; at `b=1` `= ‖A_cor·S‖²`.)
- **Proved.** UNCONDITIONALLY (for `a+b ≤ n ∧ a+b ≤ p`, all `b`). Chain: `chargeFreeBox_of_inner` (the
  `b`-general outer: `lintegral_mono` on the inner → `lintegral_const_mul'` → banked
  `detGram_lintegral_lt_top` `r=b`, `a < n−b+1`) ∘ slabD's `CorankSlabD.corankSlabD_charge_sint_le` (the
  `b`-general inner corank-slab `∫_S charge^{−a/2} ≤ C·det(A_cor·A_corᵀ)^{−a/2}`, the coupled Wishart-det
  negative-moment slab, couplerad's §w3-atlas recursion). VERIFIED: `scripts/lb` green + forced
  `#print axioms chargeFreeBox_lt_top` = `[propext, Classical.choice, Quot.sound]` (the WHOLE chain incl.
  slabD's crux, not just source-sorry-free); zero sorry/admit/axiom in both new modules.
- **Cited.** none (native; NO `cited_aoyagi_dln`).
- **Deferred.** `ρ<n` coordinate-`P_J` cases (couplerad's rowspace/drop-columns rework) are a separate
  scope note, handled by slabD's `a+b≤p` (S-column) hypothesis; not a gap in this closure.
- **Structure & ideas observed (couplerad + schurB + arch1build, decorrelated).** The interior is
  **POWER-convergent** by integrating `S` FIRST (`∫_S ‖A_cor·S‖⁻¹ dS ≤ C‖A_cor‖⁻¹` uniform, then
  `∫_{A_cor} ‖A_cor‖⁻¹ < ⊤`). There is **NO log** on the interior — the fixed-`S`/`A_cor`-first charge weight
  `W(S) ~ log(1/σ_min(S))` was an integration-ORDER artifact; the `S`-first order avoids it. The genuine log
  lives at the EDGE `a+b = ρ+1` (edgeasm). The `S`-first route SUBSUMES the bulk atom + shell-integration +
  det-pushforward CoV + arcsinh — one banked radial core does it.
- **Route (controller-adopted).** Route C, split: schurB/slabcore own the inner corank slab (via the banked
  radial core); intmtn owns the assembly + the banked outer `detGram` + the unconditional wiring.
- **Status.** sorry-free, UNCONDITIONAL for ALL `b` (`chargeFreeBox_lt_top` @ `8edeb7231`, green +
  clean-three, whole chain incl. slabD verified); awaiting a reviewer fidelity check.

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
