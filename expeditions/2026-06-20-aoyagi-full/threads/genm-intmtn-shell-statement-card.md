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

- **Lean (assembly, LANDED conditional):** `DLNFibre.DLN.RLCT.chargeFreeBox_b1_of_inner` (general `a < n`)
  and its `a=1` corollary `chargeFreeBox_b1a1_of_inner`
  (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJInteriorShell.lean` @ `980a4cc68`)
- **Lean (unconditional headline, PENDING):** `chargeFreeBox_b1a1_lt_top` — trivial wiring
  `chargeFreeBox_b1a1_of_inner hn C hC hinner` once schurB lands `corankSlab_charge_sint_le`.
- **Gloss.** `chargeFreeBox_b1a1_of_inner`: given `n ≥ 2` and a uniform inner bound
  `∀ A_cor, ∫⁻_{S∈matBox n p 1} ofReal(chargeGramDet A_cor S ^ (−1/2)) ≤ C·ofReal(frobSq A_cor ^ (−1/2))`
  with `C < ⊤`, the iterated free-box `∫⁻_{A_cor∈matBox 1 n 1} ∫⁻_{S∈matBox n p 1}
  ofReal(chargeGramDet A_cor S ^ (−1/2))` is `< ⊤`.
- **Proved.** The assembly, unconditionally in the inner bound: `lintegral_mono` (the inner bound,
  pointwise in `A_cor`) → `lintegral_const_mul'` (pull `C`) → inline `det_gramRow`
  (`frobSq A_cor = det(A_cor·A_corᵀ)`) → banked `detGram_lintegral_lt_top` (`r=1`, exponent `−1/2 = −a/2`
  at `a=1 < n`). Clean-three `[propext, Classical.choice, Quot.sound]`; zero sorry.
- **Assumed (interface, to be discharged).** The inner uniform charge bound `hinner` — exactly schurB's
  `corankSlab_charge_sint_le {n p} (hp : 2 ≤ p)` (confirmed type-checks in this shape; schurB is proving
  it via the banked qbox projection-radial core `projection_rpow_lintegral_uniform`, the `S`-first pure-power
  route: `𝔼^{n·p}` column-along-`Â_cor` subspace `V` of finrank `p`, `‖A_cor·S‖ = ‖A_cor‖·‖P_V S‖`,
  box⊆ball, `a=1<p`). On its landing, `hinner` discharges and `chargeFreeBox_b1a1_lt_top` becomes
  unconditional.
- **Cited.** none (native; NO `cited_aoyagi_dln`).
- **Deferred.** `b≥2` interior (general det-Gram slab — schurB's wheelhouse); `ρ<n` for `b≥2`
  (couplerad's rowspace/drop-columns rework). NOT this card.
- **Structure & ideas observed (couplerad + schurB + arch1build, decorrelated).** The interior is
  **POWER-convergent** by integrating `S` FIRST (`∫_S ‖A_cor·S‖⁻¹ dS ≤ C‖A_cor‖⁻¹` uniform, then
  `∫_{A_cor} ‖A_cor‖⁻¹ < ⊤`). There is **NO log** on the interior — the fixed-`S`/`A_cor`-first charge weight
  `W(S) ~ log(1/σ_min(S))` was an integration-ORDER artifact; the `S`-first order avoids it. The genuine log
  lives at the EDGE `a+b = ρ+1` (edgeasm). The `S`-first route SUBSUMES the bulk atom + shell-integration +
  det-pushforward CoV + arcsinh — one banked radial core does it.
- **Route (controller-adopted).** Route C, split: schurB owns the inner corank slab (via the banked radial
  core); intmtn owns the assembly + the banked outer `detGram`.
- **Status.** assembly sorry-free (conditional on the interface); unconditional headline pending schurB's
  inner + a reviewer fidelity check.

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
