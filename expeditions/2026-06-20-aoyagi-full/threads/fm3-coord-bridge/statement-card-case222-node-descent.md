# Statement card — the standalone (2,2,2) `RouteMNodeDescent` anchor (#147, the "(B)" anchor)

> **Claim.** There is a concrete `(2,2,2)` `RouteMNodeDescent` datum — built standalone from the
> sympy-verified Schur certificate, decorrelated from rs-grind's general producer — whose per-node
> `descentStep` reads `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss (1,1,2) 0) 0` with `nReg = 2`,
> and which composes to the `(2,2,2)` value `3/2` given the reduced `(1,1,2)` child RLCT `1/2`.

- **Lean:** `DLNFibre.DLN.RLCT.routeMNodeDescent222`,
  `DLNFibre.DLN.RLCT.routeMNodeDescent222_descentStep`,
  `DLNFibre.DLN.RLCT.routeMNodeDescent222_descentStep_eq_three_halves`
  (`lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean` @ `<set-at-integration>`)
  Supporting: `transport222` (the `ReducedTransport`), `dlnLoss_Sred_entry` (the reduced-core identity),
  `dlnLoss_Sred_ne_ae` / `GRed222_ne` (germ-nonvanishing), `hnode222` (the Schur presentation).

- **Gloss.** `routeMNodeDescent222 : RouteMNodeDescent M222route (schurState M222route M222_hlo) 2 YRed222`
  is produced by `RouteMNodeDescent.ofNodePresentation`, fed:
  - `transport222 : ReducedTransport (schurState M222route M222_hlo) YRed222` with `Y = Fin (flatDim
    (1,1,2)) → ℝ`, `redEmbed = (paramsEquivFlat (1,1,2)).symm` (the proven MP flattening homeomorphism),
    `G = √(dlnLoss (1,1,2) 0 ∘ redEmbed)`;
  - `flatCore222 w = (∑ⱼ w.1ⱼ²) + (∑ᵢⱼ (bcol·w.1ⱼ + SΓ)²)`, the cert's Schur-normal-form SHAPE, with
    `SΓ222 w () = α·[β0,β1]` (`α = (redEmbed w.2)⁰₀₀`, `[β0,β1] = (redEmbed w.2)¹₀·`) and `bcol222 w () =
    w.1 0`.
  `descentStep` reads `rlctAtOn flatCore222 (0,0) = 2/2 + rlctAtOn (dlnLoss (1,1,2) 0) (fun _ => 0)`.

- **Proved (unconditionally, axiom-clean `[propext, Classical.choice, Quot.sound]`):**
  - `dlnLoss_Sred_entry`: `dlnLoss (1,1,2) 0 A = (α·β0)² + (α·β1)²` — the cert's reduced core `G² =
    (y3−y2y1)²·(x6²+x7²)` (`α = y3−y2y1`, `[β0,β1] = [x6,x7]`), entrywise.
  - The full `ReducedTransport` (MP det-1 reindex closing `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss (1,1,2)
    0) 0`): `hmp`, `hemb`, `hzero` (`rfl`), `hredCore` (`Real.sq_sqrt`).
  - `dlnLoss_Sred_ne_ae` / `GRed222_ne`: the reduced loss is nonzero a.e. (zero-set = two coordinate
    hyperplanes, null; via `Measure.ae_eval_ne` transported through the MP equiv) — the S1.5 hygiene.
  - `hnode222`: the three `ofNodePresentation` conjuncts hold on `{w | (w.1 0)² < 1}` with `T = 1`;
    `‖SΓ‖² = dlnLoss (1,1,2) 0` faithfully (so the cert's reduced core enters genuinely).
  - `routeMNodeDescent222_descentStep`: `rlctAtOn flatCore222 (0,0) = 2/2 + rlctAtOn (dlnLoss (1,1,2)
    0) 0` (the squeeze `nReg/2`-split ∘ the MP transport — both SOUND, NO blow-up-Jacobian bridge).
  - `routeMNodeDescent222_descentStep_eq_three_halves`: `rlctAtOn flatCore222 (0,0) = 3/2` GIVEN `hred`.

- **Assumed.** `hred : rlctAtOn (dlnLoss (1,1,2) 0) (fun _ => 0) = 1/2` — the reduced `(1,1,2)` child
  RLCT (the cert's `lambdaCore(1,1,2)`), the recursion's child value, carried as a hypothesis (the
  recursion base supplies it; not re-derived here). `nReg = 2` is hard-coded (numerically agrees with
  `nRegOf_M222 = 2`, the cert's three independent confirmations).

- **Cited.** none new (the `(2,2,2)` headline's `≤`-half cited bound is elsewhere, not used here).

- **Deferred (NOT proved — named, not omitted):**
  - `flatCore222` is a Schur-normal-form-SHAPED object, NOT proven equal to the genuine `(2,2,2)`
    post-blow-up `core ‖Â·B‖²`. That identification is the blow-up-Jacobian bridge (flagged unsound for
    the raw MP-chart route in `RouteMO1Bridge`; deliberately uninvoked). Consequently the file does NOT
    prove `rlctAtOn flatCore222 (0,0) = rlctAtOn (dlnLoss H222 0) deepest222`; the `3/2` value
    NUMERICALLY equals the committed `case222_rlctAtOn_eq = 3/2` (a coincidence, not an identification).
  - `bcol222 = w.1 0` is a contract-satisfying pivot-column placeholder (squeeze-absorbed,
    RLCT-irrelevant), NOT the cert's independent column `y2`; the C1 defect mechanism (`y2·Erow`) is thus
    represented only at the level of the abstract `hnode` contract, not the verified blow-up geometry.
  - `redEmbed222` is the generic MP flattening, NOT the cert's explicit Schur shear `(y3−y2y1) ↦ y3'`
    (unnecessary here since `Y` is already the flattened reduced `Params (1,1,2)` with `α` a single coord).

- **Status.** sorry-free + reviewed (reviewer verdict PASS-WITH-CAVEATS, fidelity 2026-06-23; the
  flagged docstring overclaims were corrected to the Proved/Deferred split above; Codex-decorrelated on
  the soundness judgments, banked at `codex/case222-anchor-review-{prompt,answer}.md`).
