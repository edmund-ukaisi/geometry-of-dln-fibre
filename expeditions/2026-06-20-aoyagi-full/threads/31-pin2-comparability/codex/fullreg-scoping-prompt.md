<task>
Lean 4 / Mathlib formalisation scoping decision (DLNFibre harness). I am repairing a FALSE lemma
chain ("PIN2") in a deep-linear-network RLCT proof. The settled math is known (decorrelated, exact);
my question is the cleanest Lean ARCHITECTURE for the repair, and whether one specific step can be
landed sound now or must wait on unwritten geometry.

BACKGROUND (settled, do not re-derive):
- `deepestEPivot q := regResidualPack-pack of the reg blocks (P11-1, P12, P21) of the reindexed
  product of `framedParamsRegPivot ...` (a T=0 / core-ZEROED per-layer framed reconstruction).
- Thread 31 PROVED the old squeeze FALSE: it read the reg blocks off the core-zeroed product, but the
  core leaks into the off-diagonal reg blocks (degree-2 exact cancellation: e.g. P12 = (1+X0)Y1 +
  Y0*T1). So sum(deepestEPivot^2) != Sreg (Sreg = the FULL product's reg energy, which the loss sees).
- FIX (settled): the squeeze's reg term must read the FULL product's reg blocks => a NEW object
  `deepestEFull : DeepestSplit -> (Fin nReg -> R)` reading the reg blocks of the FULL framed product
  `framedParams ...` (core block = the core slot read, NOT 0). Then sum(deepestEFull q)^2 = Sreg.
- PIN1 (`deepestEPivot_regSlice_fderiv`, the invertible reg-slice derivative F) SURVIVES VERBATIM,
  re-used via the bridge `deepestEFull(., 0) = deepestEPivot(., 0)` (core=0+spec=0 kills the leaks)
  + a new atom `d deepestEFull / d core (0) = 0` (leaks are degree-2).

STATE OF THE LEAN FILES (all in lean/DLNFibre/DLN/RLCT/Validate/):
- DONE this tide (green): the IFT generalization. New objects `regStraightenOf2 E_full q := (E_full
  q, q.2)`, `regStraightenTotalCLM2 D_E := D_E.prod snd`, `hasStrictFDerivAt_regStraightenOf2_gen`,
  `regStraightenTotalCLM2_equiv_of_regBlock_isUnit` (block-triangular, det = det F, F invertible).
  These take E_full : R x W -> R (W = core x spec, UN-split). Build green.
- `framedParams_split_eq_frame_raw` is ALREADY a `sorry` (its body): a ~200-300 LoC geometric cert.
  Its CONCLUSION currently asserts `hconj : reindex(P0*(prod(paramsSymm w) - B)*QL) = fromBlocks
  (P00-1) P01 P10 P11` AND the FALSE `h00/h01/h10 : P00/P01/P10 = (reg blocks of the core-ZEROED
  framedParamsRegPivot product)`. The repair DELETES h00/h01/h10 from the conclusion.
- `deepest_loss_squeeze` (sorry-FREE body) consumes the cert; its only use of the false h00/h01/h10
  is one line `hSreg_eq : Sreg = sum(regStraighten (split w)).1^2` via `rw [h00,h01,h10]`. Everything
  else in the squeeze only needs `Phi = Sreg + corePhi` and `(regStraighten q).1 = <the reg object>`.

THE DECISION I want red-teamed. To make the squeeze SOUND now (delete the false load-bearers) WITHOUT
first writing the full `framedParamsFullPivot`/`deepestEFull` geometric machinery (several hundred LoC,
beyond one tide), I plan to:
  (A) DELETE h00/h01/h10 from `framedParams_split_eq_frame_raw`'s conclusion; ADD instead a single
      `hregval_full : E_full (split w) = regResidualPack-pack of (P00-1, P01, P10)` where E_full is
      threaded into the cert AS A HYPOTHESIS (an opaque function `E_full : DeepestSplit -> (Fin nReg
      -> R)`). The cert body STAYS sorry (it was already sorry).
  (B) In `deepest_loss_squeeze`, replace `hregval`/`hSreg_eq` with `hregval_full` + the identity
      `sum(E_full (split w))^2 = Sreg` (from `regResidualPack` bijectivity + the packing). The c1/c2
      arithmetic is unchanged.
  (C) Thread E_full as a parameter through `deepest_regAbsorb_exists` (now using regStraightenOf2)
      and the wiring `deepest_gauge_construction`. The CONCRETE E_full (deepestEFull reading the full
      framed product) + its strict-deriv (deepestEFull_deriv via PIN1+bridge+core-zero atom) are
      ALSO needed for `deepest_regAbsorb_exists`'s peel - and THOSE are the unwritten geometry.

The tension: `deepest_regAbsorb_exists` needs E_full's `HasStrictFDerivAt E_full D_E 0` with reg-block
F invertible (to build the shear equiv). That derivative fact is `deepestEFull_deriv`, which needs the
concrete deepestEFull + the core-zero atom + the bridge to PIN1 - i.e. the unwritten geometry. So
threading E_full as a bare hypothesis into the cert (A/B) makes the SQUEEZE sound, but the WIRING
`deepest_gauge_construction` cannot close `deepest_regAbsorb_exists` without the concrete deepestEFull's
derivative. The wiring would then carry a `sorry` for `deepestEFull_deriv` (a CORRECT-statement sorry).

QUESTIONS:
1. Is (A)+(B) - restructuring the cert's conclusion to drop the false h00/h01/h10 and rest the squeeze
   on `hregval_full` + the packing identity - a SOUND improvement even though the cert body stays
   sorry? I.e. does it remove a FALSE statement from the proof's logical content (the false h00/h01/h10
   are currently *asserted* in the cert's conclusion type, consumed by the squeeze)? Or is leaving the
   cert sorried-but-now-with-a-TRUE-conclusion not actually progress over sorried-with-FALSE-conclusion?
2. Given `deepest_regAbsorb_exists` genuinely needs `deepestEFull_deriv` (unwritten), is the right move
   to (i) land A+B+C with a single new CORRECT-statement sorry for `deepestEFull_deriv` (+ deepestEFull
   def + bridge stated), banking the sound architecture; or (ii) bank ONLY the IFT generalization
   (already green) and report the full E_full machinery as the remaining gap, touching nothing that
   would introduce a new sorry into a currently-sorry-free lemma (deepest_loss_squeeze is sorry-FREE
   today)?
3. Any soundness trap in defining `deepestEFull` to read the FULL framed product `framedParams` (core
   = core slot read) reg blocks, vs the spec's phrasing "regResidualPack of the hconj blocks"? In
   particular: is `sum(deepestEFull (split w))^2 = Sreg` (the cert's full-product reg energy) an IDENTITY
   provable from `regResidualPack` bijectivity alone, or does it ALSO secretly need the
   framedParams<->paramsSymm round-trip (the same geometry the cert's sorry already owns)?
</task>

<output_contract>
Answer Q1, Q2, Q3 in order, each <= 8 sentences. For Q2 give a clear recommendation (i) or (ii) with
the one-line reason. Flag explicitly any place where you are INFERRING from my description vs stating
a general Lean/proof-theory fact. End with a single "BIGGEST RISK:" line.
</output_contract>

<grounding_rules>
You have only my description of the Lean code, not the files. Do NOT invent Mathlib lemma names. If a
claim depends on the exact Lean statement you cannot see, say so. Distinguish "sound proof-theory
fact" from "inference about this specific codebase".
</grounding_rules>
