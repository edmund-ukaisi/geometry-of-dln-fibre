<task>
Lean 4 / Mathlib RLCT (real log canonical threshold) proof architecture. I hit an obstruction wiring
the L2-PIN2 repair: the RLCT-peel reduction lemma assumes the reg output is CORE-INDEPENDENT, but the
repair makes it core-DEPENDENT. I need the cleanest sound resolution.

THE SETUP (all real, building green except this wiring):
- `DeepestSplit = R × (C × S)` (R=reg, C=core, S=spectator).
- `coreAbsorb : DeepestSplit ≃ₜ DeepestSplit` is a measure-preserving Schur shear: fixes R and S,
  shears the core C (det 1). `coreAbsorb.symm` likewise fixes R, S, changes C.
- `regStraighten : DeepestSplit → DeepestSplit`, `q ↦ (E q, q.2)` (replace reg slot by `E q`, carry
  core+spec). OLD: `E = deepestEPivot` reads (reg, spec) ONLY (core-independent). NEW (repair):
  `E = deepestEFull` reads (reg, core, spec) — the FULL framed product reg blocks, so the squeeze's
  reg energy matches the loss's `Sreg` (the core leak `Y0·T1` is degree-2 and was wrongly dropped).
- The structure field `regAbsorb_rlct` to prove:
    rlctAtOn (fun q => ∑ (regStraighten q).1² + coreF (coreAbsorb q).2.1) 0
      = rlctAtOn (fun q => ∑ q.1²           + coreF (coreAbsorb q).2.1) 0
  where `coreF c = deepestCoreF (raw reduced-core loss)`.

THE LEMMA THAT BREAKS. The peel is currently done in two steps:
  (1) `rlctAtOn_regAbsorb_reduce`: REDUCES the coupled equality (core term has `coreAbsorb`) to the
      DECOUPLED peel (core term WITHOUT `coreAbsorb`), by conjugating BOTH sides with the
      measure-preserving `coreAbsorb.symm` (RLCT-invariant). For the LHS this needs:
        `(regStraighten (coreAbsorb.symm q)).1 = (regStraighten q).1`,
      i.e. the reg output is unchanged by `coreAbsorb.symm`. Its hypothesis `hra_regdep` is exactly
      "reg output depends only on reg+spec slots" — TRUE for deepestEPivot, FALSE for deepestEFull
      (which reads the core that `coreAbsorb.symm` changes).
  (2) `rlctAtOn_comp_localDiffeo`: the actual IFT/#72 peel of `regStraighten` (ContDiff + invertible
      strict-deriv at 0). This step is FINE for deepestEFull (its derivative at 0 is the invertible
      shear [[F,0,G],[0,I,0],[0,0,I]], F=PIN1's invertible frame factor — already proved green).

So step (2) survives; step (1)'s core-independence assumption breaks.

WHAT I KNOW:
- `coreAbsorb` and `coreAbsorb.symm` are MEASURE-PRESERVING (rlctAtOn-invariant under composition,
  via `rlctAtOn_comp_homeomorph`).
- `regStraighten = regStraightenOf2 E` fixes the carried slot: `(regStraighten q).2 = q.2` (so core
  and spec outputs are carried identically); only the reg OUTPUT reads all three slots.
- The genuine goal is just: peel `regStraighten` (a local diffeo at 0) past the rlctAtOn, with the
  core term carrying `coreAbsorb`. The `coreAbsorb` on the core term is the only reason step (1)
  existed (to decouple before the IFT peel).

QUESTION. What is the cleanest SOUND way to prove `regAbsorb_rlct` with a CORE-DEPENDENT reg output?
Rank these options, give the cheapest correct one, and flag any soundness trap:
  (A) Skip the reduce step entirely: apply `rlctAtOn_comp_localDiffeo` (the IFT peel) DIRECTLY to the
      coupled integrand `F q = ∑ q.1² + coreF (coreAbsorb q).2.1`, with π = regStraighten. Does
      `F (regStraighten q) = ∑ (regStraighten q).1² + coreF (coreAbsorb (regStraighten q)).2.1`
      equal the LHS integrand `∑ (regStraighten q).1² + coreF (coreAbsorb q).2.1`? It requires
      `(coreAbsorb (regStraighten q)).2.1 = (coreAbsorb q).2.1`. regStraighten fixes core+spec
      (`(regStraighten q).2 = q.2`), and coreAbsorb's core output reads ... (I need to know what
      coreAbsorb's core output depends on — it's a Schur shear `core ↦ core − Z(I+X)⁻¹Y` reading
      reg+spec). Since regStraighten CHANGES the reg slot (reg ↦ E q), and coreAbsorb's shear reads
      the reg slot, `(coreAbsorb (regStraighten q)).2.1 ≠ (coreAbsorb q).2.1` in general. So (A)
      seems to ALSO break — unless I reorder.
  (B) Reverse the composition order: peel regStraighten FIRST on the decoupled-core integrand, then
      the reduce/coreAbsorb step — i.e. swap which map is conjugated. Does the algebra close?
  (C) Generalize `rlctAtOn_regAbsorb_reduce`'s `hra_regdep` to allow the reg output to depend on the
      core, by conjugating with a map that fixes ALL THREE slots' relevant reads. Is there a
      measure-preserving conjugation that strips coreAbsorb from the core term WITHOUT moving the reg
      output? (coreAbsorb.symm moves the core, which the reg output now reads.)
  (D) Something else (state it).

Also answer: is `regAbsorb_rlct` even TRUE as stated with deepestEFull? (The squeeze comparability is
what matters for the headline; if regAbsorb_rlct's specific phrasing is unprovable, can the structure
field be restated to an equivalent RLCT identity that IS provable, without weakening the chart?)
</task>

<output_contract>
Rank (A)-(D) by correctness+cheapness. Give the single recommended route with the key algebraic
identity that must hold and whether it does. Then answer the truth question. ≤ 12 sentences total.
Flag INFERENCE vs general-fact. End "BIGGEST RISK:" one line.
</output_contract>

<grounding_rules>
You have only my description. Do NOT invent Mathlib lemma names. If an answer depends on what
`coreAbsorb`'s core output reads (which I only partially described), say what you'd need to confirm.
</grounding_rules>
