<task>
Lean 4 / Mathlib v4.29. I am proving S2: the diffeo-bridge correction `psiSplitDeltaL2` is `ContDiffAt ⊤`
at a point `q ∈ tsupport(cutoffBumpSplit)`. I have S4 (the strict-deriv-0 version) fully landed, including
all the per-entry building blocks AT THE ORIGIN q=0. I need to choose the cleanest structure for S2 and
want your judgement on ONE design decision.

CONTEXT (all landed, sorry-free):
- `psiSplitDeltaL2 q = psiSplitRawL2Core q − q` (at L=2), and the lens decomposition
  `psiSplitDeltaL2Core_eq_payload`: it equals the encoded payload triple
  `(regGaugeCLE.symm(l2GaugeΔ q).1, (paramsFlatCLE(l2CoreΔTuple q), regGaugeCLE.symm(l2GaugeΔ q).2))`.
- The payloads decode to matrix entries of `l2T1p − l2T1` (core) and `l2Y1p − l2Y1` (gauge).
- `l2T1p = W⁻¹ · Br` where W = 1 + Z1·A1⁻¹·A0⁻¹·Y0, Br = (1−K)·S1 + U + R·T1, K = Z1·P00⁻¹·Y0, etc.
- I have entrywise ContDiffAt facts AT q=0: contDiffAt_l2{A0,A1,P00,W}_inv_entry, contDiffAt_l2{K,R,U,S1,Br}_entry,
  all proven at 0 (where det A0=det A1=det P00=det W=1).
- `contDiffAt_matrix_inv_entry_of_det_ne_zero_at` (ContDiffAt entries + det≠0 at the point ⟹ inverse entry ContDiffAt).
- `cutoffBumpSplit : ContDiffBump (0 : DeepestSplit)` currently has rIn=unitRadius/4, rOut=unitRadius/2,
  where `unitRadius` is a radius with `ball 0 unitRadius ⊆ unitSet = {p | ∀s, det(1+readX p s) ≠ 0}`.
  unitSet is on the GAUGE slot `(Reg × Gauge)`; the bump is on the FULL split `DeepestSplit = Reg × (Core × Spec)`.
  The bump's radius only guarantees the per-pivot `1+readX_s` invertibility, NOT det W ≠ 0 or det P00 ≠ 0.

THE PROBLEM: at a general `q ∈ tsupport(cutoffBumpSplit)`, I need det A0 ≠ 0, det A1 ≠ 0, det P00 ≠ 0,
det W ≠ 0 to make the inverse entries ContDiffAt at q. The current bump radius only gives the readX pivots.

The recipe says: RE-KEY cutoffBumpSplit to a "joint-unit radius" — a radius small enough that all three
det conditions hold on the closed support. P00=W=1 at 0, continuous on the readX-unit locus, so a small
ball works. The re-key is local (downstream uses cutoffBumpSplit only via ContDiffBump fields +
eventuallyEq_one + radii, all abstract; controller pre-approved).
</task>

<questions>
1. To define the joint-unit radius I need a SET `jointUnitSet ⊆ DeepestSplit` that is OPEN and contains 0,
   on which det A0, A1, P00, W are all ≠ 0. The wrinkle: det W and det P00 involve A0⁻¹/A1⁻¹, so they are
   only CONTINUOUS on the locus where det A0, det A1 ≠ 0 (the readX-unit locus pulled back via the
   projection q ↦ (q.1,q.2.2)). So jointUnitSet = (readX-unit-proj) ∩ {det P00 ≠ 0} ∩ {det W ≠ 0}.
   Is the cleanest openness proof:
   (a) jointUnitSet := readXUnitProj ∩ Wdet⁻¹{≠0} ∩ P00det⁻¹{≠0}, prove open by: readXUnitProj open
       (preimage of unitSet under the continuous projection); then on readXUnitProj, det W and det P00
       are continuous (ContinuousOn), so {det W ≠ 0} ∩ readXUnitProj is open IN readXUnitProj, hence
       (since readXUnitProj is open in DeepestSplit) open in DeepestSplit. Use `ContinuousOn.isOpen_inter_preimage`
       or `IsOpen.inter` with the global continuity? det W is NOT globally continuous. What's the cleanest
       Mathlib idiom for "S open, f continuous-on S, {f ≠ 0} ∩ S open in the ambient space"?
   (b) Alternatively, avoid det W entirely: note that the bump only needs the support inside a NEIGHBOURHOOD
       of 0 on which the payload entries are ContDiffAt. Since the payload entries are ContDiffAt AT 0
       (already proven), and ContDiffAt is an open condition... NO — ContDiffAt at 0 doesn't give ContDiffAt
       nearby. So (b) doesn't work; I need the actual det conditions on a neighbourhood. Confirm (a) is the way.

2. For S2 itself, given the re-keyed bump guarantees the three det conditions on tsupport, I need
   GENERALIZED versions of my entry-ContDiffAt facts at a general q with det hypotheses (currently they're
   at q=0). Is it cleaner to (i) re-prove each contDiffAt_l2*_entry at general q taking det hyps, or
   (ii) keep them at 0 and prove S2 only needs ContDiffAt at 0?? — NO, S2 is explicitly at q ∈ tsupport,
   not 0. So (i). For the generalized inverse-entry facts, I use contDiffAt_matrix_inv_entry_of_det_ne_zero_at
   with the det≠0 hypothesis at q. Confirm the dependency order: A0⁻¹/A1⁻¹/P00⁻¹ entries need their own
   det≠0 at q; W⁻¹ entry needs det W ≠ 0 at q AND (W's entries ContDiffAt at q, which need A0⁻¹/A1⁻¹ at q).
   Any subtlety in threading the det hypotheses, or is it mechanical?

3. Is there a SHORTER path I'm missing — e.g. proving `ContDiffOn ⊤ psiSplitRawL2Core jointUnitSet` once
   (via the encode/decode being ContDiffOn) and deriving ContDiffAt at each tsupport point by openness?
   Versus per-point ContDiffAt. Which is less Lean friction at this pin?
</questions>

<output_contract>
Answer the 3 questions concisely. For Q1 give the exact Mathlib lemma name(s) for the openness idiom.
For Q3 give a clear recommendation (ContDiffOn-once vs per-point) with the reason. Keep under 400 words.
</output_contract>
