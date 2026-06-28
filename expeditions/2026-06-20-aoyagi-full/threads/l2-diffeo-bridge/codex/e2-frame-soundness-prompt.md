<task>
I am formalising (Lean 4) a "diffeo bridge" lemma for the L=2 case of a deep-linear-network
RLCT computation. I need to determine the CORRECT HYPOTHESES on the endpoint frames, before
sinking a multi-hundred-line build. This is a soundness-fidelity question, not a Lean-syntax one.

SETUP (L=2, two layers, deepest point of a rank-r fibre):
- A reparametrization Ψ acts on the last-layer core T1 and last-layer reg-read Y1, holding the
  three "reg blocks" (P00, P01, P10) of a framed matrix product FIXED, so that a regular-energy
  function `deepestEFull` is invariant: `deepestEFull ∘ Ψ = deepestEFull` (call this E2).
- The framed product is `P = endpointP0 · (prod − B) · endpointQL` reindexed, then block-split
  r×r / rest. The endpoint frames are `Pf : (s:Fin L)→ GL(H s.castSucc)` (left) and
  `Qf : (s:Fin L)→ GL(H s.succ)` (right), per-layer.
- A prior pen-and-paper + decorrelated-Codex finding (verified numerically): E2 is UNSOUND at
  GENERAL invertible endpoint frames — it FAILS ~7/8 random general frames, because the endpoint
  conjugation "leaks" Ψ's moved (2,2) block P11 into the read reg blocks UNLESS the frames are
  BLOCK-TRIANGULAR (Pf block-lower, Qf block-upper). The fix was: construct block-triangular
  frames (needs the corner's leading r×r block invertible — I have that lemma now).
- E2 was originally pp-VERIFIED only at IDENTITY endpoint frames.

THE L=2 SPECIFICS I need adjudicated:
- At L=2 the two layers are firstLayer (s=0) and lastLayer (s=1). The frame bundle gives:
  `Qf (firstLayer) = 1` and `Pf (lastLayer) = 1` (boundary frames are IDENTITY — call these hQf0, hPfL).
  But `Pf (firstLayer) = Pf 0` and `Qf (lastLayer) = Qf 1` are the GENERIC rank-normal-form frames
  (invertible, NOT proven block-triangular, NOT identity).
- So at L=2: TWO of the four frames are identity (Qf 0, Pf 1); TWO are generic (Pf 0, Qf 1).

QUESTIONS (the adjudication I need):
1. For the E2 reg-preservation (`P01' = P01` via the A0·A0⁻¹=I cancellation, where A0 = 1+X0 is a
   per-layer reg read, NOT a frame), which endpoint frames actually ENTER the P01 block computation
   at L=2? Is P01 read through `Pf 0`/`Qf 1` (the generic ones), or only through the identity
   boundary frames `Qf 0`/`Pf 1`?
2. Given the "fails at general frames" finding: does the L=2 bridge REQUIRE a block-triangularity
   hypothesis on `Pf 0` / `Qf 1` (i.e. the current arbitrary-Pf/Qf signature is INSUFFICIENT for a
   sound E2 and silently relies on an unstated triangular-frame property), OR does the L=2 reduction
   make the generic frames drop out of the P01 read (so identity-boundary + generic-interior
   suffices, no triangularity hypothesis needed)?
3. If a triangularity hypothesis IS needed: what is the minimal correct hypothesis to add to the
   bridge signature, and is it dischargeable at L=2 from the corner-leading-block invertibility
   (the lemma I have) via the explicit block-lower normalizer `[[A11⁻¹,0],[−A21·A11⁻¹,I]]`?
</task>

<output_contract>
Three sections, terse:
1. WHICH FRAMES ENTER P01 AT L=2 — name them (Pf 0 / Qf 1 / identity-boundary), and say whether
   the P01 block read passes through the generic frames or not. State explicitly what is INFERENCE
   vs what follows necessarily from the block-conjugation structure.
2. VERDICT — does the L=2 bridge NEED a frame-triangularity hypothesis (signature insufficient as
   stated) or NOT (generic frames drop out)? One of: NEEDS-TRIANGULARITY / GENERIC-DROPS-OUT /
   UNDETERMINABLE-WITHOUT-MORE-INFO (+ what info).
3. IF NEEDS-TRIANGULARITY — the minimal hypothesis + whether the corner-leading-block invertibility
   discharges it at L=2.
</output_contract>

<grounding_rules>
You do NOT have the Lean source. Reason from the block-matrix structure I described. Flag every
step that is an INFERENCE from the conjugation structure vs a claim you cannot make without seeing
the exact `deepestEFull` / `framedParamsPivot` definitions. If the answer genuinely depends on a
definition I have not given (e.g. exactly how Pf/Qf compose into P), say so and name the one fact
you'd need. Do NOT guess a confident verdict if the structure is underdetermined.
</grounding_rules>

<additional_grounding>
I have now READ the Lean defs of the framed product composition (these are FACTS, not inference):
- `endpointP0 = Pf 0` (the FIRST layer's left frame, cast to Fin (H 0)).
- `endpointQL = Qf (lastLayer)` (the LAST layer's right frame; at L=2, = Qf 1).
- The framed product is `P = endpointP0 · (prod − B) · endpointQL = (Pf 0) · (prod − B) · (Qf 1)` (reindexed, then r×r/rest block-split).
- `deepestEFull` reads P's blocks (P00−1, P01, P10) — so P01 is read THROUGH `Pf 0` (left) and `Qf 1` (right).
- The frame bundle's L=2 boundary-identity facts are `Qf 0 = 1` (hQf0) and `Pf 1 = 1` (hPfL) — these are the OTHER two frames, NOT the ones in the product.

So at L=2 the framed-product read passes through EXACTLY the two GENERIC frames `Pf 0` and `Qf 1`
(the identity boundary frames `Qf 0`/`Pf 1` are NOT in the product). Given this, re-answer Q2/Q3
with this fact incorporated: does the bridge need `Pf 0` block-lower + `Qf 1` block-upper as
hypotheses (since the general-frame E2-failure now provably applies)?
</additional_grounding>
