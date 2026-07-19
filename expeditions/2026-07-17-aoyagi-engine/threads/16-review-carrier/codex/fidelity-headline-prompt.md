<task>
You are red-teaming a Lean 4 / Mathlib formalisation for a FIDELITY + NON-VACUITY audit. I am a
reviewer; I want you to attack the following theorem's fidelity and hunt for vacuity or overclaim.
Do NOT trust my framing — look for the hole.

CONTEXT. A resolution-tree engine `buildTree M (conOracle M) s` recurses a blow-up construction over
a "connection state" `ConState L`. Each internal (branch) node carries a `StepData M` and a list of
`Edge M`. A per-node blow-up "center" of dimension `dCenterOfNode M node` is selected by a map
`realCNode M node hd : Fin (dCenterOfNode M node) → Fin (flatDim M)` (the "intended" center
coordinates), and a totality-guarded variant `cNodeOf` that falls back to `Fin.castLE` off the
"reachable cone" so it is always injective. The FIDELITY claim is: on the reachable cone,
`cNodeOf = realCNode` (the fallback is never taken — the intended selector is genuinely injective).

`dCenterOfNode`: terminal/rollover => 0; case-2 (occ.min? = none) => resRows*resCols; case-1
(occ.min? = some target) => 1 + (target - cleared)*resCols.

`realCNode` case-1 selects `Fin.append (uCornerSel …) (resBlockOrFallback …)`: a 1-dim "u-corner"
(the merged divisor's immutable birth corner (a,b,b) as a flat coord `flatCoordOf M ⟨a⟩ ⟨b⟩ ⟨b⟩`)
APPENDED to a `(target-cleared) × resCols` residual block at layer `node.layer`, corner `(cleared,
cleared)`. Injectivity of the append needs the u-corner range DISJOINT from the block range.

THE HEADLINE UNDER AUDIT:

    theorem cNodeOf_eq_realCNode_of_conOracle {M : Fin (L + 1) → ℕ} (s : ConState L)
        (dinv : DivBirthInv M s) (node : StepData M) (edges : List (Edge M))
        (htree : buildTree M (conOracle M) s = ResolutionTree.branch node edges)
        (hd : dCenterOfNode M node ≤ flatDim M) :
        cNodeOf M node hd = realCNode M node hd

The claim is this is "DivBirthInv-ONLY" (no separate chooser-totality "OracleInv" hypothesis is
needed).

DivBirthInv M s bundles, over every divisor k of state s:
  (validity)  divBirthCoord k = (a,b) has a<L, b<M^(a), b<M^(a+1);
  (layer bd)  a ≤ s.layer;
  (freshness) a = s.layer → b < s.cleared;
  (inj)       divBirthCoord injective.
It is established at conRoot (numDiv=0, vacuous: `DivBirthInv_conRoot`, depends on NO axioms) and
maintained through every conOracle step-child (`DivBirthInv_conOracle_stepChildren`, axiom-clean).

PROOF SKELETON of the headline (paraphrased):
  destructure dinv into ⟨hvalid, _, hfresh, _⟩.
  case L ≤ layer: conOracle = oracleTerminal => buildTree is a LEAF, contradicts htree=branch.
  case rollover (widthMinUpto(layer+1) ≤ cleared): node has dCenterOfNode=0; use
    realCNode_injective_of_dCenterOfNode_zero (vacuous, empty domain).
  case-2 (occ.min?=none): nodeOccMin node = none => RealCNodeFacts holds VACUOUSLY (the ∀ target,
    nodeOccMin = some target → … premise is never satisfiable); apply cNodeOf_eq_realCNode_of_facts.
  case-1 (occ.min?=some target):
    - subcase chooseMin s target = none: conOracle = oracleTerminal => LEAF, contradicts htree=branch.
      (THIS is where "no OracleInv" comes from: chooser success is FORCED by htree being a branch.)
    - subcase chooseMin s target = some f: supply RealCNodeFacts. The u-corner facts (a<L, row/col
      bounds, freshness a=layer→b<cleared) come from `hvalid f` and `hfresh f`; the block-fit bounds
      (cleared + (target-cleared) ≤ M^(layer), cleared + resCols ≤ M^(layer+1)) come from the occ
      membership bounds + widthMinUpto_le + an `omega`.

DISJOINTNESS lemma the case-1 injectivity rests on (`uCornerSel_ne_resBlockOrFallback`): assume the
u-corner flat coord = a block flat coord; `flatCoordOf_val_inj` forces layer a = node.layer and
column b = cleared + r (r≥0); then freshness (a=layer → b<cleared) contradicts b = cleared+r ≥
cleared. QED.

I have already verified: the module builds green; `#print axioms` on the headline (and all sibling
headlines) = exactly [propext, Classical.choice, Quot.sound]; the reachability supply lemmas exist
and compose.
</task>

<output_contract>
Answer in these sections, terse:

1. VACUITY VERDICT. Is the headline vacuously true or non-trivially instantiable? Specifically:
   (a) Is `dinv : DivBirthInv M s` inhabited for reachable s (root + maintenance ⟹ yes/no)?
   (b) Is `htree = branch node edges` co-satisfiable with dinv for at least one real s (i.e. does a
       branch node with a nonzero-dim center actually occur, so case-1/case-2 are not empty)?
   (c) Does the case-2 "RealCNodeFacts holds vacuously" step HIDE a gap — i.e. is case-2's fidelity
       real, or does it lean on an empty premise that would also be empty for a BOGUS selector?

2. SCOPE VERDICT. Does the headline give fidelity at the SUBTREE-ROOT node of s only, or at every
   internal node of the whole conRoot tree? If only the subtree root, name precisely what extra
   lemma coverage still needs to lift it to all internal nodes, and whether that is a defect of THIS
   theorem or a separate coverage obligation.

3. "DivBirthInv-ONLY" VERDICT. Is deriving chooseMin-success from "htree is a branch, not a leaf"
   legitimate, or does it smuggle an assumption? Is there any conOracle branch where buildTree yields
   a `branch` yet chooseMin FAILS (which would make the contradiction step unsound)?

4. DISJOINTNESS ATTACK. Find any case where the u-corner CAN collide with the block despite
   DivBirthInv: e.g. a divisor born at an EARLIER layer a<layer whose flat coord coincides; or the
   merged divisor f itself having a = layer but b ≥ cleared (freshness violated?). Is `hfresh f` the
   right freshness instance for the MERGED divisor being cleared at this step?

5. NAME-HONESTY. Does `cNodeOf_eq_realCNode_of_conOracle` overclaim? Should the name/scope be
   narrowed?

6. SHARPEST RESIDUAL DOUBT. The one thing you'd still check if you had the full source.
</output_contract>

<grounding_rules>
Distinguish (OBSERVED) — forced by the skeleton/signatures I gave — from (INFERRED) — your reasoning
about what the unseen full source probably does. Do not assert a defect as fact unless the skeleton
forces it; flag suspicions as suspicions with the concrete check that would settle them. If a step is
sound, say so plainly; do not manufacture doubt.
</grounding_rules>
