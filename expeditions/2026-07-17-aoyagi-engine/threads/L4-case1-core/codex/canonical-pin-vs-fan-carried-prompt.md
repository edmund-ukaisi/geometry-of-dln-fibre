<task>
Red-team a PAPER-FIDELITY object ruling for a Lean formalisation of Aoyagi (2023),
"Consideration of the learning efficiency of deep-linear networks" — the b_i / M_{s,k}
divisor-exponent ledger of her resolution-of-singularities recursion.

AOYAGI'S ACTUAL ARGUMENT (verbatim structure from her Thm 3 + the b-ledger recursion):
- Lemma 2 (block elimination): for A = [[A1,A2],[A3,A4]] with A1 a regular r×r block,
  unipotent (regular) Q1,Q2 give Q1·A·Q2 = [[A1,O],[O,C4]], C4 = Schur complement. The
  Q1,Q2 are UNITS of the local ring, so the RLCT is preserved and the variable change is a
  local analytic isomorphism with unit Jacobian.
- Thm 3 (peeling the regular part): the proof begins "We can assume WLOG (absorbing the
  regular part) that ∏ Ā^(s) = [[E_r,O],[O,O]]" — an explicit WLOG normalization to the
  CANONICAL top-left form. The induction carries a regular top-left block C'_1 and the
  Schur complement, all in the canonical (top-left) frame.
- The b-ledger recursion (her Case 1 / Case 2 blow-ups): each blow-up is at a canonical
  position — Case 1(2) introduces the divisor u_{S,J+1} (the coordinate at layer S, cleared
  count J+1, i.e. the DIAGONAL corner of the block being processed); Case 2's divisor is
  u_{S,J+1} with exponent M'_{S,J+1}=(M(S)-J)(M^{(S+1)}-J). After each blow-up "regular Q,P
  reduce D_J'' → [[1,O],[O,D_{J+1}]], advancing J (or S)" — i.e. Q,P REINDEX back to the
  canonical frame for the next step. Her divisor identities are indexed by the CANONICAL
  (S,J+1) diagonal coordinate at every step.

OUR LEAN RENDERING introduces a "fan": the tree of blow-up steps has, at the fresh-clear
cases (her Case 1(2) / Case 2), a FREE choice of WHICH below-diagonal column to clear (a
"fan case-split" in our IsRealBranch predicate — a device to build a COVER of a neighborhood
of the origin by charts; all charts are needed for the cover). On a "fan-free" branch (a
non-canonical choice) the STORED pivot coordinate (where our fold's own clear actually acts)
is NOT the diagonal corner (S,J+1); the two coincide only on the canonical branch.

The formalized invariant (INV) has, among its conjuncts, a b-ledger term μ (the fold's
actual divisor exponents) and a boost law reading μ's exponent AT the coordinate e₂ =
canonPivotOf = the DIAGONAL corner. On a fan-free branch μ lives at the STORED pivot, so
μ(e₂)=0 at the diagonal — the boost law reads the wrong coordinate and breaks.

THE FORK (this is the ruling):
(CANONICAL-PIN) State the INV only on the canonical sub-family (pin the birth pivot = the
  diagonal corner for the INV's regime); stored=diagonal there, the ledger is clean. The
  fan-free charts (needed for the geometric cover) get their per-chart leaf facts (a local
  PrincipalInv: coreGen∘chart = monomial×unit) by TRANSPORTING from the canonical chart via
  the blow-up's chart permutation — an atlas/cover-layer reindexing, claimed to be exactly
  Aoyagi's Lemma-2 Q,P WLOG move (unit Jacobian, RLCT-preserving). Machinery for this
  (RankNormalForm / block_elimination) is already formalized.
(FAN-CARRIED) State the INV on ALL branches incl. fan-free, with μ tracking the diagonal
  identities plus an explicit per-branch stored↔diagonal reindexing bridge inside the INV.
</task>

<output_contract>
1. VERDICT: which resolution is faithful to Aoyagi's argument — CANONICAL-PIN or FAN-CARRIED
   — in one sentence, with your confidence (high/medium/low).
2. THE PAPER EVIDENCE: from the structure above, is Aoyagi's fan-freedom (choice of column
   to clear) a WLOG she normalizes away by Q,P (⟹ canonical-pin), or is it essential content
   her ledger genuinely carries per-branch (⟹ fan-carried)? Cite the specific structural
   points that decide it.
3. THE TRANSPORT SOUNDNESS (canonical-pin's hinge): is "fan-free chart's PrincipalInv ←
   canonical chart's, via the blow-up chart permutation" a CLEAN transport (a relabeling /
   unit-Jacobian isomorphism, RLCT- and monomial-exponent-preserving) or is there a trap
   (the permutation not preserving the monomial×unit shape, or the fan-free charts NOT being
   permutations of the canonical one)? Flag any way this could be a hidden difficulty.
4. THE ONE DISCRIMINATING CHECK: the single cheapest concrete computation (e.g. a specific
   small dimension vector + a specific fan-free chart) that would confirm-or-refute your
   verdict.
</output_contract>

<grounding_rules>
Distinguish explicitly what you can conclude from the STRUCTURE described above (Aoyagi's
WLOG + canonical indexing + Q,P reindex) as FACT, versus what is INFERENCE about the Lean
rendering or the transport that you cannot verify without the actual defs. Do NOT assert the
transport is sound if you can only infer it — say so and give the check in point 4. You do
not have the paper or the Lean source; reason from the structure given.
</grounding_rules>
