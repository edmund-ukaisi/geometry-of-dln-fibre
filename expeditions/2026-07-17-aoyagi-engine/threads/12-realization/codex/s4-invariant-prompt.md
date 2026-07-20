<task>
Lean 4 + Mathlib v4.29. DESIGN REVIEW (not full code) for the hardest proof in a formalisation engine:
`tStar_realized`. I need the CLEANEST per-state invariant + induction structure. A prior design consult's
answer was LOST; you are re-deriving it. cwd is a git worktree of repo geometry-of-dln-fibre; read the
actual files under lean/DLNFibre/DLN/RLCT/Engine/.

TARGET (lean/DLNFibre/DLN/RLCT/Engine/O5Realization.lean, currently `sorry`):
  theorem tStar_realized (M : Fin (L+1) → ℕ) (hL : 0 < L) :
    ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L)),
      ∃ k : Fin l.numDiv, l.divProfile k = tStar M
i.e. the Mval-minimizer `tStar M` (proven `Clearable M (tStar M)` by `clearable_tStar`; proven
`tStar M ∈ Adm M`) appears as a t̃=0 analytic-divisor profile at SOME leaf of the deterministic built tree.

READ THESE (all in EngineConstruction.lean unless noted):
- `buildTree M oracle s = WellFounded.fix (conRel_wf M) fun s rec => match oracle s with
    | .terminal l _ => .leaf l
    | .step node children _ _ _ => .branch node (children.map (fun c => Edge.mk c.ecase c.esubst (rec c.child c.hdesc)))`
- `buildTree_terminal` / `buildTree_step` (:431,:440); `edgesLeaves_eq` (:2402): leaves of a branch =
  `children.flatMap (fun e => leaves e.child)`. `leaves_isFullMono` (:2461) is the ∀-over-leaves WF-induction
  TEMPLATE — I need the EXISTENTIAL steered analog (exhibit ONE leaf via the R(tStar)-steered child at each step).
- `conOracle M s` (:2090) dispatches: TERMINAL if `L ≤ s.layer` (emits `.terminal (leafOfState M s) _`);
  ROLLOVER if `widthMinUpto M (s.layer+1) ≤ s.cleared` (ONE child `s.stepRollover`); else let
  `occ = (finRange numDiv).filterMap (fun k => if s.cleared+1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer then some (s.divTilde k) else none)`;
  `occ.min? = some target` and `chooseMin s target = some f` ⟹ `case1Decision` emitting TWO children
  (case11: `Function.update divProfile f (setTail layer cleared (divProfile f))`, keeps numDiv/cleared; and
  case12: `stepAppendAdvance (…) (divProfile f)`, snoc + cleared+1); `occ.min? = none` ⟹ `case2Decision` ONE
  child `stepAppendAdvance (…) (fun p => runMinWidth M p)`; `chooseMin = none` ⟹ terminal fallback (off-cone).
- `ConState` fields: layer, cleared, numDiv, divExp, divProfile : Fin numDiv → (Fin L → ℕ), … ;
  `divTilde k = tildeOf (divProfile k) = min over Fin L`.
- `setTail layer cleared T = fun p => if layer ≤ p then cleared else T p`.
- `leafOfState M s`: analytic side `divProfile i = s.divProfile ((t0Indices s).get i)` where
  `t0Indices s = (finRange numDiv).filter (divTilde · = 0)` (the t̃=0 sublist). `0 < flatDim M` guard.
- Banked invariants (all sorry-free), bundled as `OracleInv M s` (holds at every reachable state via
  `OracleInv_conOracle_stepChildren`, :2158): `WeakDecInv` (profiles weakly decreasing), `FlatTail`
  (coords ≥ layer are constant = divTilde), `WidthBound`, `LiveHeadDom M s` (:886)
  [`∀ a b, divTilde a < divTilde b → divTilde b < widthMinUpto M s.layer → ∀ i < layer, divProfile a i ≤ divProfile b i`],
  `SameLevelChainInv` (same-t̃ divisors pairwise componentwise-comparable), `StateInvariant`
  (layer ≤ L, cleared ≤ layerCap, live_width: cleared ≤ M i for i ≤ layer).
- `step1_dominates` (:909): at a case-1 node, `divTilde x = ℓ`, `divTilde y ≤ J`, `J < ℓ`, `ℓ < widthMinUpto M s.layer`
  ⟹ `∀ i, divProfile y i ≤ divProfile x i`. `chooseMin_spec` (:1827): chosen f is at target level AND
  componentwise ≤ every same-level divisor. `chooserTotalOnChain_of_sameLevel` (:1861).
- `case2Decision` births a divisor with head `runMinWidth M p = widthMinUpto M (p+1)` (the running-min ENVELOPE),
  tail-written to `cleared`; so `divTilde` of the newborn = cleared.

INDEXING PIN: Lean `layer` = paper S − 1 (0-indexed). Profiles `Fin L → ℕ`, index i = paper coord i+1.
`tStar M : Fin L → ℕ` is weakly decreasing, `tStar (L-1) = 0` (admissible last coord), `divTilde (tStar M) = 0`.

THE CERT PROOF I AM TRANSCRIBING (pnp-o5 §4, battery-verified 847 instances):
Track ONE divisor A ("anchor"). Birth: at birth-layer b(a) [= 1 + length of maximal prefix of a equal to the
envelope r], case-2 births A with head = envelope = a's prefix and tail a^b. Maintenance per layer S (b<S≤clear):
start layer S with A having coords 1..S-1 = a's prefix, level a^{S-1}; PLATEAU (a^S=a^{S-1}) A stays; DESCENT
(a^S<a^{S-1}, needs Clearable ⟹ a^{S-1}<r_S) the steered rule 1(1) pulls A down to level a^S at J=a^S. End layer
S: coords 1..S = a's prefix, level a^S. Terminate at layer clear: A reaches t̃=0 with profile = a. R(a) steering:
at a case-1 node with target level ℓ, take case-1(1) iff ℓ > a^S else case-1(2); case-2/rollover forced.

MY ANALYSIS OF THE DIFFICULTY (verify or correct):
- The head condition `∀ i, (i:ℕ) < s.layer → divProfile A i = a i` is preserved TRIVIALLY by case11 (setTail keeps
  coords < layer), case12/case2 (append doesn't touch existing divisors), because none touch coords < layer.
- The ONLY stressing transition is ROLLOVER: layer m→m+1 extends the head range, so it needs `divProfile A m = a m`
  ESTABLISHED — i.e. the anchor's current-layer coord was pulled to a m DURING layer m. The head-only invariant is
  NOT self-maintaining at rollover; the extra fact must come from the intra-layer pull.
- So the invariant must ALSO pin the anchor's current level (coord m). Candidate: at a mid-layer state (layer m,
  cleared J), `a(m) ≤ divTilde A ≤ a(m-1)`, AND at a rollover-eligible state (J ≥ widthMinUpto(m+1)) `divTilde A = a(m)`.
  But the latter is not implied by the former; it needs the pull to have happened.
- Existence fails at conRoot (numDiv = 0). So the invariant must be guarded, e.g. `0 < s.layer → ∃ A, …`, vacuous at
  the root; the birth is a case-2 maintenance step that establishes A.
</task>

<output_contract>
Terse, structural, GROUNDED in the files (name lemmas exactly, v4.29). Do NOT write the full proof.
1. THE INVARIANT: give the exact Lean `Prop` (a predicate on `ConState L`, `M`, and the target `a`) that
   (i) holds at `conRoot`, (ii) is maintained by the R(a)-steered child at EVERY step (rollover/case1/case2), and
   (iii) at a terminal state (layer = L) yields `∃ A, divProfile A = a ∧ divTilde A = 0`. Resolve the root-existence
   and birth-layer issues. If a single fused invariant cannot carry the rollover obligation, say so and give the
   split (e.g. an explicit per-layer sub-induction on `cleared`, or a separate "level = a(layer)" lemma proven by
   a J-induction) — which is cleaner in Lean?
2. THE INDUCTION: is WF-induction on `conRel M` (like leaves_isFullMono) the right top frame, or is a different
   recursion (fuel on layers; a nested cleared-induction inside the layer) cleaner? How is the R(a)-steered child
   selected from `(conOracle M s).stepChildren` and shown to be one of the emitted children (the case11-vs-case12
   dispatch)?
3. THE PULL-ORDERING BRICK (descent case): to get `divProfile A m = a m` at J=a(m), do I need A to BE the chosen
   `f = chooseMin s target`, or does f-becomes-the-new-anchor also work? Is "the anchor is Def-4-least at its level
   (head = a's prefix ≤ all competitors)" provable from LiveHeadDom + SameLevelChainInv + chooseMin_spec, or does it
   genuinely need tStar's Mval-minimality? Which banked lemma is the core (step1_dominates? chooseMin_spec?)?
4. THE SINGLE BIGGEST RISK / where this design dead-ends, ranked by likelihood. In particular: does the steered
   trajectory (which case fires at each J, occ_above emptiness, birth timing) need to be TRACKED in the invariant,
   or does reacting to whatever conOracle emits suffice? If the former, is the proof feasible at all in the fused
   frame, or should I recommend a scoped sub-lemma decomposition to my controller?
</output_contract>

<grounding_rules>
Read buildTree, conOracle, case1Decision/case2Decision, stepCase11/stepAppendAdvance, leaves_isFullMono,
step1_dominates, LiveHeadDom, chooseMin_spec, leafOfState, t0Indices, the cert at
expeditions/2026-07-17-aoyagi-engine/threads/12-realization/cert-o5-realization.md §4-5. Ground each structural
claim. Flag inference vs verified-from-file. DESIGN review: skeleton + load-bearing obligations + risks, not the proof.
</grounding_rules>
