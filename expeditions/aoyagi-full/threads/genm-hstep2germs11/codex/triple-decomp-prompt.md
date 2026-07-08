<task>
I am formalising in Lean 4 (Mathlib v4.29) the final analytic step ("hstep2") of a deep-linear-network
RLCT computation. I need a decorrelated feasibility + decomposition read before I sink hundreds of lines
into an infrastructure build, because thrashing risk is high.

## The compose target (all banked, sorry-free)

There is a banked reduction `deepest_diffeo_bridge_gen_assembled` whose conclusion is EXACTLY the `hstep2`
goal. It takes as HYPOTHESES:
  * frame data Pf, Qf and block facts (hDA, hbdy, hPtri, hQtri, hQf22, ...) — all reachable/mechanical.
  * an abstract flat local diffeo `psi : (Fin n → ℝ) → (Fin n → ℝ)` at `wstar` with a diffeo TRIPLE:
      - `hcontdiff : ContDiff ℝ ⊤ psi`
      - `hderiv : HasStrictFDerivAt psi (id) wstar`
      - `hfix : psi wstar = wstar`
      - `hsplitPsi : ∀ᶠ x near wstar, split (psi x) = psiSplitRaw (split x)`
  * two germs at wstar: `hsub3reg` (reg-energy preserved) and `hsub4core` (core untwists to Score).

There is ALSO a banked "cutoff→flat-diffeo plumbing" `DeepestPsiFlatCutGen`: given ANY raw split-side move
`psiSplitRaw : DeepestSplit → DeepestSplit` with
  (a) `hraw0 : psiSplitRaw 0 = 0`,
  (b) `hcd : ∀ q ∈ tsupport χ, ContDiffAt ℝ ⊤ (fun q => psiSplitRaw q − q) q`  (χ a ContDiffBump at 0),
  (c) `hderiv0 : HasStrictFDerivAt (fun q => psiSplitRaw q − q) 0 0`,
it constructs `psi = split⁻¹ ∘ (q + χ·(psiSplitRaw q − q)) ∘ split` and discharges the whole triple
(`hcontdiff`/`hderiv`/`hfix`/`hsplitPsi`). So the triple reduces to supplying (a)(b)(c) for the concrete
general-L move `psiSplitRawGen`.

## The concrete move `psiSplitRawGen`

`psiSplitRawGen q` packs, per layer s (0..L-1), the four blocks of `psiReadBlk q s` into the gauge slot
(via a fixed linear equiv `regGaugeSlotEquiv.symm`) and core slot (via `paramsEquivFlat`). Each
`psiReadBlk q s` is a fixed reindex of `psiGhat q s`, where:
  * interior s:   `psiGhat q s = psiTargetD q s`,
  * first layer:  `psiGhat q s = forcedDecodeLeft  (frame P0) (psiTargetD q s)`,
  * last layer:   `psiGhat q s = forcedDecodeRight (frame Ql) (psiTargetD q s)`,
with `psiTargetD q s = movedC (deepestChain (framedParamsPivot … q)) (Z0edit0 …) s − corM`.
`forcedDecodeLeft/Right` involve `Ring.inverse (frame.toBlocks₁₁)`.
`movedC` is built from the base chain `C = deepestChain (framedParamsPivot q)` via blockSchur, schurTilde,
`nMix = I + uV`, `uNorm = B⁻¹R`, `vDown = ZA⁻¹`, `upEdit = N⁻¹u(S−S̃)`, `movedT = S̃ + Z'A⁻¹Y'` — i.e. it
involves matrix inverses A⁻¹, N⁻¹, B⁻¹ (=partProd₁₁⁻¹) at EACH layer.

## What already exists (building blocks)

  * `contDiff_framedParamsPivot_entry` : each entry of `framedParamsPivot … q s` is `ContDiff ℝ ⊤` in q.
  * `deepestChain … A s` is a fixed reindex of `A ⟨s,_⟩`, so its entries are ContDiff in q (via above).
  * Generic bricks: `contDiffAt_matrix_inv_entry_of_det_ne_zero_at`, `contDiffAt_matrix_mul_entry`,
    `contDiff_matrix_det_of_entries`, `contDiff_matrix_adjugate_entry_of_entries`,
    `hasStrictFDerivAt_triple_mul_zero` (degree-2 vanishing of a triple product at 0),
    `hasStrictFDerivAt_matrix_mul_entry_of_{left,right}_zero`.
  * At q=0 the base chain C = the block-normal corner diag(I_r,0): Y=Z=0, S=S̃=0, N=A=I, all edits vanish,
    so `psiSplitRawGen 0 = 0` conceptually.
  * The L=2 SPECIAL CASE is fully done (~2700 lines, `DeepestDiffeoBridgeL2Conj`): it builds an explicit
    2-layer lens (l2A0,l2A1,l2Y0,l2Z1,l2Y1,l2T1,l2P00,l2K,l2R,l2W,l2T1p) and proves, per block: value at 0,
    ContDiff/ContDiffAt-on-unit-locus of each entry, and HasStrictFDerivAt-at-0 of each entry, then packs.

## The three remaining producers I must build (general L ≥ 3)

  1. TRIPLE inputs (a)(b)(c) for `psiSplitRawGen`. (b) needs ContDiffAt through the depth-L chain of matrix
     inverses on a unit-locus bump support; (c) needs D(psiSplitRawGen − id)(0) = 0 (degree-2 vanishing;
     numerically cert-confirmed the deviation is O(‖q‖³)).
  2. `hsub3reg` germ: `∀ᶠ x near wstar, ∑ deepestEFull(psiSplitRawGen(split x))² = ∑ deepestEFull(split x)²`.
     There is a banked pure-algebra lemma `deepestEFull_sq_sum_eq_of_chain_movedC` that gives this for a
     single (q₁,q₂)=(psiSplitRawGen(split x), split x) GIVEN the move identity `hmove` (banked, holds ∀q)
     and IsUnit hyps `hP/hA/hN` on the base chain at q₂ (partProd₁₁, layer A₁₁, nMix). So this reduces to:
     the IsUnit germs hold `∀ᶠ x` (value=units at 0 + continuity-in-q + IsUnit openness).
  3. `hsub4core` telescope germ: `∏_s blockSchur(movedC decode)_s = Score`, via banked
     `prodSchurCore_eq_blockSchur_partProd` + banked boundary Schur-invisibility + endpoint/−B normalization.

## What I want from you

I have ~one focused formalisation thread. The full thing looks comparable in size to the L=2 machinery
(multi-hundred lines, likely > 1000). I must bank+push reachable pieces incrementally and STOP+report if a
piece reveals a genuine analytic obstruction beyond "mirror L=2 + the O(‖q‖³) cert".
</task>

<output_contract>
Be concise and concrete. Answer in exactly these sections:

1. FEASIBILITY VERDICT (one line each): for producer 1 (triple a/b/c), 2 (hsub3reg germ),
   3 (hsub4core telescope) — is it reachable by "mirror L=2 + generic bricks", or does it hide a genuine
   new difficulty? Flag any that is a multi-thread wall vs a bounded (<~250 L) build.

2. RECOMMENDED ORDER: which producer to attempt first for maximal *banked* value, given I may not finish
   all three. Justify in <=2 sentences.

3. TRIPLE (producer 1), the crux: For (b) ContDiffAt on the bump support — is the right move to (i) prove
   ContDiffAt of `psiSplitRawGen − id` at EVERY q in an open unit-locus and then choose χ with tsupport
   inside it, or (ii) something else? How is the χ / tsupport dependency on the unit-locus discharged
   cleanly in Lean (the chicken-and-egg: χ must be fixed before hcd, but hcd needs tsupport ⊆ unit-locus)?
   For (c) the degree-2 vanishing — is per-layer-block HasStrictFDerivAt-at-0 = 0 then packing (mirroring
   L=2) the only viable route, or is there a cheaper argument that D(reads)(0) matches D(identity)(0)
   directly? Name the single biggest pitfall.

4. IsUnit GERMS (producer 2): cheapest Lean route to `∀ᶠ q near 0, IsUnit (M q)` where M q is a
   chain-derived matrix that is ContinuousAt and M 0 = I (or a unit). Name the exact Mathlib lemmas
   (v4.29) for "IsUnit is open for matrices over ℝ" / det-continuity / eventually-ne.

5. Any RED FLAG in my plan — e.g. a place where the general-L object is NOT a faithful analog of the L=2
   one, or where `psiSplitRawGen 0 = 0` / the derivative-0 claim could actually be FALSE.
</output_contract>

<grounding_rules>
Distinguish clearly: (i) claims you are confident of from the structure I gave, vs (ii) inferences/guesses
about Mathlib lemma names or the exact Lean tactic. Flag (ii) explicitly as "verify". Do not invent lemma
names with false confidence — if unsure of a v4.29 name, say so and describe the lemma's type instead.
</grounding_rules>
