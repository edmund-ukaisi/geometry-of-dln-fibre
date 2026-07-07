<task>
I am formalising in Lean 4 + Mathlib a "Step Ψ_conj" (LINK-1) piece of a two-step RLCT bridge for
deep-linear-network loss geometry. I need a decorrelated strategic read on the RIGHT construction and
the highest-value bankable path for ONE formalisation tide. This is pure architecture advice — I do
not need Lean code, I need the diagnosis.

## The two-step bridge (context)
The goal is to close a lemma `hstep2` of the shape (all at a basepoint `wstar = flat-encode of the
deepest point; split wstar = 0`):

    rlctAtOn Φscore wstar = rlctAtOn Φcore_bare wstar

where (with `split : flat ≃ₜ DeepestSplit` the measure-preserving chart, `regStraighten` a fixed reg
straightener, `Score` a fixed scalar function, `coreF` = squared-Frobenius of the reduced network
product):
  Φscore x       = ∑_i (regStraighten (split x)).1 i ^2  +  Score x
  Φcore_bare x   = ∑_i (regStraighten (split x)).1 i ^2  +  coreF( deepestCoreAbsorb (split x) ).2.1

`hstep2 = Step Θ ∘ Step Ψ_conj`:
- **Step Θ** (LANDED, unconditional, general L): `rlctAtOn Φcore_conj wstar = rlctAtOn Φcore_bare wstar`
  where `Φcore_conj x = ∑ reg² + coreF( deepestCoreAbsorbConj (split x) ).2.1`. (`deepestCoreAbsorbConj`
  is the "honest" conjugate core-absorb: an additive core-shear whose shift's derivative at 0 is NONZERO.)
- **Step Ψ_conj** (what I must build): `rlctAtOn Φscore wstar = rlctAtOn Φcore_conj wstar`.

## How Step Ψ_conj works at L=2 (the template I must generalise)
It uses `rlctAtOn_diffeo_bridge_of`: exhibit a flat diffeo `psi : flat → flat`, ContDiff, with strict
Fréchet derivative = identity at `wstar`, fixing `wstar`, such that
   `Φcore_conj ∘ psi  =ᶠ[𝓝 wstar]  Φscore`.
The composition identity is proved from TWO germs (local `=ᶠ` facts), where `psiSplitRaw := split ∘ psi ∘ split⁻¹`
is the "split-side" action of `psi`:
  - **hsub3reg** (reg preservation): `∑ deepestEFull(psiSplitRaw(split x))² = ∑ deepestEFull(split x)²`.
    (`regStraighten.1 = deepestEFull`, and `deepestEFull` READS the core slot at the last layer.)
  - **hsub4core** (core = Score): `coreF( deepestCoreAbsorbConj (psiSplitRaw (split x)) ).2.1 = Score x`.

At L=2, `psiSplitRaw = psiSplitRawL2CoreConj` is a JOINT move: it edits BOTH the core slot at the last
layer (`T1 ↦ T1'`) AND the reg/gauge slot (last-layer Y-tag `Y1 ↦ Y1'`). The Y-edit is chosen so
`deepestEFull` is EXACTLY preserved (that's why hsub3reg holds), while the core-edit realises the Schur
"untwisting" so hsub4core = Score.

## Key banked facts (general L)
1. `deepestCoreF_coreAbsorbConj_eq_prodSchur`: on a small ball,
   `coreF( deepestCoreAbsorbConj q ).2.1 = ‖ prod_s ( decode(q.2.1)_s + Δ_s(q.1, q.2.2) ) ‖²`
   where `Δ = schurCorrectionConj` (per-layer Schur correction read from the reg/spectator coords).
2. `deepestPsiCoreShear K`: a per-layer LEFT core shear `S_s ↦ (1 - K_s q)·S_s`, fixes reg & spec slots;
   its `isLocalDiffeoAt 0` triple (ContDiff, strict-fderiv = id at 0, fixes 0) is banked given
   `hKcd`(K ContDiff) + `hK0`(K 0 = 0).
3. `schur_product_ldu_rec`, `Kcoup_zero`, `blockSchur_partProd_succ`: the abstract chain machinery. The
   HONEST CHAIN identity `blockSchur(partProd Ĉ L) = ScoreSchur` (Ĉ_s = reindex(decode layer s), pivot
   `deepBlkA_s + gaugeReadX_s`) is NUMERICALLY CERTIFIED but NOT yet in Lean (needs Fin-L↔ℕ cast
   resolution + a frame-strip/corner step to the framed `Score`).
4. A general conjugation flat diffeo `deepestGConjFlat K = split⁻¹ ∘ coreAbsorb_bareNaive⁻¹ ∘ (deepestPsiCoreShear K)
   ∘ coreAbsorb_bareNaive ∘ split` is banked (ContDiff/fderiv-id/fixpoint), but it uses the NAIVE
   core-absorb, and its germ target is the NAIVE core — a prior finding proved that naive germ UNSATISFIABLE.

## My two candidate architectures for the general Ψ_conj
(A) **Pure core conjugation**: `psi = split⁻¹ ∘ coreAbsorbConj⁻¹ ∘ (deepestPsiCoreShear K) ∘ coreAbsorbConj ∘ split`.
    - fderiv-id at wstar: the conjugation cancels — `D(coreAbsorbConj⁻¹)(0) ∘ id ∘ D(coreAbsorbConj)(0) = id`
      (the two are mutually inverse CLEs — `coreShearSymmCLM Dδ ∘ coreShearCLM Dδ = id`), so the nonzero
      shift-derivative does NOT obstruct fderiv-id. Clean.
    - BUT this only touches the CORE slot (both factors fix reg/spec). Then `deepestEFull(psiSplitRaw(split x))`
      differs from `deepestEFull(split x)` because deepestEFull reads the core → **hsub3reg (reg preservation)
      appears to FAIL** (no compensating Y-edit). This is my worry.
(B) **Joint move** (mirror L=2): psi edits core + reg/gauge jointly to preserve deepestEFull exactly, and
    hits Score via the honest chain. This is the real coupled bulk; comparable in size to the entire L=2
    file (~2700 lines) + honest-chain-in-Lean (not yet built).

## Questions (rank + answer each briefly)
Q1. Is my worry about (A) correct — that a pure core-slot conjugation cannot satisfy hsub3reg
    (reg preservation), because deepestEFull reads the core and there is no compensating reg/gauge edit?
    Or is there a reason hsub3reg could still hold (e.g. deepestEFull is core-independent on the relevant
    germ, or the value-fold `∂deepestEFull/∂core(0)=0` upgrades to exact local invariance)?
Q2. If (A) fails, is the joint move (B) genuinely unavoidable, or is there a cleaner general construction
    (e.g. absorb the reg-preservation into `regStraighten` or into a second conjugation, so the DIFFEO is
    a composition of two shears whose reg-edit is forced by an explicit formula, avoiding the L=2 ad-hoc
    `Y1'`)? I want the general Ψ_conj to be a principled construction, not a re-derivation of L=2 algebra.
Q3. For ONE tide, is the highest-value HONEST-PARTIAL bank to build an ABSTRACT reduction
    `deepest_diffeo_bridge_gen_conj_impl` + `..._assembled` that take `psi`, `psiSplitRaw`, the diffeo
    triple, the split-relation `split∘psi = psiSplitRaw∘split`, and the two germs ALL as hypotheses, and
    produce the hstep2 conclusion (composing with the landed Step Θ) — thereby reducing hstep2 to
    [construct psi/psiSplitRaw] + [the two germs], leaving hstep2 itself as a sorry with a precise
    remaining-step report? Is that a faithful reduction or does it risk "laundering" (hiding the hard part
    in hypotheses)? Note: the analogous NAIVE abstract reduction is already banked and accepted.
Q4. Any cheaper discriminating test I should run before committing to (A) vs (B)?
</task>

<output_contract>
Answer Q1–Q4 in order. For Q1 give a definite yes/no with the one-line reason. For Q2 name the single
best construction. For Q3 give a verdict (faithful reduction / laundering risk) + one sentence why. Keep
under ~450 words. Flag explicitly where you are inferring vs. stating a fact you can support.
</output_contract>

<grounding_rules>
You do not have the repo. Reason from the mathematical structure I described. Where your answer depends
on an assumption about the Lean definitions (e.g. exactly what `deepestEFull` reads, or whether the
Schur correction Δ depends on the core), state the assumption explicitly and say the answer is
conditional on it.
</grounding_rules>
